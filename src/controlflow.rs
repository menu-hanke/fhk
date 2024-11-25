//! Control flow analysis;

use crate::bitmap::{BitMatrix, BitmapVec, Bitmap};
use crate::dataflow::{Dataflow, DataflowSystem};
use crate::index;
use crate::ir::{Code, InsId, Opcode};

// the entry (i,j) tells you:
//
//   IF control flow goes through node i, does it necessarily ALSO go through node j?
//
// this sounds a lot like a dominance tree, but it's not the same thing at all.
// it's also not a postdominance tree. it's also not a union of the two.
// the reason this needs to exist is because CSE across "basic blocks" (which the ir doesn't
// have anyway, but imagine for a second it did) causes wonky "control flows".
// example:
//                 3. IF
//                /     \
//             4. IF  5. use 1
//            /  \    6. use 2
//      7. use 1  6. use 1
//      8. use 2
//
// here:
//   * execution of 3 implies execution of 1
//   * execution 1 implies execution of 3, IF these are all the uses of 1. if there's other uses
//     of 1 not shown in the picture, then 1 does not imply 3.
//   * 3 does not imply 2, but 2 may or may not imply 3, again depending on its other uses.
//
// note that this has nothing to do with the order of computations, only whether control flow
// must pass through the instruction or not.
//
// it is the solution to the following system:
//
//   C(i,i) = 1   for all i
//   C(i,j) = 1   where i ≠ j, if (at least) one of the following is true:
//                * (1) C(k,j) = 1 for all k ∈ uses(i)
//                * (2) op(i) ≠ IF, and C(k,j) = 1 for some k ∈ inputs(i)
//                * (3) op(i) ≠ IF, and C(cond(i),j) = 1, or C(tru(i),j) = C(fal(i),j) = 1
//   C(i,j) = 0   otherwise,
//
// or in a more dataflow-y form:
//
//   C(i) = {i} ∪  (∩  C(j) : j ∈ uses(i)) ∪  (∪  C(j) : j ∈ inputs(i))               IF op(i) ≠ IF
//   C(i) = {i} ∪  (∩  C(j) : j ∈ uses(i)) ∪  C(cond(i)) ∪  (C(tru(i)) ∩  C(fal(i)))  IF op(i) = IF
//
// note that data and control are treated uniformly here: inputs(i) contains data inputs and
// successors, while uses(i) contains data uses and precedessors.
pub type ControlMatrix = BitMatrix<InsId>;

pub fn compute_dataflow(dfg: &mut Dataflow<InsId>, code: &Code) {
    dfg.clear();
    for (_, ins) in code.pairs() {
        dfg.push();
        dfg.raw_inputs().extend_from_slice(ins.inputs_and_controls());
    }
    dfg.compute_uses();
}

// set r(i) = r(i) ∪  (∩ r(j) : js)
fn addintersect(mat: &mut BitMatrix<InsId>, i: InsId, js: &[InsId], work: &mut Bitmap<InsId>) {
    match js.len() {
        0 => {},
        1 => {
            let [ri, rj] = mat.get_rows_mut([i, js[0]]);
            ri.union(rj);
        },
        _ => {
            work.copy_from(&mat[js[0]]);
            for &j in &js[1..] {
                work.intersect(&mat[j]);
            }
            mat[i].union(work);
        }
    }
}

pub fn compute_controlflow(
    code: &Code,
    dfg: &Dataflow<InsId>,
    solver: &mut DataflowSystem<InsId>,
    mat: &mut ControlMatrix,
    work: &mut BitmapVec
) {
    let end = dfg.end();
    mat.resize(end, end);
    mat.clear_all();
    for i in index::iter_span(end) {
        mat[i].set(i);
    }
    work.resize(end.into());
    let work: &mut Bitmap<InsId> = work.cast_mut();
    solver.resize(end);
    solver.queue_all(end);
    while let Some(i) = solver.poll() {
        let pop = mat[i].popcount();
        let inputs = dfg.inputs(i);
        let uses = dfg.uses(i);
        addintersect(mat, i, uses, work);
        match code.at(i).opcode() {
            Opcode::IF => {
                let [ri, rcond] = mat.get_rows_mut([i, inputs[0]]);
                ri.union(rcond);
                addintersect(mat, i, &inputs[1..], work);
            },
            _ => for &j in inputs {
                let [ri, rj] = mat.get_rows_mut([i, j]);
                ri.union(rj);
            }
        }
        if mat[i].popcount() != pop {
            solver.queue_nodes(inputs);
            solver.queue_nodes(uses);
        }
    }
}
