//! Loop optimizations.

use crate::bitmap::BitmapWord;
use crate::compile::Ccx;
use crate::index::{self, index, IndexSet, IndexSlice};
use crate::ir::{FuncId, Ins, InsId, Opcode, PhiId};
use crate::optimize::{FuncPass, Ocx};
use crate::typestate::Absent;

const MAX_LOOP: usize = BitmapWord::BITS;

index!(struct LoopId(u16));

#[derive(Default)]
pub struct OptLoop;

#[derive(zerocopy::FromBytes, zerocopy::IntoBytes, zerocopy::Immutable)]
struct InnerLoop {
    body: InsId,
    tail: InsId
}

fn isloopbody(code: &IndexSlice<InsId, Ins>, mut id: InsId, tail: InsId) -> bool {
    loop {
        if id == tail {
            return true
        }
        let ins = code[id];
        if !(Opcode::JMP|Opcode::GOTO).contains(ins.opcode()) {
            return false
        }
        id = ins.decode_C();
    }
}

fn scanloops(
    code: &IndexSlice<InsId, Ins>,
    visited: &mut IndexSet<InsId>,
    loops: &mut [InnerLoop; MAX_LOOP],
    mut nloop: usize,
    id: InsId
) -> usize {
    if visited.test_and_set(id) {
        return nloop;
    }
    let ins = code[id];
    if ins.opcode() == Opcode::IF {
        for &branch in ins.controls() {
            if isloopbody(code, branch, id) {
                loops[nloop] = InnerLoop { body: branch, tail: id };
                visited.insert(id); // don't bother checking again
                nloop += 1;
                break;
            }
        }
    }
    for &c in ins.controls() {
        if nloop >= MAX_LOOP { break }
        nloop = scanloops(code, visited, loops, nloop, c);
    }
    nloop
}

fn collecteffects(
    code: &IndexSlice<InsId, Ins>,
    loops: &IndexSlice<LoopId, InnerLoop>,
    visited: &mut IndexSet<InsId>,
    loopdep: &mut IndexSlice<InsId, BitmapWord<LoopId>>,
    phidep: &mut IndexSlice<PhiId, BitmapWord<LoopId>>,
) {
    phidep.raw.fill(Default::default());
    for (lid, &InnerLoop { mut body, tail }) in loops.pairs() {
        loop {
            let mut w: BitmapWord<LoopId> = Default::default();
            w.set(lid);
            loopdep[body] = w;
            visited.insert(body);
            //crate::trace::trace!("loop {:?} {:?}", body, w);
            if body == tail { break }
            let ins = code[body];
            if ins.opcode() == Opcode::JMP {
                let (_, _, phi) = ins.decode_JMP();
                phidep[phi].union(&w);
            }
            body = ins.decode_C();
        }
    }
}

fn visit(
    code: &IndexSlice<InsId, Ins>,
    visited: &mut IndexSet<InsId>,
    loopdep: &mut IndexSlice<InsId, BitmapWord<LoopId>>,
    phidep: &IndexSlice<PhiId, BitmapWord<LoopId>>,
    id: InsId
) -> BitmapWord<LoopId> {
    if visited.test_and_set(id) {
        return loopdep[id];
    }
    let mut w = visitinputs(code, visited, loopdep, phidep, id);
    let ins = code[id];
    let opcode = ins.opcode();
    if opcode.is_pinned() {
        let c = ins.decode_C();
        if visited.contains(c) {
            w.union(&loopdep[c]);
        }
        if opcode == Opcode::PHI {
            let (_, phi) = ins.decode_PHI();
            w.union(&phidep[phi]);
        }
        //crate::trace::trace!("pinned {:?} w={:?} c={:?} visited={:?}", id, w, c, visited.contains(c));
    }
    loopdep[id] = w;
    w
}

fn visitinputs(
    code: &IndexSlice<InsId, Ins>,
    visited: &mut IndexSet<InsId>,
    loopdep: &mut IndexSlice<InsId, BitmapWord<LoopId>>,
    phidep: &IndexSlice<PhiId, BitmapWord<LoopId>>,
    id: InsId
) -> BitmapWord<LoopId> {
    let mut w: BitmapWord<LoopId> = Default::default();
    for &input in code[id].inputs() {
        w.union(&visit(code, visited, loopdep, phidep, input));
    }
    w
}

impl FuncPass for OptLoop {

    fn new(_: &mut Ccx<Absent>) -> Self {
        Default::default()
    }

    fn run(ccx: &mut Ocx, fid: FuncId) {
        let base = ccx.tmp.end();
        ccx.mark1.clear();
        let func = &mut ccx.ir.funcs[fid];
        let code = func.code.inner_mut();
        let (loops_ptr, loops) = ccx.tmp.reserve();
        let nloop = scanloops(code, &mut ccx.mark1, loops, 0, func.entry);
        if nloop > 0 {
            //crate::trace::trace!("fid={:?} loops={}", fid, nloop);
            let (loopdep_ptr, _) = ccx.tmp.reserve_dst::<IndexSlice<InsId, BitmapWord<LoopId>>>
                (code.raw.len());
            let (phidep_ptr, _) = ccx.tmp.reserve_dst::<IndexSlice<PhiId, BitmapWord<LoopId>>>
                (func.phis.end().into());
            let mut data = ccx.tmp.get_many_mut::<3>();
            let loops = IndexSlice::from_raw(&data.get_mut(loops_ptr)[..nloop]);
            let loopdep = data.get_dst_mut(loopdep_ptr, code.raw.len());
            let phidep = data.get_dst_mut(phidep_ptr, func.phis.end().into());
            ccx.mark1.clear();
            collecteffects(code, loops, &mut ccx.mark1, loopdep, phidep);
            let mut keep: BitmapWord<LoopId> = Default::default();
            for id in index::iter_span(code.end()) {
                if code[id].opcode().is_control() {
                    let mut w = visitinputs(code, &mut ccx.mark1, loopdep, phidep, id);
                    if ccx.mark1.contains(id) {
                        w.difference(&loopdep[id]);
                    }
                    keep.union(&w);
                }
            }
            //crate::trace::trace!("keep = {:?}", keep);
            for (lid, &InnerLoop { body, tail }) in loops.pairs() {
                if !keep.test(lid) {
                    let (_, tru, fal) = code[tail].decode_IF();
                    code[tail] = Ins::GOTO(if body == tru { fal } else { tru });
                }
            }
        }
        ccx.tmp.truncate(base);
    }

}
