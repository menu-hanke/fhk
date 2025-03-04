//! Eliminate "model switch" IFs.

use crate::compile::Ccx;
use crate::index::{IndexOption, IndexSet, IndexSlice};
use crate::ir::{ins_matches, FuncId, Ins, InsId, Opcode, PhiId};
use crate::optimize::{FuncPass, Ocx};
use crate::typestate::Absent;

// a "model switch" is an IF that looks like this:
//
//    JMP v=v0      JMP v=v1   ...   JMP v=vN
//       |              |               |
//       |              v               |
//       +-------->  IF v=v0 <----------+
//                    |   |
//                    |   +-----------> ...
//                   IF v=v1
//                    |   |
//                    |   +-----------> ...
//                   ...
//                    |
//                   IF v=vK ---------> ...
//                    |
//                    v
//                   ...
// inlining model/availability chunks tends to produce this kind of control flow.
// this pass eliminates the IFs and patches each precedessor JMP to a GOTO.
// (in the future this should probably be replaced with a more general sparse conditional
//  constant propagation pass, but this will have to do for now.)

#[derive(Default)]
pub struct OptSwitch;

#[derive(zerocopy::FromBytes, zerocopy::IntoBytes, zerocopy::Immutable)]
struct CtrState {
    phi: IndexOption<PhiId>,
}

const SWITCH_UNVISITED: InsId = zerocopy::transmute!(!0u16);
const SWITCH_NONE: InsId = zerocopy::transmute!(!1u16);

#[derive(Clone, zerocopy::FromBytes, zerocopy::IntoBytes, zerocopy::Immutable)]
struct PhiState {
    switch: InsId
}

fn visit_candidate(
    code: &IndexSlice<InsId, Ins>,
    ctr_state: &mut IndexSlice<InsId, CtrState>,
    phi_state: &mut IndexSlice<PhiId, PhiState>,
    visited: &mut IndexSet<InsId>,
    id: InsId
) {
    if visited.test_and_set(id) {
        return
    }
    let ins = code[id];
    let phi = if ins_matches!(code, ins; IF ((EQ|NE) (PHI) const)) {
        // potential link
        let phi = code[code[ins.decode_V()].decode_V()].decode_PHI().1;
        if phi_state[phi].switch == SWITCH_UNVISITED {
            // the first IF we visit must be the head, because the head dominates all other
            // IFs in the chain
            phi_state[phi].switch = id;
        }
        Some(phi)
    } else if ins_matches!(code, ins; JMP const) {
        Some(ins.decode_JMP().2)
    } else {
        None
    }.into();
    ctr_state[id].phi = phi;
    for &c in ins.controls() {
        visit_candidate(code, ctr_state, phi_state, visited, c);
        let good = ctr_state[c].phi == phi
            && code[c].opcode() == Opcode::IF
            && (ins.opcode() == Opcode::IF
                || (ins.opcode() == Opcode::JMP && phi.is_some() && phi_state[phi.raw].switch == c));
        if !good {
            if phi.is_some() && ins.opcode() == Opcode::JMP {
                phi_state[phi.raw].switch = SWITCH_NONE;
            }
            if ctr_state[c].phi.is_some() && code[c].opcode() == Opcode::IF {
                phi_state[ctr_state[c].phi.raw].switch = SWITCH_NONE;
            }
        }
    }
}

fn visit_full_data(
    code: &IndexSlice<InsId, Ins>,
    ctr_state: &mut IndexSlice<InsId, CtrState>,
    phi_state: &mut IndexSlice<PhiId, PhiState>,
    visited: &mut IndexSet<InsId>,
    id: InsId
) {
    let ins = code[id];
    if ins.opcode().is_pinned() {
        let ctr = ins.decode_C();
        if let Some(phi) = ctr_state[ctr].phi.unpack() {
            phi_state[phi].switch = SWITCH_NONE;
        }
    }
    for &v in ins.inputs() {
        if !visited.test_and_set(v) {
            visit_full_data(code, ctr_state, phi_state, visited, v);
        }
    }
}

fn visit_full(
    code: &IndexSlice<InsId, Ins>,
    ctr_state: &mut IndexSlice<InsId, CtrState>,
    phi_state: &mut IndexSlice<PhiId, PhiState>,
    visited: &mut IndexSet<InsId>,
    id: InsId
) {
    if visited.test_and_set(id) {
        return
    }
    if ctr_state[id].phi.is_none() {
        visit_full_data(code, ctr_state, phi_state, visited, id);
    }
    for &c in code[id].controls() {
        visit_full_data(code, ctr_state, phi_state, visited, c);
    }
}

fn visit_patch(
    code: &mut IndexSlice<InsId, Ins>,
    ctr_state: &IndexSlice<InsId, CtrState>,
    phi_state: &IndexSlice<PhiId, PhiState>,
    visited: &mut IndexSet<InsId>,
    id: InsId
) {
    if visited.test_and_set(id) {
        return
    }
    let ins = code[id];
    if let Some(phi) = ctr_state[id].phi.unpack() {
        if ins.opcode() == Opcode::JMP && phi_state[phi].switch != SWITCH_NONE {
            let mut ctr = ins.decode_C();
            debug_assert!(phi_state[phi].switch == ctr);
            debug_assert!(code[ins.decode_V()].opcode().is_const());
            let kjmp = code[ins.decode_V()];
            while ctr_state[ctr].phi == Some(phi).into() {
                let (cond, tru, fal) = code[ctr].decode_IF();
                debug_assert!(ins_matches!(code, code[ctr]; IF ((EQ|NE) (PHI) const)));
                debug_assert!(code[code[cond].decode_V()].decode_PHI().1 == ctr_state[ctr].phi.unwrap());
                let opcode = code[cond].opcode();
                let kswitch = code[code[cond].decode_VV().1];
                // note: this assumes two constants are equal iff the instructions are equal.
                // this works as long as the KINT/KINT64/KFP64 logic is consistent everywhere,
                // and no one modifies the (unused) a field.
                // also, this logic only works for integers. this can be done with floats as well
                // because we are just comparing constants, but the main purpose of this pass
                // is to cleanup the arm/avail chunks emitted by the frontend after inlining.
                debug_assert!(kjmp.a() == 0 && kswitch.a() == 0);
                debug_assert!(kjmp.type_().is_int() && kjmp.type_() == kswitch.type_());
                ctr = if (kjmp == kswitch) == (opcode == Opcode::EQ) { tru } else { fal };
            }
            code[id] = Ins::GOTO(ctr);
        }
        // else: we don't need to do anything about the switch chain IFs: they become dead code
        // after all JMPs have been patched.
    }
    for &c in ins.controls() {
        visit_patch(code, ctr_state, phi_state, visited, c);
    }
}

impl FuncPass for OptSwitch {

    fn new(_: &mut Ccx<Absent>) -> Self {
        Default::default()
    }

    fn run(ccx: &mut Ocx, fid: FuncId) {
        let base = ccx.tmp.end();
        let func = &mut ccx.ir.funcs[fid];
        let code = func.code.inner_mut();
        let (ctr_ptr, _) = ccx.tmp.reserve_dst::<IndexSlice<InsId, CtrState>>(code.raw.len());
        let (phi_ptr, _) = ccx.tmp.reserve_dst::<IndexSlice<PhiId, PhiState>>(func.phis.end().into());
        let mut data = ccx.tmp.get_many_mut::<2>();
        let ctr_state = data.get_dst_mut(ctr_ptr, code.raw.len());
        let phi_state = data.get_dst_mut(phi_ptr, func.phis.end().into());
        phi_state.raw.fill(PhiState { switch: SWITCH_UNVISITED });
        ccx.mark1.clear();
        visit_candidate(code, ctr_state, phi_state, &mut ccx.mark1, func.entry);
        if phi_state.raw.iter().any(|s| s.switch < SWITCH_NONE) {
            ccx.mark1.clear();
            visit_full(code, ctr_state, phi_state, &mut ccx.mark1, func.entry);
            ccx.mark1.clear();
            visit_patch(code, ctr_state, phi_state, &mut ccx.mark1, func.entry);
        }
        ccx.tmp.truncate(base);
    }

}
