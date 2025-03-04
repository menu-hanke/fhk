//! GOTO elimination.

use crate::bump::{Bump, BumpPtr, BumpRef};
use crate::compile::Ccx;
use crate::index::IndexSlice;
use crate::ir::{FuncId, Ins, InsId, Opcode};
use crate::optimize::{FuncPass, Ocx};
use crate::typestate::Absent;

#[derive(Default)]
pub struct OptGoto;

type ControlInfo = u8;
const PIN:   u8 = 0x1;
const PRED1: u8 = 0x2;
const PRED2: u8 = 0x4;
const VISIT: u8 = 0x8;

fn scan(bump: &mut Bump<InsId>, ctr: BumpRef<ControlInfo>, code: &IndexSlice<InsId, Ins>) {
    for (id, &ins) in code.pairs() {
        if ins.opcode().is_pinned() {
            bump.push(id);
        } else if ins.opcode().is_control() {
            let idx: usize = id.into();
            bump[ctr.add_size(idx as _)] = Default::default();
        }
    }
}

fn visitpred(ctr: &mut IndexSlice<InsId, ControlInfo>, code: &IndexSlice<InsId, Ins>, id: InsId) {
    debug_assert!(code[id].opcode().is_control());
    match ctr[id] {
        0 => {
            ctr[id] = PRED1;
            for &c in code[id].controls() {
                visitpred(ctr, code, c);
            }
        },
        _ => {
            ctr[id] = PRED2;
        }
    }
}

fn markpins(
    bump: &mut BumpPtr,
    ctr: BumpRef<ControlInfo>,
    pin: BumpRef<InsId>,
    npin: usize,
    code: &IndexSlice<InsId, Ins>
) {
    for i in 0..npin {
        let p: usize = code[bump[pin.add_size(i as _)]].decode_C().into();
        bump[ctr.add_size(p as _)] |= PIN;
    }
}

fn visitelim(
    ctr: &mut IndexSlice<InsId, ControlInfo>,
    code: &mut IndexSlice<InsId, Ins>,
    id: InsId
) {
    if ctr[id] & VISIT != 0 {
        return
    }
    ctr[id] |= VISIT;
    let ins = code[id];
    if ins.opcode() == Opcode::GOTO {
        // if either:
        //   (1a) we have no pins; or
        //   (1b) we are the only precedessor,
        // then eliminate this GOTO and merge to successor
        // else if:
        //   (2) we are the only successor,
        // then eliminate this GOTO and merge to precedessor
        let target = ins.decode_V();
        if ctr[id] & PIN == 0 || ctr[target] & PRED2 == 0 {
            code[id] = ins.set_opcode(Opcode::NOP).set_b(zerocopy::transmute!(target));
        } else if ctr[id] & PRED2 == 0 {
            code[id] = ins.set_opcode(Opcode::NOP).set_b(!0);
        }
    }
    let elim = code[id].opcode() == Opcode::NOP;
    for (i, &(mut c)) in ins.controls().iter().enumerate() {
        visitelim(ctr, code, c);
        let mut cins = code[c];
        if cins.opcode() == Opcode::NOP {
            while cins.opcode() == Opcode::NOP {
                if cins.b() == !0 {
                    code[c] = cins.set_b(zerocopy::transmute!(id));
                }
                c = cins.decode_V();
                cins = code[c];
            }
            if elim {
                code[id] = code[id].set_a(zerocopy::transmute!(c));
            } else {
                code[id].controls_mut()[i] = c;
            }
        }
    }
}

fn patchpins(code: &mut IndexSlice<InsId, Ins>, pin: &[InsId]) {
    for &p in pin {
        let mut c = code[p].decode_C();
        if code[c].opcode() == Opcode::NOP {
            while code[c].opcode() == Opcode::NOP {
                c = zerocopy::transmute!(code[c].b());
            }
            code[p].controls_mut()[0] = c;
        }
    }
}

impl FuncPass for OptGoto {

    fn new(_: &mut Ccx<Absent>) -> Self {
        Default::default()
    }

    fn run(ccx: &mut Ocx, fid: FuncId) {
        let base = ccx.tmp.end();
        let func = &mut ccx.ir.funcs[fid];
        let code = func.code.inner_mut();
        let ncode = code.raw.len();
        let (ctr_ptr, _) = ccx.tmp.reserve_dst::<IndexSlice<InsId, ControlInfo>>(ncode);
        let pins_base = ccx.tmp.end().cast_up::<InsId>();
        scan(ccx.tmp.align_for(), ctr_ptr.cast(), code);
        let npin = ccx.tmp.end().cast::<InsId>().size_index() - pins_base.size_index();
        visitpred(ccx.tmp.get_dst_mut(ctr_ptr, ncode), code, func.entry);
        markpins(&mut ccx.tmp, ctr_ptr.cast(), pins_base, npin, code);
        visitelim(ccx.tmp.get_dst_mut(ctr_ptr, ncode), code, func.entry);
        patchpins(code, &ccx.tmp[pins_base..]);
        while code[func.entry].opcode() == Opcode::NOP {
            func.entry = code[func.entry].decode_V();
        }
        ccx.tmp.truncate(base);
    }

}
