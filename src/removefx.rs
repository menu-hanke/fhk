//! Move FX phis to the end.

use core::mem::swap;

use alloc::boxed::Box;
use alloc::vec;

use crate::bump::{Bump, BumpRef};
use crate::compile::{self, Ccx, Phase};
use crate::index::{self, IndexSlice};
use crate::ir::{Func, FuncId, Ins, InsId, Opcode, Phi, PhiId, Type};
use crate::minivec::MiniIndexValueVec;

// func -> phi reordering [old phi -> new phi]
pub struct RemoveFx {
    funcs: Box<IndexSlice<FuncId, BumpRef<PhiId>>>,
    bump: Bump
}

fn reorder(
    work: &mut Bump<PhiId>,
    func: &mut Func,
    phis: &mut MiniIndexValueVec<PhiId, Phi>
) -> BumpRef<PhiId> {
    let (ptr, order) = work.push_zeroed_slice(func.phis.end().into());
    let order = IndexSlice::<PhiId, PhiId>::from_raw_mut(order);
    let mut cursor1 = 0.into();
    let mut cursor2 = func.phis.end()-1;
    for (idx, phi) in func.phis.pairs() {
        match phi.type_ {
            Type::FX => {
                order[cursor2] = idx;
                cursor2 -= 1;
            },
            _ => {
                order[cursor1] = idx;
                cursor1 += 1;
            }
        }
        if idx+1 == func.arg { func.arg = cursor1; }
        if idx+1 == func.ret { func.ret = cursor1; }
    }
    func.fx = cursor1;
    phis.clear();
    let fphis: &IndexSlice<PhiId, Phi> = &*func.phis.inner_mut();
    for &idx in &order.raw {
        phis.push(fphis[idx]);
    }
    swap(phis, &mut func.phis);
    ptr
}

fn patch(ctx: &RemoveFx, this: FuncId, code: &mut IndexSlice<InsId, Ins>) {
    for id in index::iter_span(code.end()) {
        let ins = code[id];
        let opcode = ins.opcode();
        match opcode {
            Opcode::JMP | Opcode::PHI => {
                let abc = code[id].abc_mut();
                let idx = match opcode { Opcode::JMP => 2, _ => 1 };
                abc[idx] = zerocopy::transmute!(ctx.bump[ctx.funcs[this].add_size(abc[idx] as _)]);
            },
            Opcode::RES => {
                let (call, phi) = ins.decode_RES();
                let call = code[call];
                let func = match call.opcode() { Opcode::CALL => call.b(), _/*CALLB(I)*/ => call.c() };
                let phi: usize = phi.into();
                let newphi = ctx.bump[ctx.funcs[zerocopy::transmute!(func)].add_size(phi as _)];
                code[id] = ins.set_b(zerocopy::transmute!(newphi));
            },
            _ => {}
        }
    }
}

impl Phase for RemoveFx {

    fn new(ccx: &mut Ccx) -> compile::Result<Self> {
        Ok(RemoveFx {
            funcs: IndexSlice::from_raw_box(
                       vec![BumpRef::zero(); ccx.ir.funcs.raw.len()]
                       .into_boxed_slice()
                   ),
            bump: Default::default()
        })
    }

    fn run(ccx: &mut Ccx<Self>) -> compile::Result {
        let ctx = &mut *ccx.data;
        let insert = ctx.bump.align_for::<PhiId>();
        let mut phis = Default::default();
        for (id, func) in ccx.ir.funcs.pairs_mut() {
            ctx.funcs[id] = reorder(insert, func, &mut phis);
        }
        for (id, func) in ccx.ir.funcs.pairs_mut() {
            patch(ctx, id, func.code.inner_mut());
        }
        Ok(())
    }

}
