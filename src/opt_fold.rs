//! Constant folding + simplification + CSE + DCE

use core::mem::swap;

use alloc::collections::vec_deque::VecDeque;
use hashbrown::hash_table::Entry;
use hashbrown::HashTable;
use zerocopy::Unalign;

use crate::bump::BumpRef;
use crate::compile::Ccx;
use crate::hash::fxhash;
use crate::index::{IndexOption, IndexVec};
use crate::ir::{ins_matches, Func, FuncId, Ins, InsId, Opcode, Type};
use crate::optimize::{FuncPass, Ocx, Optimize};
use crate::typestate::{Absent, Access, R};

#[derive(Default)]
pub struct Fold {
    old_new: IndexVec<InsId, IndexOption<InsId>>, // old ins -> new ins
    next: VecDeque<InsId>,
    cse_map: HashTable<InsId>,
    code: IndexVec<InsId, Ins>
}

type Fcx<'a, 'b> = Ccx<Optimize, R<'a>, R<'b>>;

enum FoldStatus {
    Done(Ins),
    Again(Ins),
    New(InsId),
    // Old(InsId)
}

fn kintvalue(fcx: &Fcx, ins: Ins) -> i64 {
    use Opcode::*;
    match ins.opcode() {
        KINT => ins.bc() as i32 as _,
        KINT64 => {
            let data: BumpRef<Unalign<i64>> = zerocopy::transmute!(ins.bc());
            fcx.intern.bump()[data].get()
        },
        KFP64 => {
            let data: BumpRef<Unalign<f64>> = zerocopy::transmute!(ins.bc());
            fcx.intern.bump()[data].get() as _
        },
        _ => unreachable!()
    }
}

fn kfpvalue(fcx: &Fcx, ins: Ins) -> f64 {
    use Opcode::*;
    match ins.opcode() {
        KINT => ins.bc() as i32 as _,
        KINT64 => {
            let data: BumpRef<Unalign<i64>> = zerocopy::transmute!(ins.bc());
            fcx.intern.bump()[data].get() as _
        },
        KFP64 => {
            let data: BumpRef<Unalign<f64>> = zerocopy::transmute!(ins.bc());
            fcx.intern.bump()[data].get()
        },
        _ => unreachable!()
    }
}

fn newkint(fcx: &mut Fcx, ty: Type, value: i64) -> Ins {
    if value == (value as i32) as _ {
        Ins::KINT(ty, value as _)
    } else {
        Ins::KINT64(ty, zerocopy::transmute!(fcx.intern.intern(&value.to_ne_bytes()).to_bump()))
    }
}

fn newkfp(fcx: &mut Fcx, ty: Type, value: f64) -> Ins {
    if value == (value as i32) as _ {
        Ins::KINT(ty, value as i32 as _)
    } else {
        Ins::KFP64(ty, zerocopy::transmute!(fcx.intern.intern(&value.to_ne_bytes()).to_bump()))
    }
}

fn foldintarith(op: Opcode, left: i64, right: i64) -> i64 {
    use Opcode::*;
    match op {
        ADD  => left + right,
        SUB  => left - right,
        MUL  => left * right,
        DIV  => left / right,
        UDIV => ((left as u64) / (right as u64)) as _,
        _    => unreachable!()
    }
}

fn foldfparith(op: Opcode, left: f64, right: f64) -> f64 {
    use Opcode::*;
    match op {
        ADD  => left + right,
        SUB  => left - right,
        MUL  => left * right,
        DIV  => left / right,
        POW  => left.powf(right),
        _    => unreachable!()
    }
}

fn foldintcmp(op: Opcode, left: i64, right: i64) -> bool {
    use Opcode::*;
    match op {
        EQ  => left == right,
        NE  => left != right,
        LT  => left < right,
        LE  => left <= right,
        ULT => (left as u64) < (right as u64),
        ULE => (left as u64) <= (right as u64),
        _   => unreachable!()
    }
}

fn foldfpcmp(op: Opcode, left: f64, right: f64) -> bool {
    use Opcode::*;
    match op {
        EQ  => left == right,
        NE  => left != right,
        LT  => left < right,
        LE  => left <= right,
        _   => unreachable!()
    }
}

fn fold(fcx: &mut Fcx, mut ins: Ins) -> FoldStatus {
    use Opcode::*;
    let opt = &mut *fcx.data;
    let code = &opt.fold.code;
    macro_rules! m { ($($p:tt)*) => { ins_matches!(code, ins; _ $($p)*) }; }
    let op = ins.opcode();
    match op {

        // fold constant arithmetic
        ADD|SUB|MUL|DIV|UDIV|POW if m!(const const) => {
            let (left, right) = ins.decode_VV();
            let left = code[left];
            let right = code[right];
            let ty = ins.type_();
            debug_assert!(left.type_() == ty);
            debug_assert!(right.type_() == ty);
            if ty.is_fp() {
                ins = newkfp(fcx, ty, foldfparith(op, kfpvalue(fcx, left), kfpvalue(fcx, right)));
            } else {
                debug_assert!(ty.is_int());
                ins = newkint(fcx, ty, foldintarith(op, kintvalue(fcx, left), kintvalue(fcx, right)));
            }
            FoldStatus::Done(ins)
        },

        // fold constant comparisons
        EQ|NE|LT|LE|ULT|ULE if m!(const const) => {
            let (left, right) = ins.decode_VV();
            let left = code[left];
            let right = code[right];
            debug_assert!(left.type_() == right.type_());
            debug_assert!(ins.type_() == Type::B1);
            let value = if left.type_().is_fp() {
                foldfpcmp(op, kfpvalue(fcx, left), kfpvalue(fcx, right))
            } else {
                debug_assert!(left.type_().is_int());
                foldintcmp(op, kintvalue(fcx, left), kintvalue(fcx, right))
            };
            FoldStatus::Done(Ins::KINT(Type::B1, value as _))
        },

        // fold comparison against itself
        // (note: you can only do this for integers because of nans)
        EQ|NE|LT|LE|ULT|ULE if ins.a() == ins.b() && !code[ins.decode_V()].type_().is_fp() => {
            FoldStatus::Done(Ins::KINT(Type::B1, (EQ|LE|ULE).contains(op) as _))
        },

        // sort commutative operands:
        // * constants go to right
        // * non-constants are sorted by insid
        ADD|MUL|EQ|NE if m!(const _) || (ins.a() > ins.b() && !m!(_ const)) => {
            ins.inputs_mut().swap(0, 1);
            FoldStatus::Again(ins)
        },

        // x+0 = x-0 = x
        ADD|SUB if m!(_ 0) => FoldStatus::New(ins.decode_V()),

        // x*1 = x/1 = x
        MUL|DIV|UDIV if m!(_ 1) => FoldStatus::New(ins.decode_V()),

        // x*0 = 0
        MUL if m!(_ 0) && !ins.type_().is_fp() => FoldStatus::Done(Ins::KINT(ins.type_(), 0)),

        // fold constant negation
        NEG if m!(const) => {
            let operand = code[ins.decode_V()];
            let ty = ins.type_();
            FoldStatus::Done(match ty {
                Type::F32|Type::F64 => newkfp(fcx, ty, -kfpvalue(fcx, operand)),
                Type::I8|Type::I16|Type::I32|Type::I64 => newkint(fcx, ty, -kintvalue(fcx, operand)),
                Type::B1 => Ins::KINT(Type::B1, (operand == Ins::KINT(Type::B1, 0)) as _),
                _ => unreachable!()
            })
        },

        // eliminate MOVs
        MOV => {
            let value = ins.decode_V();
            debug_assert!(code[value].opcode() != MOV);
            FoldStatus::New(value)
        },

        // eliminate GOTOs
        // GOTO => {
        //     FoldStatus::Old(ins.decode_V())
        // },

        // eliminate constant IF
        IF if m!(const) => {
            let (cond, left, right) = ins.decode_IF();
            let value = code[cond];
            debug_assert!(value == Ins::KINT(Type::B1, 0) || value == Ins::KINT(Type::B1, 1));
            FoldStatus::Done(Ins::GOTO(if value == Ins::KINT(Type::B1, 0) { right } else { left }))
        },

        // eliminate IF if both branches are the same
        IF if ins.b() == ins.c() => {
            FoldStatus::Done(Ins::GOTO(zerocopy::transmute!(ins.b())))
        },

        _ => FoldStatus::Done(ins)
    }
}

fn visit(fcx: &mut Fcx, func: &Func, id: InsId) -> InsId {
    if let Some(new) = fcx.data.fold.old_new[id].unpack() {
        return new;
    }
    let mut ins = func.code.at(id);
    for input in ins.inputs_mut() {
        *input = visit(fcx, func, *input);
    }
    let new = loop {
        match fold(fcx, ins) {
            FoldStatus::Again(xins) => ins = xins,
            FoldStatus::New(id) => break id,
            // FoldStatus::Old(id) => {
            //     // this cannot cause infinite recursion, because the frontend will never
            //     // generate an infinite loop, so an instruction can never unconditionally
            //     // loop back to itself.
            //     break visit(fcx, func, id)
            // },
            FoldStatus::Done(ins) => {
                if ins.opcode().is_control() {
                    fcx.data.fold.next.extend(ins.controls());
                }
                break match ins.opcode().is_cse() {
                    true => {
                        let opt = &mut *fcx.data;
                        match opt.fold.cse_map.entry(
                            fxhash(ins),
                            |idx| opt.fold.code[*idx] == ins,
                            |idx| fxhash(opt.fold.code[*idx])
                        ) {
                            Entry::Occupied(e) => *e.get(),
                            Entry::Vacant(e) => {
                                let id = opt.fold.code.push(ins);
                                e.insert(id);
                                id
                            }
                        }
                    },
                    false => fcx.data.fold.code.push(ins)
                }
            }
        }
    };
    fcx.data.fold.old_new[id] = Some(new).into();
    new
}

fn fixup(fold: &mut Fold) {
    for ins in &mut fold.code.raw {
        for ctrl in ins.controls_mut() {
            *ctrl = fold.old_new[*ctrl].unwrap();
        }
    }
}

impl FuncPass for Fold {

    fn new(_: &mut Ccx<Absent>) -> Self {
        Default::default()
    }

    fn run(ocx: &mut Ocx, fid: FuncId) {
        ocx.freeze_ir(|fcx| {
            let ir = Access::borrow(&fcx.ir);
            let func = &ir.funcs[fid];
            debug_assert!(fcx.data.fold.next.is_empty());
            fcx.data.fold.old_new.clear();
            fcx.data.fold.old_new.raw.resize(func.code.end().into(), None.into());
            fcx.data.fold.cse_map.clear();
            fcx.data.fold.code.clear();
            fcx.data.fold.next.push_back(func.entry);
            while let Some(id) = fcx.data.fold.next.pop_front() {
                visit(fcx, func, id);
            }
            fixup(&mut fcx.data.fold);
        });
        let func = &mut ocx.ir.funcs[fid];
        func.entry = ocx.data.fold.old_new[func.entry].unwrap();
        swap(func.code.inner_mut(), &mut ocx.data.fold.code);
    }

}
