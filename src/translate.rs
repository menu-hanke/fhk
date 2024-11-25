//! IR -> Cranelift translation.

use cranelift_codegen::ir::condcodes::{FloatCC, IntCC};
use cranelift_codegen::ir::{InstBuilder, MemFlags, TrapCode, Value};
use zerocopy::Unalign;

use crate::bump::BumpRef;
use crate::lang::Lang;
use crate::mem::SizeClass;
use crate::support::{ALLOC, DSINIT};
use crate::compile;
use crate::emit::{block2cl, irt2cl, loadslot, storeslot, v2block, Ecx, Emit, MEM_RESULT};
use crate::ir::{Bundle, FuncKind, InsId, LangOp, Opcode, PhiId, Query, Type};
use crate::schedule::BlockId;

fn ctrargs(emit: &mut Emit, target: BlockId, jmp: Option<(PhiId, Value)>) {
    let mut src = emit.blockparams[emit.block]
        .ones()
        .zip(emit.fb.ctx.func.dfg.block_params(block2cl(emit.block)));
    for phi in &emit.blockparams[target] {
        if let Some((jphi, jval)) = jmp {
            if phi == jphi {
                emit.tmp_val.push(jval);
                continue;
            }
        }
        loop {
            let (sphi, &sval) = src.next().unwrap();
            if sphi == phi {
                emit.tmp_val.push(sval);
                break;
            }
        }
    }
}

// TODO: rethink the part that computes the blockparams. phis only need to be passed when jumping
//       to the block containing the phi.
//       because the passed value necessarily dominates the JMP.
fn emitjump(ecx: &mut Ecx, target: InsId, phi: Option<(PhiId, Value)>) {
    let emit = &mut *ecx.data;
    let target = v2block(emit.values[target]);
    emit.tmp_val.clear();
    ctrargs(emit, target, phi);
    emit.fb.ins().jump(block2cl(target), &emit.tmp_val);
}

fn ins_jmp(ecx: &mut Ecx, id: InsId) {
    let emit = &mut *ecx.data;
    let ins = emit.code[id];
    let (value, target, phi) = ins.decode_JMP();
    let func = &ecx.ir.funcs[emit.fid];
    'jret: {
        if phi < func.ret {
            let ty = func.phis.at(phi).type_;
            if ty != Type::FX {
                let phi: usize = phi.into();
                match func.kind {
                    FuncKind::User() => {
                        // user funcs return normally
                        break 'jret;
                    },
                    FuncKind::Query(Query { offsets, .. }) => {
                        let res = emit.fb.ctx.func.dfg.block_params(block2cl(BlockId::START))[1];
                        let ofs = ecx.perm[offsets.add_size(phi as _)];
                        emit.fb.ins().store(MEM_RESULT, emit.values[value], res, ofs as i32);
                    },
                    FuncKind::Bundle(Bundle { scl, slots, .. }) => {
                        let vmctx = emit.fb.vmctx();
                        let slot = ecx.perm[slots.add_size(phi as _)];
                        storeslot(emit, vmctx, emit.idx, scl, slot, ty, emit.values[value]);
                    }
                }
            }
            emitjump(ecx, target, None);
            return;
        }
    }
    emitjump(ecx, target, Some((phi, ecx.data.values[value])));
}

fn ins_goto(ecx: &mut Ecx, id: InsId) {
    let target = ecx.data.code[id].decode_GOTO();
    emitjump(ecx, target, None);
}

fn ins_if(ecx: &mut Ecx, id: InsId) {
    let emit = &mut *ecx.data;
    let (cond, tru, fal) = emit.code[id].decode_IF();
    let cond = emit.values[cond];
    let tru = v2block(emit.values[tru]);
    let fal = v2block(emit.values[fal]);
    emit.tmp_val.clear();
    ctrargs(emit, tru, None);
    let boundary = emit.tmp_val.len();
    ctrargs(emit, fal, None);
    emit.fb.ins().brif(
        cond,
        block2cl(tru),
        &emit.tmp_val[..boundary],
        block2cl(fal),
        &emit.tmp_val[boundary..]
    );
}

fn ins_ret(ecx: &mut Ecx) {
    // TODO: user funcs return values here.
    ecx.data.fb.ins().return_(&[]);
}

fn ins_ub(ecx: &mut Ecx) {
    // TODO: call an rt function and abort.
    // execution of this instruction is always a compiler bug.
    let emit = &mut *ecx.data;
    emit.fb.ctx.func.layout.set_cold(emit.fb.block);
    emit.fb.ins().trap(TrapCode::User(0));
}

fn ins_phi(ecx: &mut Ecx, id: InsId) {
    let emit = &mut *ecx.data;
    let ins = emit.code[id];
    if ins.type_() == Type::FX { return }
    let (ctr, phi) = ins.decode_PHI();
    let idx = emit.blockparams[emit.block].popcount_leading(phi);
    emit.values[id] = emit.fb.ctx.func.dfg.block_params(
        block2cl(v2block(emit.values[ctr])))[idx as usize];
}

fn ins_kintx(ecx: &mut Ecx, id: InsId) {
    use Type::*;
    let ins = ecx.data.code[id];
    let type_ = ins.type_();
    let data = ins.bc();
    let k = match ins.opcode() {
        Opcode::KINT => data as i64,
        Opcode::KINT64 => {
            let data: BumpRef<Unalign<i64>> = zerocopy::transmute!(data);
            ecx.intern.bump()[data].get()
        },
        _ => unreachable!()
    };
    let value = match type_ {
        I8 | I16 | I32 | I64 | PTR | B1 => ecx.data.fb.ins().iconst(irt2cl(type_), k),
        F32 | F64 => {
            let data = match type_ {
                F32 => ecx.mcode.data.intern(&(k as f32)).to_bump().cast(),
                _   => ecx.mcode.data.intern(&(k as f64)).to_bump().cast()
            };
            let data = ecx.data.fb.importdataref(data);
            let ptr = ecx.data.fb.dataptr(data);
            ecx.data.fb.kload(type_, ptr)
        },
        FX | LSV => unreachable!()
    };
    ecx.data.values[id] = value;
}

fn ins_mov(ecx: &mut Ecx, id: InsId) {
    let emit = &mut *ecx.data;
    let value = emit.code[id].decode_V();
    emit.values[id] = emit.values[value];
}

fn ins_arith(ecx: &mut Ecx, id: InsId) {
    use {Type::*, Opcode::*};
    let emit = &mut *ecx.data;
    let ins = emit.code[id];
    let (left, right) = ins.decode_VV();
    debug_assert!(emit.code[left].type_() == ins.type_());
    debug_assert!(emit.code[right].type_() == ins.type_());
    let left = emit.values[left];
    let right = emit.values[right];
    let value = match (ins.opcode(), ins.type_()) {
        (ADD, F32|F64) => emit.fb.ins().fadd(left, right),
        (SUB, F32|F64) => emit.fb.ins().fsub(left, right),
        (MUL, F32|F64) => emit.fb.ins().fmul(left, right),
        (DIV, F32|F64) => emit.fb.ins().fdiv(left, right),
        (ADD, I8|I16|I32|I64) => emit.fb.ins().iadd(left, right),
        (SUB, I8|I16|I32|I64) => emit.fb.ins().isub(left, right),
        (MUL, I8|I16|I32|I64) => emit.fb.ins().imul(left, right),
        (DIV, I8|I16|I32|I64) => emit.fb.ins().sdiv(left, right), // nb. signed
        _ => unreachable!()
    };
    emit.values[id] = value;
}

fn ins_addp(ecx: &mut Ecx, id: InsId) {
    let emit = &mut *ecx.data;
    let (left, right) = emit.code[id].decode_VV();
    let right = emit.fb.coerce(emit.values[right], Type::I64);
    emit.values[id] = emit.fb.ins().iadd(emit.values[left], right);
}

fn ins_cmp(ecx: &mut Ecx, id: InsId) {
    use {Type::*, Opcode::*};
    let emit = &mut *ecx.data;
    let ins = emit.code[id];
    let (left, right) = ins.decode_VV();
    let ty = emit.code[left].type_();
    debug_assert!(emit.code[right].type_() == ty);
    debug_assert!(ins.type_() == Type::B1);
    let left = emit.values[left];
    let right = emit.values[right];
    let opcode = ins.opcode();
    let value = match ty {
        F32 | F64 => {
            let cmp = match opcode {
                EQ  => FloatCC::Equal,
                NE  => FloatCC::NotEqual,
                LT  => FloatCC::LessThan,
                LE  => FloatCC::LessThanOrEqual,
                ULT => FloatCC::UnorderedOrLessThan,
                ULE => FloatCC::UnorderedOrLessThanOrEqual,
                _   => unreachable!()
            };
            emit.fb.ins().fcmp(cmp, left, right)
        },
        I8 | I16 | I32 | I64 => {
            let cmp = match opcode {
                EQ  => IntCC::Equal,
                NE  => IntCC::NotEqual,
                LT  => IntCC::SignedLessThan,
                LE  => IntCC::SignedLessThanOrEqual,
                ULT => IntCC::UnsignedLessThan,
                ULE => IntCC::UnsignedLessThanOrEqual,
                _   => unreachable!()
            };
            emit.fb.ins().icmp(cmp, left, right)
        },
        _ => unreachable!()
    };
    emit.values[id] = value;
}

// TODO: separate escaping and non-escaping allocs
// TODO 2: consider not making this call the allocator every time.
// instead, make a fast path like this:
//   | cursor = load vmctx.cursor   ; guaranteed aligned to some boundary (4?)
//   | newcursor = cursor - size
//   | if overflow  ->  jmp slowpath
//   | newcursor = cursor & mask     ; align only if required alignment != fixed boundary
//   | store vmctx.cursor = newcursor
//   | base = load vmctx.base
//   | ptr = base + newcursor
// (NOTE 3: the align boundary could be computed dynamically by counting ALLOC instructions
//  with KINT alignment and taking the most common one)
fn ins_alloc(ecx: &mut Ecx, id: InsId) {
    let emit = &mut *ecx.data;
    let (size, align) = emit.code[id].decode_VV();
    let alloc = emit.supp.instantiate(&mut ecx.mcode, &ALLOC::new());
    let alloc = emit.fb.importsupp(&emit.supp, alloc.cast());
    let size = emit.fb.coerce(emit.values[size], Type::I64);
    let align = emit.fb.coerce(emit.values[align], Type::I64);
    let call = emit.fb.ins().call(alloc, &[size, align]);
    emit.values[id] = emit.fb.ctx.func.dfg.inst_results(call)[0];
}

fn ins_store(ecx: &mut Ecx, id: InsId) {
    let emit = &mut *ecx.data;
    let ins = emit.code[id];
    let (ptr, value) = ins.decode_VV();
    emit.fb.ins().store(MemFlags::trusted(), emit.values[value], emit.values[ptr], 0);
}

fn ins_load(ecx: &mut Ecx, id: InsId) {
    let emit = &mut *ecx.data;
    let ins = emit.code[id];
    let ptr = ins.decode_V();
    let ty = irt2cl(ins.type_());
    emit.values[id] = emit.fb.ins().load(ty, MemFlags::trusted(), emit.values[ptr], 0);
}

fn ins_callb(ecx: &mut Ecx, id: InsId) {
    let emit = &mut *ecx.data;
    let (idx, _, bundle) = emit.code[id].decode_CALLB();
    let FuncKind::Bundle(Bundle { scl, check, .. }) = ecx.ir.funcs[bundle].kind
        else { unreachable!() };
    let vmctx = emit.fb.vmctx();
    let bit = loadslot(emit, vmctx, emit.values[idx], scl, check, Type::B1);
    let merge_block = emit.fb.newblock();
    let call_block = emit.fb.newblock();
    emit.fb.ctx.func.layout.set_cold(call_block);
    emit.fb.ins().brif(bit, merge_block, &[], call_block, &[]);
    emit.fb.block = call_block;
    let funcref = emit.fb.importfunc(&ecx.ir, bundle);
    let args = [emit.values[idx]];
    emit.fb.ins().call(funcref, match scl { SizeClass::GLOBAL => &[], _ => &args });
    emit.fb.ins().jump(merge_block, &[]);
    emit.fb.block = merge_block;
}

fn ins_res(ecx: &mut Ecx, id: InsId) {
    let emit = &mut *ecx.data;
    let ins = emit.code[id];
    let ty = ins.type_();
    if ty == Type::FX { return; }
    let (call, phi) = ins.decode_RES();
    let value = match emit.code[call].opcode() {
        Opcode::CALL => todo!(),
        Opcode::CALLB | Opcode::CALLBI => {
            let (idx, _, bundle) = emit.code[call].decode_CALLB();
            let FuncKind::Bundle(Bundle { scl, slots, .. }) = ecx.ir.funcs[bundle].kind
                else { unreachable!() };
            debug_assert!(ecx.ir.funcs[bundle].phis.at(phi).type_ == ty);
            let vmctx = emit.fb.vmctx();
            let phi: usize = phi.into();
            loadslot(emit, vmctx, emit.values[idx], scl, ecx.perm[slots.add_size(phi as _)], ty)
        },
        _ => unreachable!()
    };
    ecx.data.values[id] = value;
}

fn ins_binit(ecx: &mut Ecx, id: InsId) {
    let emit = &mut *ecx.data;
    let (size, bundle) = emit.code[id].decode_BINIT();
    let func = &ecx.ir.funcs[bundle];
    let FuncKind::Bundle(bundle) = &func.kind else { unreachable!() };
    if !bundle.scl.is_dynamic() { /* NOP */ return }
    let dsinit = emit.supp.instantiate(&mut ecx.mcode, &DSINIT::new());
    let dsinit = emit.fb.importsupp(&emit.supp, dsinit.cast());
    let tab = emit.fb.importdataref(bundle.dynslots.cast());
    let tab = emit.fb.dataptr(tab);
    let nret: usize = func.ret.into();
    // bitmap + one for each return
    let num = emit.fb.ins().iconst(irt2cl(Type::I32), (1 + nret) as i64);
    emit.fb.ins().call(dsinit, &[tab, num, emit.values[size]]);
}

fn ins_lop(ecx: &mut Ecx, id: InsId) -> compile::Result {
    let LangOp { lang, op } = ecx.data.code[id].decode_L();
    ecx.data.values[id] = Lang::from_u8(lang).emit(ecx, id, op)?;
    Ok(())
}

pub fn translate(ecx: &mut Ecx, id: InsId) -> compile::Result {
    use Opcode::*;
    let ins = ecx.data.code[id];
    if ins.type_() != Type::LSV {
        match ins.opcode() {
            NOP => { /* NOP */ },
            JMP => ins_jmp(ecx, id),
            GOTO => ins_goto(ecx, id),
            IF => ins_if(ecx, id),
            RET => ins_ret(ecx),
            TRET => todo!(),
            UB => ins_ub(ecx),
            PHI => ins_phi(ecx, id),
            KNOP => { /* NOP */ },
            KINT | KINT64 => ins_kintx(ecx, id),
            KFP64 => todo!(),
            KSTR => todo!(),
            MOV | MOVB | MOVF => ins_mov(ecx, id),
            CONV => todo!(),
            ADD | SUB | MUL | DIV => ins_arith(ecx, id),
            ADDP => ins_addp(ecx, id),
            POW => todo!(),
            NEG => todo!(),
            EQ | NE | LT | LE | ULT | ULE => ins_cmp(ecx, id),
            ALLOC => ins_alloc(ecx, id),
            STORE => ins_store(ecx, id),
            LOAD => ins_load(ecx, id),
            BOX => todo!(),
            CALL => todo!(),
            CALLB | CALLBI => ins_callb(ecx, id),
            CARG => { /* NOP */ },
            RES => ins_res(ecx, id),
            BINIT => ins_binit(ecx, id),
            LOV | LOVV | LOX | LOXX => ins_lop(ecx, id)?
        }
    }
    Ok(())
}
