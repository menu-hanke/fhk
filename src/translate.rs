//! IR -> Cranelift translation.

use cranelift_codegen::ir::condcodes::{FloatCC, IntCC};
use cranelift_codegen::ir::{InstBuilder, MemFlags, TrapCode, Value};
use zerocopy::Unalign;

use crate::bump::BumpRef;
use crate::controlflow::BlockId;
use crate::lang::Lang;
use crate::mem::{CursorType, SizeClass};
use crate::compile;
use crate::emit::{block2cl, irt2cl, loadslot, storeslot, Ecx, Emit, InsValue, MEM_RESULT};
use crate::ir::{Chunk, FuncKind, InsId, LangOp, Opcode, PhiId, Query, Type};
use crate::support::{NativeFunc, SuppFunc};

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
    let target = emit.values[target].block();
    emit.tmp_val.clear();
    ctrargs(emit, target, phi);
    emit.fb.ins().jump(block2cl(target), &emit.tmp_val);
}

fn ins_jmp(ecx: &mut Ecx, id: InsId) {
    let emit = &mut *ecx.data;
    let ins = emit.code[id];
    let (value, target, phi) = ins.decode_JMP();
    let func = &ecx.ir.funcs[emit.fid];
    let ty = emit.code[value].type_();
    'jret: {
        if phi < func.ret && ty != Type::FX {
            let phi: usize = phi.into();
            match func.kind {
                FuncKind::User() => {
                    // user funcs return normally
                    break 'jret;
                },
                FuncKind::Query(Query { offsets, .. }) => {
                    let res = emit.fb.ctx.func.dfg.block_params(block2cl(BlockId::START))[1];
                    let ofs = ecx.perm[offsets.offset(phi as _)];
                    emit.fb.ins().store(MEM_RESULT, emit.values[value].value(), res, ofs as i32);
                },
                FuncKind::Chunk(Chunk { scl, slots, .. }) => {
                    let vmctx = emit.fb.vmctx();
                    let slot = ecx.perm[slots.offset(phi as _)];
                    storeslot(emit, vmctx, emit.idx, scl, slot, ty, emit.values[value].value());
                }
            }
        }
    }
    // TODO: handle fx types properly (whatever that means)
    let jmp = match ty {
        Type::FX => None,
        _ => Some((phi, ecx.data.values[value].value()))
    };
    emitjump(ecx, target, jmp);
}

fn ins_goto(ecx: &mut Ecx, id: InsId) {
    let target = ecx.data.code[id].decode_GOTO();
    emitjump(ecx, target, None);
}

fn ins_if(ecx: &mut Ecx, id: InsId) {
    let emit = &mut *ecx.data;
    let (cond, tru, fal) = emit.code[id].decode_IF();
    let cond = emit.values[cond].value();
    let tru = emit.values[tru].block();
    let fal = emit.values[fal].block();
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

fn coldblock(emit: &mut Emit) {
    // cranelift doesn't allow marking the entry block as cold
    if emit.block != BlockId::START {
        emit.fb.ctx.func.layout.set_cold(block2cl(emit.block));
    }
}

fn ins_ub(ecx: &mut Ecx) {
    // TODO: call an rt function and abort.
    // execution of this instruction is always a compiler bug.
    let emit = &mut *ecx.data;
    coldblock(emit);
    emit.fb.ins().trap(TrapCode::User(0));
}

fn ins_abort(ecx: &mut Ecx) {
    let emit = &mut *ecx.data;
    coldblock(emit);
    let abort = emit.fb.importsupp(&ecx.ir, SuppFunc::ABORT);
    emit.fb.ins().call(abort, &[]);
    // the call above doesn't return. this trap is here just to satisfy cranelift.
    emit.fb.ins().trap(TrapCode::User(0));
}

fn ins_phi(ecx: &mut Ecx, id: InsId) {
    let emit = &mut *ecx.data;
    let ins = emit.code[id];
    if ins.type_() == Type::FX {
        // TODO: handle this properly:
        //   * remove tmp_val
        //   * use InsValue instead of Value in ctrargs and emitjump
        emit.values[id] = InsValue { raw: !0 - 1 };
        return;
    }
    let (ctr, phi) = ins.decode_PHI();
    // phi must be scheduled in the same block as its control instruction:
    debug_assert!(emit.values[ctr].block() == emit.block);
    let idx = emit.blockparams[emit.block].popcount_leading(phi);
    emit.values[id] = InsValue::from_value(
        emit.fb.ctx.func.dfg.block_params(block2cl(emit.block))[idx as usize]
    );
}

fn ins_kintx(ecx: &mut Ecx, id: InsId) {
    use Type::*;
    let ins = ecx.data.code[id];
    let type_ = ins.type_();
    let data = ins.bc();
    let k = match ins.opcode() {
        Opcode::KINT => data as i32 as i64,
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
    ecx.data.values[id] = InsValue::from_value(value);
}

fn ins_kfp64(ecx: &mut Ecx, id: InsId) {
    let emit = &mut *ecx.data;
    let ins = emit.code[id];
    let b: BumpRef<Unalign<f64>> = zerocopy::transmute!(ins.bc());
    let k = ecx.intern.bump()[b].get();
    let type_ = ins.type_();
    let data = match type_ {
        Type::F32 => ecx.mcode.data.intern(&(k as f32)).to_bump().cast(),
        Type::F64 => ecx.mcode.data.intern(&k).to_bump().cast(),
        _ => unreachable!()
    };
    let data = emit.fb.importdataref(data);
    let ptr = emit.fb.dataptr(data);
    emit.values[id] = InsValue::from_value(emit.fb.kload(type_, ptr));
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
    let left = emit.values[left].value();
    let right = emit.values[right].value();
    let value = match (ins.opcode(), ins.type_()) {
        (ADD, F32|F64) => emit.fb.ins().fadd(left, right),
        (SUB, F32|F64) => emit.fb.ins().fsub(left, right),
        (MUL, F32|F64) => emit.fb.ins().fmul(left, right),
        (DIV, F32|F64) => emit.fb.ins().fdiv(left, right),
        (ADD, I8|I16|I32|I64) => emit.fb.ins().iadd(left, right),
        (SUB, I8|I16|I32|I64) => emit.fb.ins().isub(left, right),
        (MUL, I8|I16|I32|I64) => emit.fb.ins().imul(left, right),
        (DIV, I8|I16|I32|I64) => emit.fb.ins().sdiv(left, right),
        (UDIV, I8|I16|I32|I64) => emit.fb.ins().udiv(left, right),
        _ => unreachable!()
    };
    emit.values[id] = InsValue::from_value(value);
}

fn ins_pow(ecx: &mut Ecx, id: InsId) {
    let emit = &mut *ecx.data;
    let ins = emit.code[id];
    let (left, right) = ins.decode_VV();
    let left = emit.values[left].value();
    let right = emit.values[right].value();
    let func = emit.fb.importnative(NativeFunc::POWF64);
    let call = emit.fb.ins().call(func, &[left, right]);
    emit.values[id] = InsValue::from_value(emit.fb.ctx.func.dfg.inst_results(call)[0]);
}

fn ins_addp(ecx: &mut Ecx, id: InsId) {
    let emit = &mut *ecx.data;
    let (left, right) = emit.code[id].decode_VV();
    let right = emit.fb.coerce(emit.values[right].value(), Type::I64);
    emit.values[id] = InsValue::from_value(emit.fb.ins().iadd(emit.values[left].value(), right));
}

fn ins_neg(ecx: &mut Ecx, id: InsId) {
    use Type::*;
    let emit = &mut *ecx.data;
    let ins = emit.code[id];
    let operand = emit.values[ins.decode_V()].value();
    let value = match ins.type_() {
        I8|I16|I32|I64 => emit.fb.ins().ineg(operand),
        F32|F64 => emit.fb.ins().fneg(operand),
        B1 => emit.fb.ins().bxor_imm(operand, 1),
        _ => unreachable!()
    };
    emit.values[id] = InsValue::from_value(value);
}

fn ins_cmp(ecx: &mut Ecx, id: InsId) {
    use {Type::*, Opcode::*};
    let emit = &mut *ecx.data;
    let ins = emit.code[id];
    let (left, right) = ins.decode_VV();
    let ty = emit.code[left].type_();
    debug_assert!(emit.code[right].type_() == ty);
    debug_assert!(ins.type_() == Type::B1);
    let left = emit.values[left].value();
    let right = emit.values[right].value();
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
    emit.values[id] = InsValue::from_value(value);
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
    let alloc = emit.fb.importsupp(&ecx.ir, SuppFunc::ALLOC);
    let size = emit.fb.coerce(emit.values[size].value(), Type::I64);
    let align = emit.fb.coerce(emit.values[align].value(), Type::I64);
    let call = emit.fb.ins().call(alloc, &[size, align]);
    emit.values[id] = InsValue::from_value(emit.fb.ctx.func.dfg.inst_results(call)[0]);
}

fn ins_store(ecx: &mut Ecx, id: InsId) {
    let emit = &mut *ecx.data;
    let ins = emit.code[id];
    let (ptr, value) = ins.decode_VV();
    emit.fb.ins().store(MemFlags::trusted(), emit.values[value].value(), emit.values[ptr].value(), 0);
}

fn ins_load(ecx: &mut Ecx, id: InsId) {
    let emit = &mut *ecx.data;
    let ins = emit.code[id];
    let ptr = ins.decode_V();
    let ty = irt2cl(ins.type_());
    emit.values[id] = InsValue::from_value(
        emit.fb.ins().load(ty, MemFlags::trusted(), emit.values[ptr].value(), 0)
    );
}

// TODO: use BOX in lang_C (but lang_Lua can't use it because the "frame" address is fixed)
// (side note: a BOX equivalent for output parameters isn't useful since there's no CSE
//  opportunity - just use ALLOC)
// (side note 2: all calls should eventually use either BOX or their own LSV, not ALLOC,
//  because ALLOC can't be CSE'd)
fn ins_box(ecx: &mut Ecx, id: InsId) {
    let emit = &mut *ecx.data;
    let value = emit.code[id].decode_V();
    let frame = emit.fb.frame(&mut emit.frame);
    let opcode = emit.code[value].opcode();
    let ofs = match opcode {
        Opcode::CARG => {
            let mut args = value;
            let ofs = frame.layout.align(8);
            while emit.code[args].opcode() == Opcode::CARG {
                let (next, value) = emit.code[args].decode_CARG();
                let p = frame.layout.alloc_type(emit.code[value].type_());
                emit.fb.ins().stack_store(emit.values[value].value(), frame.slot, p as i32);
                args = next;
            }
            ofs
        },
        _ => {
            let ofs = frame.layout.alloc_type(emit.code[value].type_());
            emit.fb.ins().stack_store(emit.values[value].value(), frame.slot, ofs as i32);
            ofs
        }
    };
    emit.values[id] = InsValue { raw: ofs as _ };
}

fn ins_abox(ecx: &mut Ecx, id: InsId) {
    let emit = &mut *ecx.data;
    let (_, size, align) = emit.code[id].decode_ABOX();
    let frame = emit.fb.frame(&mut emit.frame);
    let ofs = frame.layout.alloc(size as _, align as _);
    emit.values[id] = InsValue { raw: ofs as _ };
}

fn ins_bref(ecx: &mut Ecx, id: InsId) {
    let emit = &mut *ecx.data;
    let box_ = emit.code[id].decode_V();
    debug_assert!((Opcode::BOX|Opcode::ABOX).contains(emit.code[box_].opcode()));
    let slot = emit.frame.as_ref().unwrap().slot;
    let ofs = emit.values[box_].raw;
    let ptr = emit.fb.ins().stack_addr(irt2cl(Type::PTR), slot, ofs as i32);
    emit.values[id] = InsValue::from_value(ptr);
}

fn ins_callc(ecx: &mut Ecx, id: InsId) {
    let emit = &mut *ecx.data;
    let (idx, _, chunk) = emit.code[id].decode_CALLC();
    let FuncKind::Chunk(Chunk { scl, check, .. }) = ecx.ir.funcs[chunk].kind
        else { unreachable!() };
    let vmctx = emit.fb.vmctx();
    let bit = loadslot(emit, vmctx, emit.values[idx].value(), scl, check, Type::B1);
    let merge_block = emit.fb.newblock();
    let call_block = emit.fb.newblock();
    emit.fb.ctx.func.layout.set_cold(call_block);
    emit.fb.ins().brif(bit, merge_block, &[], call_block, &[]);
    emit.fb.block = call_block;
    let funcref = emit.fb.importfunc(&ecx.ir, chunk);
    let args = [emit.values[idx].value()];
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
        Opcode::CALLC | Opcode::CALLCI => {
            let (idx, _, chunk) = emit.code[call].decode_CALLC();
            let FuncKind::Chunk(Chunk { scl, slots, .. }) = ecx.ir.funcs[chunk].kind
                else { unreachable!() };
            debug_assert!(ecx.ir.funcs[chunk].phis.at(phi).type_ == ty);
            let vmctx = emit.fb.vmctx();
            let phi: usize = phi.into();
            loadslot(emit, vmctx, emit.values[idx].value(), scl, ecx.perm[slots.offset(phi as _)], ty)
        },
        _ => unreachable!()
    };
    ecx.data.values[id] = InsValue::from_value(value);
}

fn ins_cinit(ecx: &mut Ecx, id: InsId) {
    let emit = &mut *ecx.data;
    let (size, chunk) = emit.code[id].decode_CINIT();
    let func = &ecx.ir.funcs[chunk];
    let FuncKind::Chunk(chunk) = &func.kind else { unreachable!() };
    if !chunk.scl.is_dynamic() { /* NOP */ return }
    let dsinit = emit.fb.importsupp(&ecx.ir, SuppFunc::INIT);
    let tab = emit.fb.importdataref(chunk.dynslots.cast());
    let tab = emit.fb.dataptr(tab);
    let nret: usize = func.ret.into();
    // bitmap + one for each return
    let num = emit.fb.ins().iconst(irt2cl(Type::I32), (1 + nret) as i64);
    emit.fb.ins().call(dsinit, &[tab, num, emit.values[size].value()]);
}

fn ins_lop(ecx: &mut Ecx, id: InsId) -> compile::Result {
    let LangOp { lang, op } = ecx.data.code[id].decode_L();
    ecx.data.values[id] = Lang::from_u8(lang).emit(ecx, id, op)?;
    Ok(())
}

pub fn translate(ecx: &mut Ecx, id: InsId) -> compile::Result {
    use Opcode::*;
    let ins = ecx.data.code[id];
    // hack: translate boxes here
    if ins.type_() != Type::LSV || (BOX|ABOX).contains(ins.opcode()) {
        match ins.opcode() {
            NOP => { /* NOP */ },
            JMP => ins_jmp(ecx, id),
            GOTO => ins_goto(ecx, id),
            IF => ins_if(ecx, id),
            RET => ins_ret(ecx),
            TRET => todo!(),
            UB => ins_ub(ecx),
            ABORT => ins_abort(ecx),
            PHI => ins_phi(ecx, id),
            KINT | KINT64 => ins_kintx(ecx, id),
            KFP64 => ins_kfp64(ecx, id),
            KSTR => todo!(),
            KREF => { /* NOP */ },
            MOV | MOVB | MOVF => ins_mov(ecx, id),
            CONV => todo!(),
            ADD | SUB | MUL | DIV | UDIV => ins_arith(ecx, id),
            POW => ins_pow(ecx, id),
            ADDP => ins_addp(ecx, id),
            NEG => ins_neg(ecx, id),
            EQ | NE | LT | LE | ULT | ULE => ins_cmp(ecx, id),
            ALLOC => ins_alloc(ecx, id),
            STORE => ins_store(ecx, id),
            LOAD => ins_load(ecx, id),
            BOX => ins_box(ecx, id),
            ABOX => ins_abox(ecx, id),
            BREF => ins_bref(ecx, id),
            CALL => todo!(),
            CALLC | CALLCI => ins_callc(ecx, id),
            CARG => { /* NOP */ },
            RES => ins_res(ecx, id),
            CINIT => ins_cinit(ecx, id),
            LO | LOV | LOVV | LOVX | LOX | LOXX => ins_lop(ecx, id)?
        }
    }
    Ok(())
}
