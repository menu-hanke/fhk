//! IR -> Machine code pipeline.

use alloc::vec::Vec;
use cranelift_codegen::ir::condcodes::IntCC;
use cranelift_codegen::ir::{AbiParam, AliasRegion, ExtFuncData, ExternalName, FuncRef, GlobalValue, GlobalValueData, InstBuilder, InstInserterBase, MemFlags, Signature, UserExternalName, Value};
use cranelift_codegen::isa::{CallConv, OwnedTargetIsa};
use cranelift_codegen::settings::Configurable;
use cranelift_codegen::{FinalizedMachReloc, FinalizedRelocTarget};
use cranelift_entity::packed_option::ReservedValue;

use crate::bitmap::BitMatrix;
use crate::bump::{self, Aligned, Bump};
use crate::compile::{self, Ccx, Phase};
use crate::dump::{dump_mcode, dump_schedule};
use crate::index::{self, IndexSlice, IndexVec, InvalidValue};
use crate::ir::{Bundle, Func, FuncId, FuncKind, Ins, InsId, Opcode, PhiId, Query, Type, IR};
use crate::mcode::{Label, MCode, MCodeData, MCodeOffset, Reloc};
use crate::mem::{SizeClass, Slot};
use crate::schedule::{compute_schedule, BlockId, Gcm};
use crate::support::{emitsupport, SuppRef, SupportFuncs};
use crate::trace::trace;
use crate::translate::translate;
use crate::typestate::{Absent, R, RW};

// workaround for cranelift types which are newtypes over u32 but don't implement zerocopy traits:
pub unsafe trait CraneliftEntityRef32 {}
unsafe impl CraneliftEntityRef32 for Value {}

pub struct FuncBuilder {
    pub ctx: cranelift_codegen::Context,
    pub block: cranelift_codegen::ir::Block
}

pub type Values = IndexSlice<InsId, Value/*|cl::Block*/>;

pub struct Emit {
    pub isa: OwnedTargetIsa,
    pub fb: FuncBuilder,
    pub gcm: Gcm,
    pub supp: SupportFuncs,
    pub code: IndexVec<InsId, Ins>,
    pub values: IndexVec<InsId, Value/*|cl::Block*/>,
    pub blockparams: BitMatrix<BlockId, PhiId>,
    pub stack: Value,
    pub block: BlockId,
    pub fid: FuncId,
    pub idx: Value, // meaningful for bundle functions only
    // work arrays:
    pub tmp_val: Vec<Value>
}

pub type Ecx<'a> = Ccx<Emit, RW, R<'a>>;

// vmctx including dynamic memory
pub const MEM_VMCTX: MemFlags = MemFlags::trusted().with_alias_region(Some(AliasRegion::Vmctx));
// query result
pub const MEM_RESULT: MemFlags = MemFlags::trusted().with_alias_region(Some(AliasRegion::Table));

// this logic exists inside cranelift, but it's hidden too well behind a TargetIsa pointer.
// no thanks, this handles all relevant platforms.
// (could just consider writing all support functions as extern "sysv")
pub const NATIVE_CALLCONV: CallConv = {
    if cfg!(all(target_os="macos", target_arch="aarch64")) {
        CallConv::AppleAarch64
    } else if cfg!(windows) {
        CallConv::WindowsFastcall
    } else {
        CallConv::SystemV
    }
};

const NS_DATA: u32 = 0;
const NS_FUNC: u32 = 1;
const NS_SUPP: u32 = 2;

impl<'a> InstInserterBase<'a> for &'a mut FuncBuilder {
    fn data_flow_graph(&self) -> &cranelift_codegen::ir::DataFlowGraph {
        &self.ctx.func.dfg
    }
    fn data_flow_graph_mut(&mut self) -> &mut cranelift_codegen::ir::DataFlowGraph {
        &mut self.ctx.func.dfg
    }
    fn insert_built_inst(
        self,
        inst: cranelift_codegen::ir::Inst
    ) -> &'a mut cranelift_codegen::ir::DataFlowGraph {
        self.ctx.func.layout.append_inst(inst, self.block);
        &mut self.ctx.func.dfg
    }
}

impl FuncBuilder {

    pub fn ins(&mut self) -> cranelift_codegen::ir::InsertBuilder<'_, &mut FuncBuilder> {
        cranelift_codegen::ir::InsertBuilder::new(self)
    }

    pub fn newblock(&mut self) -> cranelift_codegen::ir::Block {
        let block = self.ctx.func.dfg.make_block();
        self.ctx.func.layout.append_block(block);
        block
    }

    pub fn vmctx(&mut self) -> Value {
        self.ins().get_pinned_reg(irt2cl(Type::PTR))
    }

    pub fn dataptr(&mut self, data: GlobalValue) -> Value {
        self.ins().global_value(irt2cl(Type::PTR), data)
    }

    pub fn kload(&mut self, type_: Type, ptr: Value) -> Value {
        self.ins().load(irt2cl(type_), MemFlags::trusted().with_readonly(), ptr, 0)
    }

    pub fn coerce(&mut self, v: Value, irt: Type) -> Value {
        use Type::*;
        use cranelift_codegen::ir::types;
        let vty = self.ctx.func.dfg.value_type(v);
        let tty = irt2cl(irt);
        if vty == tty {
            v
        } else {
            match (vty, irt) {
                (types::I8|types::I16|types::I32, I64)
                    | (types::I8|types::I16, I32)
                    | (types::I8, I16)
                    => self.ins().sextend(tty, v),
                (types::I8|types::I16|types::I32, PTR) => self.ins().uextend(tty, v),
                _ => todo!()
            }
        }
    }

}

fn makesig(signature: &mut Signature, func: &Func) {
    match func.kind {
        FuncKind::User() => todo!(),
        FuncKind::Query(_) => {
            // queries use sysv callconv even on windows so that fhk_vmcall doesn't need a
            // windows-specific version
            signature.call_conv = CallConv::SystemV;
            // must match fhk_vmcall
            signature.params.extend_from_slice(&[
                AbiParam::new(irt2cl(Type::I32)),
                AbiParam::new(irt2cl(Type::PTR))
            ]);
        },
        FuncKind::Bundle(Bundle { scl, .. }) => {
            signature.call_conv = CallConv::Fast;
            if scl != SizeClass::GLOBAL {
                signature.params.push(AbiParam::new(irt2cl(Type::I32)));
            }
        }
    }
}

fn funcref(func: FuncId) -> UserExternalName {
    let func: u16 = zerocopy::transmute!(func);
    UserExternalName::new(NS_FUNC, func as _)
}

fn dataref(data: MCodeData) -> UserExternalName {
    UserExternalName::new(NS_DATA, zerocopy::transmute!(data))
}

fn suppref(supp: SuppRef) -> UserExternalName {
    UserExternalName::new(NS_SUPP, zerocopy::transmute!(supp))
}

impl FuncBuilder {

    pub fn importdataref(&mut self, ptr: MCodeData) -> GlobalValue {
        let nameref = self.ctx.func.declare_imported_user_function(dataref(ptr.cast()));
        self.ctx.func.create_global_value(GlobalValueData::Symbol {
            name: ExternalName::user(nameref),
            offset: 0.into(),
            colocated: true,
            tls: false
        })
    }

    pub fn importdata<T>(&mut self, mcode: &mut MCode, value: &T) -> GlobalValue
        where T: ?Sized + Aligned + bump::IntoBytes
    {
        self.importdataref(mcode.data.intern(value).to_bump_sized(size_of_val(value)).cast())
    }

    pub fn importfunc(&mut self, ir: &IR, fid: FuncId) -> FuncRef {
        let mut sig = Signature::new(CallConv::Fast);
        makesig(&mut sig, &ir.funcs[fid]);
        let sig = self.ctx.func.import_signature(sig);
        let funcref = self.ctx.func.declare_imported_user_function(funcref(fid));
        self.ctx.func.import_function(ExtFuncData {
            name: ExternalName::user(funcref),
            signature: sig,
            colocated: true
        })
    }

    pub fn importsupp(&mut self, sf: &SupportFuncs, supp: SuppRef) -> FuncRef {
        let mut sig = Signature::new(CallConv::Fast);
        sf.signature(&mut sig, supp);
        let sig = self.ctx.func.import_signature(sig);
        let funcref = self.ctx.func.declare_imported_user_function(suppref(supp));
        self.ctx.func.import_function(ExtFuncData {
            name: ExternalName::User(funcref),
            signature: sig,
            colocated: true
        })
    }

}

pub fn irt2cl(irt: Type) -> cranelift_codegen::ir::Type {
    use Type::*;
    use cranelift_codegen::ir::types;
    match irt {
        PTR => types::I64,
        I8  => types::I8,
        I16 => types::I16,
        I32 => types::I32,
        I64 => types::I64,
        F32 => types::F32,
        F64 => types::F64,
        B1  => types::I8,
        FX|LSV => unreachable!()
    }
}

pub fn v2block(v: Value) -> BlockId {
    zerocopy::transmute!(v.as_u32() as u16)
}

pub fn block2cl(block: BlockId) -> cranelift_codegen::ir::Block {
    let block: u16 = zerocopy::transmute!(block);
    cranelift_codegen::ir::Block::from_u32(block as _)
}

fn slotptr(
    emit: &mut Emit,
    vmctx: Value,
    idx: Value,
    scl: SizeClass,
    slot: Slot,
    type_: Type
) -> Value {
    debug_assert!(type_ != Type::FX);
    debug_assert!(slot.bit() == 0 || type_ == Type::B1);
    let base = match scl.is_dynamic() {
        true => emit.fb.ins().load(irt2cl(Type::PTR), MEM_VMCTX, vmctx, slot.byte() as i32),
        false => emit.fb.ins().iadd_imm(vmctx, slot.byte() as i64)
    };
    let mut idx = emit.fb.coerce(idx, Type::I64);
    if type_.size() > 1 {
        idx = emit.fb.ins().imul_imm(idx, type_.size() as i64);
    }
    emit.fb.ins().iadd(base, idx)
}

pub fn loadslot(
    emit: &mut Emit,
    vmctx: Value,
    idx: Value,
    scl: SizeClass,
    slot: Slot,
    type_: Type
) -> Value {
    let ptr = slotptr(emit, vmctx, idx, scl, slot, type_);
    let mut value = emit.fb.ins().load(irt2cl(type_), MEM_VMCTX, ptr, 0);
    // TODO: B1 doesn't always need to be stored masked, only when colocated
    if type_ == Type::B1 {
        value = emit.fb.ins().band_imm(value, 1 << slot.bit());
        value = emit.fb.ins().icmp_imm(IntCC::NotEqual, value, 0);
    }
    value
}

pub fn storeslot(
    emit: &mut Emit,
    vmctx: Value,
    idx: Value,
    scl: SizeClass,
    slot: Slot,
    type_: Type,
    mut value: Value
) {
    let ptr = slotptr(emit, vmctx, idx, scl, slot, type_);
    if type_ == Type::B1 {
        let old = emit.fb.ins().load(irt2cl(Type::B1), MEM_VMCTX, ptr, 0);
        value = emit.fb.ins().ishl_imm(value, slot.bit() as i64);
        value = emit.fb.ins().bor(value, old);
    }
    emit.fb.ins().store(MEM_VMCTX, value, ptr, 0);
}

pub fn cast_entitrefs<T>(xs: &[u32]) -> &[T]
    where T: CraneliftEntityRef32
{
    unsafe { core::slice::from_raw_parts(xs as *const [u32] as *const u32 as *const T, xs.len()) }
}

pub fn collectargs(emit: &Emit, dest: &mut Bump<u32>, mut arg: InsId) {
    while emit.code[arg].opcode() != Opcode::KNOP {
        debug_assert!(emit.code[arg].opcode() == Opcode::CARG);
        let (ap, v) = emit.code[arg].decode_CARG();
        dest.push(emit.values[v].as_u32());
        arg = ap;
    }
}

fn trace_schedule(emit: &Emit, func: &Func, fid: FuncId) {
    trace!(
        "---------- FUNC {} ----------",
        {let fid: u16 = zerocopy::transmute!(fid); fid}
    );
    trace!("{}", {
        let mut tmp = Default::default();
        dump_schedule(&mut tmp, func, &emit.code, &emit.values, &emit.blockparams);
        tmp
    });
}

fn emithead(emit: &mut Emit, func: &Func) {
    match func.kind {
        FuncKind::User() => { /* NOP */ },
        FuncKind::Query(_) => {
            // vmctx
            emit.fb.ctx.func.dfg.append_block_param(block2cl(BlockId::START), irt2cl(Type::PTR));
            // optimizer is not allowed to remove query parameters, or add new ones:
            debug_assert!(emit.fb.ctx.func.dfg.block_params(block2cl(BlockId::START)).len() == 2);
        },
        FuncKind::Bundle(Bundle { check, scl, .. }) => {
            let entry = emit.fb.newblock();
            emit.fb.block = entry;
            let idx = match scl {
                SizeClass::GLOBAL => emit.fb.ins().iconst(irt2cl(Type::I32), 0),
                _ => {
                    emit.fb.ctx.func.dfg.append_block_param(entry, irt2cl(Type::I32));
                    emit.fb.ctx.func.dfg.block_params(entry)[0]
                }
            };
            emit.idx = idx;
            let vmctx = emit.fb.vmctx();
            let one = emit.fb.ins().iconst(irt2cl(Type::B1), 1);
            storeslot(emit, vmctx, idx, scl, check, Type::B1, one);
            let jarg = [idx];
            let jarg: &[Value] = match emit.blockparams[BlockId::START].is_empty() {
                true => &[],
                false => {
                    // entry block takes index (TODO: vector return pointers go here as well.)
                    &jarg
                }
            };
            emit.fb.ins().jump(block2cl(BlockId::START), jarg);
        }
    }
}

fn emitreloc(mcode: &mut MCode, emit: &Emit, base: MCodeOffset, reloc: &FinalizedMachReloc) {
    let &FinalizedMachReloc { offset, kind, ref target, addend } = reloc;
    match target {
        &FinalizedRelocTarget::Func(ofs) =>
            mcode.relocs.push(Reloc::code(
                    base + offset,
                    addend as i32 + ofs as i32,
                    kind,
                    Label::func(emit.fid)
            )),
        &FinalizedRelocTarget::ExternalName(ExternalName::User(name)) => {
            match emit.fb.ctx.func.params.user_named_funcs()[name] {
                UserExternalName { namespace: NS_DATA, index } =>
                    mcode.relocs.push(Reloc::data(
                            base + offset,
                            addend as i32,
                            kind,
                            zerocopy::transmute!(index))
                    ),
                UserExternalName { namespace: NS_FUNC, index } =>
                    mcode.relocs.push(Reloc::code(
                            base + offset,
                            addend as i32,
                            kind,
                            Label::func(zerocopy::transmute!(index as u16))
                    )),
                UserExternalName { namespace: NS_SUPP, index } =>
                    mcode.relocs.push(Reloc::code(
                            base + offset,
                            addend as i32,
                            kind,
                            emit.supp[{
                                let supp: SuppRef = zerocopy::transmute!(index);
                                supp
                            }].label
                    )),
                _ => unreachable!()
            }
        },
        &FinalizedRelocTarget::ExternalName(ExternalName::LibCall(libcall)) => {
            // TODO: patch it right here right now.
            todo!()
        },
        _ => unreachable!()
    }
}

fn compilefunc(emit: &mut Emit, mcode: &mut MCode) -> MCodeOffset {
    if trace!(CLIF) {
        trace!("{}", emit.fb.ctx.func.display());
    }
    let loc = mcode.code.end().offset() as MCodeOffset;
    emit.fb.ctx.compile(&*emit.isa, &mut Default::default()).unwrap();
    let code = emit.fb.ctx.compiled_code().unwrap();
    mcode.code.write(code.code_buffer());
    mcode.align_code();
    for reloc in code.buffer.relocs() {
        emitreloc(mcode, emit, loc, reloc);
    }
    if trace!(MCODE) {
        trace!("{}", {
            let mut buf = Default::default();
            dump_mcode(&mut buf, &mcode.code.as_slice()[loc as usize..]);
            // dump_mcode(&mut buf, code.code_buffer());
            buf
        });
    }
    loc
}

fn emitirfunc(ecx: &mut Ecx, fid: FuncId) -> compile::Result {
    let emit = &mut *ecx.data;
    emit.fid = fid;
    let func = &ecx.ir.funcs[fid];
    compute_schedule(
        &mut emit.gcm,
        func,
        &mut emit.code,
        &mut emit.values,
        &mut emit.blockparams
    );
    if trace!(SCHEDULE) {
        trace_schedule(emit, func, fid);
    }
    // TODO: sink RIGHT HERE
    emit.fb.ctx.clear();
    let clf = &mut emit.fb.ctx.func;
    makesig(&mut clf.signature, func);
    for (id, phis) in emit.blockparams.pairs() {
        let block = clf.dfg.make_block();
        debug_assert!(block.as_u32() as u16 == zerocopy::transmute!(id));
        for phi in phis {
            clf.dfg.append_block_param(block, irt2cl(func.phis.at(phi).type_));
        }
    }
    // this must go after the blocks are created, so that they get assigned matching ids,
    // but before they are added to the layout, so that emithead can add an entry block.
    emithead(emit, func);
    for id in index::iter_span(emit.blockparams.rows()) {
        emit.fb.ctx.func.layout.append_block(block2cl(id));
    }
    emit.fb.block = cranelift_codegen::ir::Block::from_u32(0);
    emit.block = BlockId::START;
    for id in index::iter_span(emit.code.end()) {
        translate(ecx, id)?;
        if ecx.data.code[id].opcode().is_control() {
            ecx.data.block += 1;
            let block: usize = ecx.data.block.into();
            ecx.data.fb.block = cranelift_codegen::ir::Block::from_u32(block as _);
        }
    }
    let loc = compilefunc(&mut ecx.data, &mut ecx.mcode);
    ecx.mcode.labels[Label::func(fid)] = loc;
    if let FuncKind::Query(Query { obj, .. }) = ecx.ir.funcs[fid].kind {
        ecx.objs[obj].mcode = loc;
    }
    Ok(())
}

fn emitsuppfunc(ecx: &mut Ecx, supp: SuppRef) {
    let emit = &mut *ecx.data;
    emit.fb.ctx.clear();
    emit.supp.signature(&mut emit.fb.ctx.func.signature, supp);
    let entry = emit.fb.newblock();
    // supp code uses this to get function args:
    debug_assert!(entry == block2cl(BlockId::START));
    for param in &emit.fb.ctx.func.stencil.signature.params {
        emit.fb.ctx.func.stencil.dfg.append_block_param(entry, param.value_type);
    }
    emit.fb.block = entry;
    emitsupport(ecx, supp);
    if trace!(CLIF) || trace!(MCODE) {
        trace!("---------- SUPP@{} ----------", supp.offset());
    }
    let loc = compilefunc(&mut ecx.data, &mut ecx.mcode);
    ecx.mcode.labels[ecx.data.supp[supp].label] = loc;
}

fn emitfuncs(ecx: &mut Ecx) -> compile::Result {
    debug_assert!(ecx.mcode.labels.is_empty());
    <MCodeOffset as zerocopy::FromZeros>::extend_vec_zeroed(&mut ecx.mcode.labels.raw,
        ecx.ir.funcs.raw.len()).unwrap();
    for id in index::iter_span(ecx.ir.funcs.end()) {
        emitirfunc(ecx, id)?;
    }
    while let Some(supp) = ecx.data.supp.work.pop_front() {
        emitsuppfunc(ecx, supp);
    }
    Ok(())
}

impl Phase for Emit {

    fn new(_: &mut Ccx<Absent>) -> compile::Result<Self> {
        let mut flag_builder = cranelift_codegen::settings::builder();
        flag_builder.set("enable_pinned_reg", "true").unwrap();
        flag_builder.set("opt_level", "speed").unwrap();
        flag_builder.set("unwind_info", "false").unwrap();
        let isa = cranelift_native::builder()
            .unwrap()
            .finish(cranelift_codegen::settings::Flags::new(flag_builder))
            .unwrap();
        Ok(Emit {
            isa,
            fb: FuncBuilder {
                ctx: cranelift_codegen::Context::new(),
                block: cranelift_codegen::ir::Block::reserved_value()
            },
            gcm: Default::default(),
            supp: Default::default(),
            code: Default::default(),
            values: Default::default(),
            blockparams: Default::default(),
            stack: Value::reserved_value(),
            idx: Value::reserved_value(),
            block: BlockId::INVALID.into(),
            fid: FuncId::INVALID.into(),
            tmp_val: Default::default()
        })
    }

    fn run(ccx: &mut Ccx<Self>) -> compile::Result {
        ccx.freeze_ir(emitfuncs)
    }

}
