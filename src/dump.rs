//! Textual dumps for debugging.

use core::fmt::Write;
use core::str;

use cfg_if::cfg_if;

use crate::bitmap::BitMatrix;
use crate::bump::Bump;
use crate::controlflow::BlockId;
use crate::emit::InsValue;
use crate::index::{self, IndexSlice};
use crate::intern::Intern;
use crate::ir::{Code, Func, FuncId, Ins, InsId, LangOp, Operand, PhiId, IR};
use crate::lang::Lang;
use crate::mem::{BreakpointId, Layout};
use crate::obj::{FieldType, ObjRef, Objects};
use crate::parser::{stringify, SequenceType};
use crate::trace::trace;

/* ---- Objects ------------------------------------------------------------- */

fn dump_field(
    buf: &mut Bump,
    intern: &Intern,
    fty: FieldType,
    value: u32
) {
    use FieldType::*;
    match fty {
        Lit  => write!(buf, "{}", value as i32).unwrap(),
        Ref if value == zerocopy::transmute!(ObjRef::NIL) => { buf.write(b"(nil)"); },
        Ref  => write!(buf, "{:?}", {let r: ObjRef = zerocopy::transmute!(value); r}).unwrap(),
        Name => stringify(
            buf,
            intern,
            intern.get_slice(zerocopy::transmute!(value)),
            SequenceType::Pattern // doesn't matter what is passed here, it doesn't have captures
        ),
        _ => unreachable!()
    }
}

fn dump_obj(
    buf: &mut Bump,
    intern: &Intern,
    objs: &Objects,
    idx: ObjRef
) {
    let obj = &objs[idx];
    let op = obj.operator();
    write!(buf, "{:?} {:-5}", idx, op.name()).unwrap();
    let raw = objs.get_raw(idx);
    let mut idx = 1;
    for (fty, name) in op.fields() {
        use FieldType::*;
        if fty == Spec {
            write!(buf, ".{}", obj.data).unwrap();
            continue;
        }
        write!(buf, " {}:", name).unwrap();
        if (Lit | Ref | Name).contains(fty) {
            dump_field(buf, intern, fty, raw[idx]);
            idx += 1;
            continue
        }
        // else: it's a vla
        let fty = match fty { VRef => Ref, _ => Lit };
        buf.push(b'[');
        while idx < raw.len() {
            dump_field(buf, intern, fty, raw[idx]);
            idx += 1;
            if idx < raw.len() { buf.push(b' '); }
        }
        buf.push(b']');
    }
    buf.push(b'\n');
}

pub fn dump_objs(
    buf: &mut Bump,
    intern: &Intern,
    objs: &Objects,
    start: ObjRef
) {
    if start == objs.end() { return }
    let mut idx = start;
    loop {
        dump_obj(buf, intern, objs, idx);
        let Some(i) = objs.next(idx) else { break };
        idx = i;
    }
}

pub fn trace_objs( sequences: &Intern, objs: &Objects, start: ObjRef) {
    if trace!() {
        let mut tmp = Default::default();
        dump_objs(&mut tmp, sequences, objs, start);
        trace!("{}", str::from_utf8(tmp.as_slice()).unwrap());
    }
}

/* ---- IR ------------------------------------------------------------------ */

fn dump_ins(buf: &mut Bump, id: InsId, ins: Ins, values: Option<&IndexSlice<InsId, InsValue>>) {
    let opcode = ins.opcode();
    write!(
        buf,
        "{}{:04} {:-3} {:-6}",
        match opcode.is_control() && values.is_none() { true => "->", false => "  " },
        {let i: u16 = zerocopy::transmute!(id); i},
        ins.type_().name(),
        opcode.name()
    ).unwrap();
    let mut raw: u64 = zerocopy::transmute!(ins);
    for &op in opcode.operands() {
        raw >>= 16;
        match op {
            Operand::X  => write!(buf, " {}", raw as i16),
            Operand::XX => { raw >>= 16; write!(buf, " {}", raw as i32) },
            Operand::L  => {
                let LangOp { lang, op } = zerocopy::transmute!(raw as u16);
                // TODO: also put opname here (add an opname() in trait language?)
                write!(buf, " {}.{}", Lang::from_u8(lang).name(), op)
            },
            Operand::V  => write!(buf, " {:?}", {let i: InsId = zerocopy::transmute!(raw as u16); i}),
            Operand::C  => {
                if let Some(values) = values {
                    let block: u16 = zerocopy::transmute!(values.raw[raw as u16 as usize].block());
                    write!(buf, " ->{}", block)
                } else {
                    write!(buf, " ->{:?}", {let i: InsId = zerocopy::transmute!(raw as u16); i})
                }
            },
            Operand::P  => write!(buf, " {:?}", {let p: PhiId = zerocopy::transmute!(raw as u16); p}),
            Operand::F  => write!(buf, " {:?}", {let f: FuncId = zerocopy::transmute!(raw as u16); f})
        }.unwrap()
    }
    buf.push(b'\n');
}

fn dump_code(buf: &mut Bump, code: &Code) {
    for id in index::iter_span(code.end()) {
        dump_ins(buf, id, code.at(id), None);
    }
}

fn dump_phi(buf: &mut Bump, func: &Func, phi: PhiId) {
    let raw: u16 = zerocopy::transmute!(phi);
    write!(buf, "[{} {}]", raw, func.phis.at(phi).type_.name()).unwrap();
}

fn dump_phis(buf: &mut Bump, func: &Func) {
    for idx in index::iter_span(func.phis.end()) {
        if idx > 0.into() { buf.push(b' '); }
        buf.push(if idx < func.ret { b'R' } else if idx < func.arg { b'A' } else { b'P' });
        dump_phi(buf, func, idx);
    }
    buf.push(b'\n');
}

pub fn dump_ir(buf: &mut Bump, ir: &IR) {
    for (id, func) in ir.funcs.pairs() {
        write!(
            buf,
            "---------- FUNC {} ----------\n",
            {let i: u16 = zerocopy::transmute!(id); i}
        ).unwrap();
        write!(buf, "ENTRY ->{:?}\n", func.entry).unwrap();
        dump_phis(buf, func);
        dump_code(buf, &func.code);
    }
}

pub fn dump_schedule(
    buf: &mut Bump,
    func: &Func,
    code: &IndexSlice<InsId, Ins>,
    values: &IndexSlice<InsId, InsValue>,
    params: &BitMatrix<BlockId, PhiId>
) {
    dump_phis(buf, func);
    let mut block: BlockId = 0.into();
    for (id, &ins) in code.pairs() {
        dump_ins(buf, id, ins, Some(values));
        if ins.opcode().is_control() && id+1 != code.end() {
            block += 1;
            write!(buf, "->{}", {let b: u16 = zerocopy::transmute!(block); b}).unwrap();
            for phi in &params[block] {
                buf.push(b' ');
                dump_phi(buf, func, phi);
            }
            buf.write(b":\n");
        }
    }
}

/* ---- Memory -------------------------------------------------------------- */

pub fn dump_layout(buf: &mut Bump, layout: &Layout) {
    let Some(end_reset) = layout.reset
        .pairs()
        .rev()
        .find_map(|(i,m)| (!m.is_empty()).then_some(i+1))
        else { return };
    write!(buf, "             ").unwrap();
    for i in index::iter_span(end_reset) {
        let i: u8 = zerocopy::transmute!(i);
        write!(buf, " {:02}", i).unwrap();
    }
    buf.push(b'\n');
    for breakpoint in index::iter_span(BreakpointId::MAXNUM.into()) {
        let this = layout.breakpoints[breakpoint];
        let next = layout.breakpoints[breakpoint+1];
        if next == 0 { break; }
        write!(buf, "{:4} .. {:4} ", this, next).unwrap();
        for i in index::iter_span(end_reset) {
            buf.write(match layout.reset[i].test(breakpoint) {
                true  => b" * ",
                false => b"   "
            });
        }
        buf.push(b'\n');
    }
}

/* ---- Machine code -------------------------------------------------------- */

#[cfg(all(target_arch="x86_64", feature="iced-x86"))]
mod x64 {
    use core::fmt::Write;
    use alloc::string::String;
    use iced_x86::{Decoder, FastFormatterOptions, Instruction, SpecializedFormatter, SpecializedFormatterTraitOptions};

    use crate::bump::Bump;

    struct FmtOptions;

    impl SpecializedFormatterTraitOptions for FmtOptions {
        fn space_after_operand_separator(_options: &FastFormatterOptions) -> bool { true }
        fn rip_relative_addresses(_options: &FastFormatterOptions) -> bool { true }
        fn uppercase_hex(_options: &FastFormatterOptions) -> bool { false }
        fn use_hex_prefix(_options: &FastFormatterOptions) -> bool { true }
    }

    fn disasm(buf: &mut String, code: &[u8]) {
        let mut decoder = Decoder::new(64, code, 0);
        let mut ins = Instruction::new();
        let mut fmt = SpecializedFormatter::<FmtOptions>::new();
        while decoder.can_decode() {
            decoder.decode_out(&mut ins);
            write!(buf, "{:04x} ", ins.ip()).unwrap();
            fmt.format(&ins, buf);
            buf.push('\n');
        }
    }

    pub fn dump_mcode(buf: &mut Bump, code: &[u8]) {
        let mut s = String::new();
        disasm(&mut s, code);
        buf.write(&*s);
    }
}

cfg_if! {
    if #[cfg(all(target_arch="x86_64", feature="iced-x86"))] {
        pub use x64::dump_mcode;
    } else {
        pub fn dump_mcode(_buf: &mut Bump, _code: &[u8]) {}
    }
}
