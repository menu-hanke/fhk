//! Machine code linking.

use core::mem::take;

use crate::compile::{self, Ccx, Stage};
use crate::image::Image;
use crate::mcode::{MCode, Reloc, Segment, Sym};
use crate::mmap::{Mmap, Prot};
use crate::support::NativeFunc;
use crate::trace::trace;
use crate::typestate::Absent;

#[derive(Default)]
pub struct Link;

unsafe fn doreloc(kind: cranelift_codegen::binemit::Reloc, at: *mut u8, what: *const u8) {
    use cranelift_codegen::binemit::Reloc::*;
    unsafe {
        match kind {
            Abs4 => at.cast::<u32>().write_unaligned(what as _),
            Abs8 => at.cast::<u64>().write_unaligned(what as _),
            X86PCRel4 | X86CallPCRel4 =>
                at.cast::<i32>().write_unaligned((what as isize - at as isize).try_into().unwrap()),
            S390xPCRel32Dbl | S390xPLTRel32Dbl => at.cast::<i32>().write_unaligned(
                (((what as isize) - (at as isize)) >> 1).try_into().unwrap()),
            Arm64Call => at.cast::<u32>().write_unaligned(
                    at.cast::<u32>().read_unaligned()
                    | ((((what as isize) - (at as isize)) >> 2) as u32 & 0x03ffffff)),
            RiscvCallPlt => todo!(), // can't be bothered right now
            _ => unimplemented!() // don't need
        }
    }
}

fn link(mcode: &MCode) -> compile::Result<Mmap> {
    let code = mcode.code();
    let data = mcode.data();
    // TODO this can really fail and should set an error insted of unwrapping
    let mut map = Mmap::new(code.len() + data.len(), Prot::Read | Prot::Write).unwrap();
    let mem = map.as_mut_slice();
    mem[..code.len()].copy_from_slice(code);
    mem[code.len()..].copy_from_slice(data);
    let mem = mem.as_mut_ptr();
    for &Reloc { at, seg, add, kind, sym, which } in &mcode.relocs {
        let loc = match seg {
            Segment::Code => mem,
            Segment::Data => unsafe { mem.add(code.len()) }
        };
        let base = match sym {
            Sym::Data   => unsafe { mem.add(code.len() + which as usize) },
            Sym::Label  => unsafe { mem.add(mcode.labels[zerocopy::transmute!(which)] as usize) },
            Sym::Native => NativeFunc::from_u8(which as _).ptr().cast()
        };
        unsafe { doreloc(kind, loc.add(at as _), base.offset(add as _)) }
    }
    // protect data first so that any overlap is still executable
    map.protect(code.len()..code.len()+data.len(), Prot::Read.into());
    map.protect(0..code.len(), Prot::Read | Prot::Exec);
    trace!(
        LINK "code is at {:#x}..{:#x} ({} bytes)",
        map.base() as usize, map.base() as usize + code.len(), code.len(),
    );
    trace!(
        LINK "data is at {:#x}..{:#x} ({} bytes)",
        map.base() as usize + code.len(), map.base() as usize + code.len() + data.len(), data.len()
    );
    if trace!(LINK) {
        // TODO: move disassembly here too
        for (label, &ofs) in mcode.labels.pairs() {
            trace!(LINK "{:?} {:?}", unsafe { mem.add(ofs as _) }, label);
        }
    }
    Ok(map)
}

impl Stage for Link {

    fn new(_: &mut Ccx<Absent>) -> compile::Result<Self> {
        Ok(Default::default())
    }

    fn run(ccx: &mut Ccx<Self>) -> compile::Result {
        // ensure start of data ( = end of code) is aligned
        // put code first so that final label addresses can be calculated from map base.
        ccx.mcode.align_code();
        let mem = link(&ccx.mcode)?;
        ccx.image = Some(Image {
            mem,
            fin: take(&mut ccx.fin).build(),
            breakpoints: ccx.layout.breakpoints,
            size: ccx.layout.size
        });
        Ok(())
    }

}
