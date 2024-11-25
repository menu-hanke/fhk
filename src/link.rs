//! Machine code linking.

use crate::compile::{self, Ccx, Phase};
use crate::image::Image;
use crate::mcode::{MCode, Reloc, Sym};
use crate::mmap::{mmap, Mmap};
use crate::trace::trace;
use crate::typestate::Absent;

#[derive(Default)]
pub struct Link;

unsafe fn doreloc(kind: cranelift_codegen::binemit::Reloc, at: *mut u8, what: *const u8) {
    use cranelift_codegen::binemit::Reloc::*;
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

fn link(mcode: &MCode) -> compile::Result<Mmap> {
    let code: &[u8] = mcode.code.as_slice();
    let data: &[u8] = mcode.data.bump().as_slice();
    // TODO this can really fail and should set an error insted of unwrapping
    let mut map = mmap(code.len() + data.len(), Mmap::READ | Mmap::WRITE).unwrap();
    let mem = map.as_mut_slice();
    mem[..code.len()].copy_from_slice(code);
    mem[code.len()..].copy_from_slice(data);
    let mem = mem.as_mut_ptr();
    for &Reloc { at, add, kind, sym, which } in &mcode.relocs {
        let base = match sym {
            Sym::Data => code.len() as u32 + which,
            Sym::Label => mcode.labels[zerocopy::transmute!(which as u16)]
        };
        unsafe {
            doreloc(
                kind,
                mem.add(at as _),
                mem.add(base as _).offset(add as _)
            )
        }
    }
    // protect data first so that any overlap is still executable
    map.protect(code.len()..code.len()+data.len(), Mmap::READ);
    map.protect(0..code.len(), Mmap::READ | Mmap::EXEC);
    trace!(
        LINK "code is at {:#x}..{:#x} ({} bytes)",
        map.base() as usize, map.base() as usize + code.len(), code.len(),
    );
    trace!(
        LINK "data is at {:#x}..{:#x} ({} bytes)",
        map.base() as usize + code.len(), map.base() as usize + code.len() + data.len(), data.len()
    );
    Ok(map)
}

impl Phase for Link {

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
            lang: Default::default(), // TODO
            breakpoints: ccx.layout.breakpoints,
            size: ccx.layout.size
        });
        Ok(())
    }

}
