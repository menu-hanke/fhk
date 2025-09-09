//! Machine code & relocs.

use alloc::vec::Vec;
use enumset::EnumSetType;
use hashbrown::hash_table::Entry;
use hashbrown::HashTable;

use crate::bump::{self, as_bytes, Bump};
use crate::compile;
use crate::hash::fxhash;
use crate::index::{index, IndexVec};
use crate::mmap::{Mmap, Prot};
use crate::support::NativeFunc;
use crate::trace::trace;

// cranelift uses:
//   x64        32
//   aarch64    32
//   riscv64     4
//   s390x       4
const FUNC_ALIGN: u32 = 32;

index!(pub struct Label(u32) invalid(!0) debug("L{}"));

pub type MCodeOffset = u32;

// FIXME this only derives EnumSetType for VARIANT_COUNT
// remove this when (if) core::mem::variant_count stabilizes
#[derive(EnumSetType)]
pub enum Sym {
    Data,   // which = offset from mcode.data
    Label,  // which = Label
    Native, // which = NativeFunc
}

#[derive(Clone, Copy)]
pub enum Segment {
    Code,
    Data
}

pub struct Reloc {
    pub at: MCodeOffset,
    pub add: i32,
    pub kind: cranelift_codegen::binemit::Reloc,
    pub sym: Sym,
    pub seg: Segment,
    pub which: u32
}

// this implements its own interning because intern::Intern stores the sequence lengths inline.
// unlike intern::Intern, we don't need a `handle -> data` operation, so we can put the lengths
// in a separate table.
#[derive(Default)]
pub struct MCode {
    data: Bump,
    code: Bump,
    data_tab: HashTable<(/*offset:*/MCodeOffset, /*len:*/MCodeOffset)>,
    pub relocs: Vec<Reloc>,
    pub labels: IndexVec<Label, MCodeOffset>,
}

impl Sym {

    pub fn from_u8(raw: u8) -> Self {
        // FIXME replace with core::mem::variant_count when it stabilizes
        assert!(raw < <Self as enumset::__internal::EnumSetTypePrivate>::VARIANT_COUNT as _);
        unsafe { core::mem::transmute(raw) }
    }

}

impl Reloc {

    pub fn data_abs8(at: MCodeOffset, which: MCodeOffset) -> Reloc {
        Reloc {
            at,
            add: 0,
            kind: cranelift_codegen::binemit::Reloc::Abs8,
            sym: Sym::Data,
            seg: Segment::Data,
            which
        }
    }

}


impl MCode {

    #[cfg(target_arch="x86_64")]
    pub fn align_code(&mut self) {
        let mut need = (-(self.code.end().ptr() as isize) as usize) & (FUNC_ALIGN as usize - 1);
        loop {
            // NOP encodings yoinked from cranelift
            match need {
                0 => {},
                1 => { self.code.push::<[u8; 1]>([0x90]); },
                2 => { self.code.push::<[u8; 2]>([0x66,0x90]); },
                3 => { self.code.push::<[u8; 3]>([0x0F,0x1F,0x00]); },
                4 => { self.code.push::<[u8; 4]>([0x0F,0x1F,0x40,0x00]); },
                5 => { self.code.push::<[u8; 5]>([0x0F,0x1F,0x44,0x00,0x00]); },
                6 => { self.code.push::<[u8; 6]>([0x66,0x0F,0x1F,0x44,0x00,0x00]); },
                7 => { self.code.push::<[u8; 7]>([0x0F,0x1F,0x80,0x00,0x00,0x00,0x00]); },
                8 => { self.code.push::<[u8; 8]>([0x0F,0x1F,0x84,0x00,0x00,0x00,0x00,0x00]); },
                _ => { self.code.push::<[u8; 9]>([0x66,0x0F,0x1F,0x84,0x00,0x00,0x00,0x00,0x00]);
                       need -= 9; continue; }
            }
            break;
        }
    }

    #[cfg(not(target_arch="x86_64"))]
    pub fn align_code(&mut self) {
        // TODO insert nops
        self.code.align(FUNC_ALIGN);
    }

    pub fn write_code(&mut self, code: &[u8]) -> MCodeOffset {
        self.code.write(code).ptr() as _
    }

    pub fn code(&self) -> &[u8] {
        self.code.as_slice()
    }

    fn intern_data_bytes(&mut self, bytes: &[u8], align: usize) -> MCodeOffset {
        let data: &[u8] = self.data.as_slice();
        match self.data_tab.entry(
            fxhash(bytes),
            |&(ofs,len)| &data[ofs as usize..(ofs+len) as usize] == bytes
                && (ofs as usize) & (align-1) == 0,
            |&(ofs,len)| fxhash(&data[ofs as usize..(ofs+len) as usize])
        ) {
            Entry::Occupied(e) => e.get().0,
            Entry::Vacant(e) => {
                self.data.align(align);
                let ofs = self.data.write(bytes).ptr();
                e.insert((ofs as _, bytes.len() as _));
                ofs as _
            }
        }
    }

    pub fn intern_data<T>(&mut self, data: &T) -> MCodeOffset
        where T: ?Sized + bump::Aligned + bump::IntoBytes
    {
        self.intern_data_bytes(as_bytes(data), T::ALIGN)
    }

    pub fn write_data<T>(&mut self, data: &T) -> MCodeOffset
        where T: ?Sized + bump::Aligned + bump::IntoBytes
    {
        self.data.write(data).ptr() as _
    }

    pub fn reserve_data<T>(&mut self, len: usize) -> (MCodeOffset, &mut [T])
        where T: bump::FromBytes + bump::IntoBytes
    {
        let (p, r) = self.data.reserve_dst(len);
        (p.ptr() as _, r)
    }

    pub fn align_data(&mut self, align: usize) -> MCodeOffset {
        self.data.align(align);
        self.data.end().ptr() as _
    }

    pub fn align_data_for<T>(&mut self) -> MCodeOffset
        where T: ?Sized + bump::Aligned
    {
        self.align_data(T::ALIGN)
    }

    pub fn data(&self) -> &[u8] {
        self.data.as_slice()
    }

}

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

impl MCode {

    pub fn link(&self) -> compile::Result<Mmap> {
        link(self)
    }

}
