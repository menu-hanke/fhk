//! Machine code & relocs.

use alloc::vec::Vec;

use crate::bump::{Bump, BumpRef};
use crate::index::{index, IndexVec};
use crate::intern::Intern;
use crate::ir::FuncId;

// cranelift uses:
//   x64        32
//   aarch64    32
//   riscv64     4
//   s390x       4
const FUNC_ALIGN: u32 = 32;

index!(pub struct Label(u16) invalid(!0));

pub type MCodeOffset = u32;

// marker for BumpRef in mcode.data
pub type MCodeData<T=[u8]> = BumpRef<T>;

#[derive(Clone, Copy)]
pub enum Sym {
    Data,   // which = offset from mcode.data
    Label,  // which = Label
}

pub struct Reloc {
    pub at: MCodeOffset,
    pub add: i32,
    pub kind: cranelift_codegen::binemit::Reloc,
    pub sym: Sym,
    pub which: u32
}

#[derive(Default)]
pub struct MCode {
    pub data: Intern,
    pub code: Bump,
    pub relocs: Vec<Reloc>,
    pub labels: IndexVec<Label, MCodeOffset>
}

impl Label {

    pub fn func(func: FuncId) -> Self {
        zerocopy::transmute!(func)
    }

}

impl Reloc {

    pub fn data(
        at: MCodeOffset,
        add: i32,
        kind: cranelift_codegen::binemit::Reloc,
        data: MCodeData
    ) -> Self {
        Self {
            at,
            add,
            kind,
            sym: Sym::Data,
            which: zerocopy::transmute!(data)
        }
    }

    pub fn code(
        at: MCodeOffset,
        add: i32,
        kind: cranelift_codegen::binemit::Reloc,
        label: Label
    ) -> Self {
        let label: u16 = zerocopy::transmute!(label);
        Self {
            at,
            add,
            kind,
            sym: Sym::Label,
            which: label as _
        }
    }

}

impl MCode {

    #[cfg(target_arch="x86_64")]
    pub fn align_code(&mut self) {
        let mut need = (-(self.code.end().offset() as isize) as usize) & (FUNC_ALIGN as usize - 1);
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

}
