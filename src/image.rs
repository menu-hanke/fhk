//! Image definition and building.

use core::marker::PhantomPinned;
use core::mem::take;

use crate::bump::Bump;
use crate::compile;
use crate::finalize::{FinalizerBuilder, Finalizers};
use crate::host::HostInst;
use crate::index::{index, IndexArray};
use crate::mcode::{MCode, MCodeOffset};
use crate::mem::Offset;
use crate::mmap::Mmap;

index!(pub struct BreakpointId(u8));

impl BreakpointId {
    pub const MAXNUM: usize = 64;
}

pub struct Image {
    pub mem: Mmap,
    pub breakpoints: IndexArray<BreakpointId, Offset, {BreakpointId::MAXNUM+1}>,
    pub fin: Finalizers,
    pub size: Offset
}

#[derive(Default)]
pub struct ImageBuilder {
    pub mcode: MCode,
    pub breakpoints: IndexArray<BreakpointId, Offset, {BreakpointId::MAXNUM+1}>,
    pub fin: FinalizerBuilder,
    pub size: Offset
}

// note: the repr align is redundant here, but (regardless of fields), the compiled code expects
// this to be aligned to 8.
#[repr(align(8))]
pub struct Instance {
    pub host: HostInst,
    pub dup: Offset, // allocations to duplicate when continuing from this state
    pub sp: *mut u8, // stack pointer just before entering query
    _pin: PhantomPinned
}

impl ImageBuilder {

    // TODO: when string creation is implemented, also put the string in the imagebuilder
    // perfect hash table.
    pub fn intern_string(&mut self, data: &[u8], work: &mut Bump) -> MCodeOffset {
        let base = work.end();
        work.push((data.len() as u32).to_ne_bytes());
        work.write(data);
        if data.last() != Some(&0) {
            work.push(0u8);
        }
        let ofs = self.mcode.intern_data(&work[base..]);
        work.truncate(base);
        ofs + 4
    }

    pub fn build(&mut self) -> compile::Result<Image> {
        self.mcode.align_code();
        let mem = self.mcode.link()?;
        Ok(Image {
            mem,
            fin: take(&mut self.fin).build(),
            breakpoints: self.breakpoints,
            size: self.size
        })
    }

}
