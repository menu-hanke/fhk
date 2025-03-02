//! Optimizer entry point.

// TODO passes:
// * eliminate constant phis
// * conditional constant propagation
// * remove unused parameters and return values
// * merge identical functions
// * merge functions with identical callers
// * outline instance-invariant code
// * loop optimizations: code motion, eliminate useless loops, fusion

use enumset::{EnumSet, EnumSetType};

use crate::compile::{self, Ccx, Stage};
use crate::dump::dump_ir;
use crate::index;
use crate::ir::FuncId;
use crate::opt_fold::Fold;
use crate::opt_inline::Inline;
use crate::trace::trace;
use crate::typestate::{Absent, R};

#[derive(EnumSetType)]
pub enum OptFlag {
    FOLD,
    INLINE
}

pub fn parse_optflags(flags: &[u8]) -> EnumSet<OptFlag> {
    use OptFlag::*;
    let mut oflg: EnumSet<OptFlag> = EnumSet::empty();
    for &f in flags {
        oflg.insert_all(match f {
            b'f' => FOLD.into(),
            b'i' => INLINE.into(),
            b'a' => EnumSet::all(),
            _ => continue
        });
    }
    oflg
}

pub struct Optimize {
    pub fold: Fold,
    pub inline: Inline
}

pub type Ocx<'a> = Ccx<Optimize, R<'a>>;

pub trait FuncPass: Sized {
    fn new(ccx: &mut Ccx<Absent>) -> compile::Result<Self>;
    fn run(ccx: &mut Ocx, fid: FuncId) -> compile::Result;
}

pub trait Pass: Sized {
    fn new(ccx: &mut Ccx<Absent>) -> compile::Result<Self>;
    fn run(ccx: &mut Ocx) -> compile::Result;
}

impl Stage for Optimize {

    fn new(ccx: &mut Ccx<Absent>) -> compile::Result<Self> {
        Ok(Self {
            fold: Fold::new(ccx)?,
            inline: Inline::new(ccx)?
        })
    }

    fn run(ocx: &mut Ccx<Optimize>) -> compile::Result {
        ocx.freeze_graph(|ocx| {
            if ocx.flags.contains(OptFlag::FOLD) {
                for fid in index::iter_span(ocx.ir.funcs.end()) {
                    Fold::run(ocx, fid)?;
                }
            }
            if ocx.flags.contains(OptFlag::INLINE) {
                Inline::run(ocx)?;
            }
            if trace!(OPTIMIZE) && !ocx.flags.is_empty() {
                let mut tmp = Default::default();
                dump_ir(&mut tmp, &ocx.ir);
                trace!("{}", core::str::from_utf8(tmp.as_slice()).unwrap());
            }
            Ok(())
        })
    }

}
