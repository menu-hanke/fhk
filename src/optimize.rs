//! Optimizer entry point.

// TODO passes:
// * conditional constant propagation
// * remove unused parameters and return values
// * merge identical functions
// * merge functions with identical callers
// * outline instance-invariant code
// * loop optimizations: code motion, eliminate useless loops, fusion
// * load-store elimination and dead store elimination
// * remove loops without side effects

use enumset::{EnumSet, EnumSetType};

use crate::compile::{self, Ccx, Stage};
use crate::dump::dump_ir;
use crate::index;
use crate::ir::{FuncId, IR};
use crate::opt_fold::Fold;
use crate::opt_goto::OptGoto;
use crate::opt_inline::Inline;
use crate::opt_phi::OptPhi;
use crate::trace::trace;
use crate::typestate::{Absent, R};

const MAX_ITER: usize = 100; // TODO: make this configurable

#[derive(EnumSetType)]
pub enum OptFlag {
    FOLD,
    GOTO,
    INLINE,
    PHI
}

pub fn parse_optflags(flags: &[u8]) -> EnumSet<OptFlag> {
    use OptFlag::*;
    let mut oflg: EnumSet<OptFlag> = EnumSet::empty();
    for &f in flags {
        oflg.insert_all(match f {
            b'f' => FOLD.into(),
            b'g' => GOTO.into(),
            b'i' => INLINE.into(),
            b'p' => PHI.into(),
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
    fn new(ccx: &mut Ccx<Absent>) -> Self;
    fn run(ccx: &mut Ocx, fid: FuncId);
}

pub trait Pass: Sized {
    fn new(ccx: &mut Ccx<Absent>) -> Self;
    fn run(ccx: &mut Ocx);
}

// TODO: replace this with a sparse hash?
fn irsize(ir: &IR) -> usize {
    let size: usize =ir.funcs.raw.iter().map(|f| { let size: usize = f.code.end().into(); size }).sum();
    size + 37*ir.funcs.raw.len()
}

impl Stage for Optimize {

    fn new(ccx: &mut Ccx<Absent>) -> compile::Result<Self> {
        Ok(Self {
            fold: Fold::new(ccx),
            inline: Inline::new(ccx)
        })
    }

    fn run(ocx: &mut Ccx<Optimize>) -> compile::Result {
        let mut size = irsize(&ocx.ir);
        ocx.freeze_graph(|ocx| {
            for i in 0..MAX_ITER {
                for fid in index::iter_span(ocx.ir.funcs.end()) {
                    if ocx.flags.contains(OptFlag::FOLD) {
                        Fold::run(ocx, fid);
                    }
                    if ocx.flags.contains(OptFlag::PHI) {
                        OptPhi::run(ocx, fid);
                    }
                    if ocx.flags.contains(OptFlag::GOTO) {
                        OptGoto::run(ocx, fid);
                    }
                }
                if ocx.flags.contains(OptFlag::INLINE) {
                    Inline::run(ocx);
                }
                let newsize = irsize(&ocx.ir);
                if size == newsize {
                    trace!(OPTIMIZE "converged in {} iterations", i+1);
                    break
                } else {
                    trace!(OPTIMIZE "IR size {} -> {}", size, newsize);
                    if trace!(OPTIMIZE) && !ocx.flags.is_empty() {
                        let mut tmp = Default::default();
                        dump_ir(&mut tmp, &ocx.ir);
                        trace!("{}", core::str::from_utf8(tmp.as_slice()).unwrap());
                    }
                    size = newsize;
                }
            }
        });
        Ok(())
    }

}
