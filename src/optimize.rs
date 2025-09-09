//! Optimizer entry point.

// TODO passes:
// * conditional constant propagation
// * remove unused parameters and return values
// * merge identical functions
// * merge functions with identical callers
// * outline instance-invariant code
// * loop optimizations: code motion, fusion
// * merge identical phis
// * load-store elimination and dead store elimination
// * size class optimization: if CINITs have statically known size, set CINIT->NOP and scl->static

use core::hash::Hasher;

use enumset::{EnumSet, EnumSetType};
use rustc_hash::FxHasher;

use crate::compile::{self, Ccx, Stage};
use crate::controlflow::ControlFlow;
use crate::dump::dump_ir;
use crate::index::IndexSet;
use crate::{index, opt_control};
use crate::ir::{FuncId, PhiId, IR};
use crate::opt_fold::Fold;
use crate::opt_inline::Inline;
use crate::trace::trace;
use crate::typestate::{Absent, R};

const MAX_ITER: usize = 100; // TODO: make this configurable

#[derive(EnumSetType)]
pub enum OptFlag {
    CCP,
    FOLD,
    GOTO,
    INLINE,
    LOOP,
    PHI,
    SWITCH,
    IFCHAIN
}

pub fn parse_optflags(flags: &[u8]) -> EnumSet<OptFlag> {
    use OptFlag::*;
    let mut oflg: EnumSet<OptFlag> = EnumSet::empty();
    for &f in flags {
        oflg.insert_all(match f {
            b'c' => CCP.into(),
            b'f' => FOLD.into(),
            b'g' => GOTO.into(),
            b'i' => INLINE.into(),
            b'l' => LOOP.into(),
            b'p' => PHI.into(),
            b's' => SWITCH.into(),
            b'n' => IFCHAIN.into(),
            b'a' => EnumSet::all(),
            _ => continue
        });
    }
    if flags.get(0) == Some(&b'-') {
        oflg = oflg.complement();
    }
    oflg
}

// TODO: remove *Pass traits and derive default here
pub struct Optimize {
    pub fold: Fold,
    pub inline: Inline,
    pub cf: ControlFlow, // TODO: make opt_inline use this
    pub phi_mark: IndexSet<PhiId>
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

fn optimize(ocx: &mut Ocx) {
    use OptFlag::*;
    if ocx.flags.contains(INLINE) {
        Inline::run(ocx);
    }
    for fid in index::iter_span(ocx.ir.funcs.end()) {
        if !(ocx.flags & (SWITCH|LOOP|PHI|CCP|GOTO)).is_empty() {
            opt_control::run(ocx, fid);
        }
        if ocx.flags.contains(FOLD) {
            Fold::run(ocx, fid);
        }
    }
}

// TODO: replace this with a sparse hash?
fn irhash(ir: &mut IR) -> u64 {
    let mut hash = FxHasher::default();
    for func in &mut ir.funcs.raw {
        for &ins in &func.code.inner_mut().raw {
            hash.write_u64(zerocopy::transmute!(ins));
        }
    }
    hash.finish()
}

impl Stage for Optimize {

    fn new(ccx: &mut Ccx<Absent>) -> compile::Result<Self> {
        Ok(Self {
            fold: Fold::new(ccx),
            inline: Inline::new(ccx),
            cf: Default::default(),
            phi_mark: Default::default()
        })
    }

    fn run(ocx: &mut Ccx<Optimize>) -> compile::Result {
        let mut hash = irhash(&mut ocx.ir);
        ocx.freeze_graph(|ocx| {
            for i in 0..MAX_ITER {
                optimize(ocx);
                let newhash = irhash(&mut ocx.ir);
                if hash == newhash || newhash == 0 {
                    trace!(OPTIMIZE "converged in {} iterations", i+1);
                    break
                } else {
                    if trace!(OPTIMIZE) && !ocx.flags.is_empty() {
                        let mut tmp = Default::default();
                        dump_ir(&mut tmp, &ocx.ir, &ocx.intern, &ocx.objs);
                        trace!("{}", core::str::from_utf8(tmp.as_slice()).unwrap());
                    }
                    hash = newhash;
                }
            }
        });
        Ok(())
    }

}
