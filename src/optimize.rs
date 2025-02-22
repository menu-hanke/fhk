//! Optimizer entry point.

use enumset::EnumSetType;

use crate::compile::{self, Ccx, Stage};
use crate::dump::dump_ir;
use crate::index;
use crate::ir::FuncId;
use crate::opt_fold::Fold;
use crate::trace::trace;
use crate::typestate::{Absent, R};

#[derive(EnumSetType)]
pub enum OptFlag {
    Fold
}

pub struct Optimize {
    pub fold: Fold
}

pub type Ocx<'a> = Ccx<Optimize, R<'a>>;

pub trait FuncPass: Sized {
    fn new(ccx: &mut Ccx<Absent>) -> compile::Result<Self>;
    fn run(ccx: &mut Ocx, fid: FuncId) -> compile::Result;
}

impl Stage for Optimize {

    fn new(ccx: &mut Ccx<Absent>) -> compile::Result<Self> {
        Ok(Self {
            fold: Fold::new(ccx)?
        })
    }

    fn run(ocx: &mut Ccx<Optimize>) -> compile::Result {
        ocx.freeze_graph(|ocx| {
            if ocx.flags.contains(OptFlag::Fold) {
                for fid in index::iter_span(ocx.ir.funcs.end()) {
                    Fold::run(ocx, fid)?;
                }
            }
            if trace!(OPTIMIZE) {
                let mut tmp = Default::default();
                dump_ir(&mut tmp, &ocx.ir);
                trace!("{}", core::str::from_utf8(tmp.as_slice()).unwrap());
            }
            Ok(())
        })
    }

}
