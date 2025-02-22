//! Optimizer entry point.

use crate::compile::{self, Ccx, Stage};
use crate::typestate::Absent;

#[derive(Default)]
pub struct Optimize {

}

impl Stage for Optimize {

    fn new(_: &mut Ccx<Absent>) -> compile::Result<Self> {
        Ok(Default::default())
    }

    fn run(_: &mut Ccx<Self>) -> compile::Result {
        Ok(())
    }

}
