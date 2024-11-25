//! Optimizer entry point.

use crate::compile::{self, Ccx, Phase};
use crate::typestate::Absent;

#[derive(Default)]
pub struct Optimize {

}

impl Phase for Optimize {

    fn new(_: &mut Ccx<Absent>) -> compile::Result<Self> {
        Ok(Default::default())
    }

    fn run(_: &mut Ccx<Self>) -> compile::Result {
        Ok(())
    }

}
