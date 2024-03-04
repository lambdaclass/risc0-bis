// Copyright 2024 RISC Zero, Inc.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

#![doc = include_str!("../README.md")]
#![cfg_attr(not(feature = "std"), no_std)]

pub mod control_id;
mod info;
pub mod layout;
pub mod poly_ext;
#[cfg(feature = "prove")]
pub mod prove;
mod taps;

use risc0_zkp::{
    adapter::{CircuitCoreDef, TapsProvider},
    field::baby_bear::BabyBear,
    taps::TapSet,
};

pub struct CircuitImpl;

pub const REGISTER_GROUP_ACCUM: usize = 0;
pub const REGISTER_GROUP_CODE: usize = 1;
pub const REGISTER_GROUP_CTRL: usize = 1;
pub const REGISTER_GROUP_DATA: usize = 2;

pub const GLOBAL_MIX: usize = 0;
pub const GLOBAL_OUT: usize = 1;
pub const CIRCUIT: CircuitImpl = CircuitImpl::new();

impl CircuitImpl {
    const fn new() -> Self {
        CircuitImpl
    }
}

impl TapsProvider for CircuitImpl {
    fn get_taps(&self) -> &'static TapSet<'static> {
        taps::TAPSET
    }
}

impl CircuitCoreDef<BabyBear> for CircuitImpl {}

#[cfg(test)]
mod tests {
    use risc0_core::field::baby_bear::BabyBearElem;
    use risc0_zkp::{
        adapter::{CircuitStep, CircuitStepContext, CircuitStepHandler},
        hal::cpu::CpuBuffer,
    };

    use super::CIRCUIT;

    struct CustomStepMock;

    impl CircuitStepHandler<BabyBearElem> for CustomStepMock {
        fn call(
            &mut self,
            _cycle: usize,
            name: &str,
            extra: &str,
            args: &[BabyBearElem],
            outs: &mut [BabyBearElem],
        ) -> anyhow::Result<()> {
            println!("name: {name}, extra: {extra}, args: {args:?}");
            outs[0] = BabyBearElem::new(2);
            Ok(())
        }

        fn sort(&mut self, _name: &str) {
            unimplemented!()
        }
    }

    #[test]
    fn step_exec() {
        let mut custom = CustomStepMock {};
        let ctx = CircuitStepContext { size: 0, cycle: 0 };
        let args0 = CpuBuffer::from_fn("args0", 20, |_| BabyBearElem::default());
        let args1 = CpuBuffer::from_fn("args1", 20, |_| BabyBearElem::default());
        let args2 = CpuBuffer::from_fn("args2", 20, |_| BabyBearElem::default());
        let args = [&args0, &args1, &args2].map(CpuBuffer::as_slice_sync);
        CIRCUIT
            .step_exec(&ctx, &mut custom, args.as_slice())
            .unwrap();
    }
}
