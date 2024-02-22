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

pub mod exec;
mod pager;
pub mod preflight;
pub mod rv32im;

use risc0_binfmt::{MemoryImage, SystemState};
use risc0_zkp::{
    adapter::CircuitInfo as _,
    core::digest::DIGEST_WORDS,
    field::{baby_bear::Elem, Elem as _},
};
use risc0_zkvm_platform::WORD_SIZE;

use crate::CircuitImpl;

pub struct SyscallRecord {
    pub to_guest: Vec<u32>,
    pub regs: (u32, u32),
}

pub struct Segment {
    pub partial_image: MemoryImage,
    pub pre_state: SystemState,
    pub post_state: SystemState,
    pub syscalls: Vec<SyscallRecord>,
    pub insn_cycles: usize,
}

impl Segment {
    pub fn prepare_globals(&self) -> Vec<Elem> {
        let mut io = vec![Elem::INVALID; CircuitImpl::OUTPUT_SIZE];

        // initialize Input
        let mut offset = 0;
        for i in 0..DIGEST_WORDS * WORD_SIZE {
            io[offset + i] = Elem::ZERO;
        }
        offset += DIGEST_WORDS * WORD_SIZE;

        // initialize PC
        let pc_bytes = self.pre_state.pc.to_le_bytes();
        for i in 0..WORD_SIZE {
            io[offset + i] = (pc_bytes[i] as u32).into();
        }
        offset += WORD_SIZE;

        // initialize ImageID
        let merkle_root = self.pre_state.merkle_root.as_words();
        for i in 0..DIGEST_WORDS {
            let bytes = merkle_root[i].to_le_bytes();
            for j in 0..WORD_SIZE {
                io[offset + i * WORD_SIZE + j] = (bytes[j] as u32).into();
            }
        }

        io
    }
}
