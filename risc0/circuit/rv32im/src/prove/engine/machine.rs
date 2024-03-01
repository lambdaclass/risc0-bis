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

use std::cmp;
use std::sync::atomic::Ordering;

use anyhow::{anyhow, bail, Result};
use lazy_regex::{regex, Captures};
use risc0_zkp::{
    adapter::CircuitStepContext,
    field::{
        baby_bear::{BabyBearElem, Elem},
        Elem as _,
    },
    hal::cpu::SyncSlice,
};
use risc0_zkvm_platform::syscall::bigint;

use super::{
    argument::{BytesArgument, RamArgument},
    Quad,
};
use crate::prove::hal::cpp::{ParallelCircuitStepExecHandler, ParallelCircuitStepVerifyHandler};
use crate::{
    prove::emu::{
        addr::WordAddr,
        preflight::{PreflightCycle, PreflightStage, PreflightTrace},
    },
    CIRCUIT,
};

pub struct MachineContext {
    trace: PreflightTrace,

    // Tables for sorting arguments in proper order
    ram_arg: RamArgument,
    bytes_arg: BytesArgument,
}

impl MachineContext {
    pub fn new(steps: usize, trace: PreflightTrace) -> Self {
        Self {
            trace,
            ram_arg: RamArgument::new(steps),
            bytes_arg: BytesArgument::new(steps),
        }
    }

    pub fn is_parallel_safe(&self, cycle: usize) -> bool {
        let cur_cycle = self.get_cycle(cycle);
        let is_safe = cur_cycle.backs.is_some();
        // tracing::debug!("is_parallel_safe: {cycle} <= {is_safe}");
        is_safe
    }

    pub fn inject_backs(&self, steps: usize, cycle: usize, data: SyncSlice<BabyBearElem>) {
        let cur_cycle = self.get_cycle(cycle);
        if let Some(backs) = &cur_cycle.backs {
            // tracing::trace!("[{cycle}] inject_backs({backs:?})");
            for back in &backs.0 {
                data.set(back.idx * steps + cycle - back.back, back.value.into());
            }
        }
    }

    pub fn sort(&mut self, name: &str) {
        match name {
            "ram" => self.ram_arg.sort(),
            "bytes" => self.bytes_arg.sort(),
            _ => unimplemented!("Unknown argument type {name}"),
        };
    }

    pub fn step_exec(
        &self,
        steps: usize,
        cycle: usize,
        args: &[SyncSlice<BabyBearElem>],
    ) -> Result<BabyBearElem> {
        // let cur_cycle = self.get_cycle(cycle);
        // tracing::debug!("[{cycle}]: {:?}", cur_cycle);
        // if [10008, 10009, 10010].contains(&cycle) {
        //     let data = &args[2];
        //     let x108: u32 = data.get(108 * steps + cycle - 1).into();
        //     let x112: u32 = data.get(112 * steps + cycle - 1).into();
        //     let x115: u32 = data.get(115 * steps + cycle - 1).into();
        //     let x118: u32 = data.get(118 * steps + cycle - 1).into();
        //     let x192: u32 = data.get(192 * steps + cycle - 1).into();
        //     tracing::debug!("x108: 0x{x108:08x}, x112: 0x{x112:08x}, x115: 0x{x115:08x}, x118: 0x{x118:08x}, x192: 0x{x192:08x}");
        // }

        let ctx = CircuitStepContext { size: steps, cycle };
        CIRCUIT.par_step_exec(&ctx, self, args)
    }

    pub fn step_verify_mem(
        &mut self,
        steps: usize,
        cycle: usize,
        args: &[SyncSlice<BabyBearElem>],
    ) -> Result<BabyBearElem> {
        let ctx = CircuitStepContext { size: steps, cycle };
        CIRCUIT.par_step_verify_mem(&ctx, self, args)
    }

    pub fn step_verify_bytes(
        &mut self,
        steps: usize,
        cycle: usize,
        args: &[SyncSlice<BabyBearElem>],
    ) -> Result<BabyBearElem> {
        let ctx = CircuitStepContext { size: steps, cycle };
        CIRCUIT.par_step_verify_bytes(&ctx, self, args)
    }
}

impl ParallelCircuitStepExecHandler<Elem> for MachineContext {
    fn call(
        &self,
        cycle: usize,
        name: &str,
        extra: &str,
        args: &[Elem],
        outs: &mut [Elem],
    ) -> anyhow::Result<()> {
        // tracing::trace!("[{cycle}] call({name})");
        match name {
            "halt" => Ok(()),
            "trace" => Ok(()),
            "getMajor" => self.get_major(cycle, outs),
            "getMinor" => self.get_minor(cycle, outs),
            "divide" => self.divide(args, outs),
            "bigintQuotient" => self.bigint_quotient(args, outs),
            "pageInfo" => self.page_info(cycle, outs),
            "ramWrite" => self.ram_write(cycle, args),
            "ramRead" => self.ram_read(cycle, args, outs),
            "plonkWrite" => self.arg_write_exec(cycle, extra, args),
            "log" => self.log(extra, args),
            "syscallInit" => Ok(()),
            "syscallBody" => self.syscall_body(outs),
            "syscallFini" => self.syscall_fini(outs),
            _ => unimplemented!("Unsupported extern: {name}"),
        }
    }
}

impl ParallelCircuitStepVerifyHandler<Elem> for MachineContext {
    fn call(
        &mut self,
        cycle: usize,
        name: &str,
        extra: &str,
        args: &[Elem],
        outs: &mut [Elem],
    ) -> Result<()> {
        match name {
            "plonkWrite" => self.arg_write_verify(cycle, extra, args),
            "plonkRead" => self.arg_read_verify(cycle, extra, outs),
            _ => unimplemented!("Unsupported extern: {name}"),
        }
    }
}

impl MachineContext {
    fn arg_read_verify(&mut self, cycle: usize, name: &str, outs: &mut [Elem]) -> Result<()> {
        // tracing::debug!("[{cycle}] arg_read({name})");
        match name {
            "ram" => self.ram_arg.read(cycle, outs.try_into().unwrap()),
            "bytes" => self.bytes_arg.read(cycle, outs.try_into().unwrap()),
            _ => unimplemented!("Unknown argument type {name}"),
        }
        Ok(())
    }

    fn arg_write_verify(&mut self, cycle: usize, name: &str, args: &[Elem]) -> Result<()> {
        // tracing::debug!("[{cycle}] arg_write({name})");
        match name {
            "bytes" => self.bytes_arg.write(cycle, args.try_into().unwrap()),
            _ => unimplemented!("Unknown argument type {name}"),
        }
        Ok(())
    }

    fn arg_write_exec(&self, cycle: usize, name: &str, args: &[Elem]) -> Result<()> {
        // tracing::debug!("[{cycle}] arg_write({name})");
        match name {
            "ram" => self.ram_arg.write(cycle, args.try_into().unwrap()),
            _ => unimplemented!("Unknown argument type {name}"),
        }
        Ok(())
    }
}

impl MachineContext {
    fn get_stage_offset(&self, cycle: usize) -> (&PreflightStage, usize) {
        if cycle < self.trace.pre.cycles.len() {
            (&self.trace.pre, 0)
        } else {
            (&self.trace.body, self.trace.pre.cycles.len())
        }
    }

    fn get_cycle(&self, cycle: usize) -> &PreflightCycle {
        let (stage, offset) = self.get_stage_offset(cycle);
        &stage.cycles[cycle - offset]
    }

    fn get_major(&self, cycle: usize, outs: &mut [Elem]) -> Result<()> {
        let cur_cycle = self.get_cycle(cycle);
        let (major, _) = cur_cycle.mux.as_body()?;
        tracing::trace!("[{cycle}] get_major: {major:?}");
        outs[0] = major.as_u32().into();
        Ok(())
    }

    fn get_minor(&self, cycle: usize, outs: &mut [Elem]) -> Result<()> {
        let cur_cycle = self.get_cycle(cycle);
        let (_, minor) = cur_cycle.mux.as_body()?;
        tracing::trace!("[{cycle}] get_minor: {minor:?}");
        outs[0] = minor.into();
        Ok(())
    }

    fn ram_read(&self, cycle: usize, args: &[Elem], outs: &mut [Elem]) -> Result<()> {
        let addr: u32 = args[0].into();
        let op: u32 = args[1].into();

        let (stage, offset) = self.get_stage_offset(cycle);
        let cycle_idx = cycle - offset;
        let stage_cycles = stage.cycles.len();
        let cur_cycle = stage
            .cycles
            .get(cycle_idx)
            .ok_or_else(|| anyhow!("[{cycle}] Preflight trace truncated: {stage_cycles}"))?;

        let mem_idx = cur_cycle.mem_idx.load(Ordering::Relaxed);

        let txn = &stage.txns[mem_idx];
        let txn_cycle = txn.cycle + offset;
        if txn_cycle != cycle {
            bail!("[{cycle}] Mismatched memory txn cycle. {txn_cycle} != {cycle}, {cur_cycle:?}, {txn:?}",);
        }

        if txn.addr != WordAddr(addr) {
            bail!(
                "[{cycle}] Mismatched memory txn addr. {:?} != {:?}",
                txn.addr,
                WordAddr(addr)
            );
        }

        cur_cycle.mem_idx.store(mem_idx + 1, Ordering::Relaxed);

        tracing::trace!(
            "[{cycle}] {:?} ram_read(0x{addr:08x}, {op}): {txn:?}",
            cur_cycle.mux
        );
        Quad(outs[0], outs[1], outs[2], outs[3]) = txn.data.into();
        Ok(())
    }

    fn ram_write(&self, cycle: usize, args: &[Elem]) -> Result<()> {
        let addr: u32 = args[0].into();
        let data: u32 = Quad(args[1], args[2], args[3], args[4]).into();
        let op: u32 = args[5].into();
        tracing::trace!("[{cycle}] ram_write(0x{addr:08x}, 0x{data:08x}, {op})");
        Ok(())
    }

    fn page_info(&self, cycle: usize, outs: &mut [Elem]) -> Result<()> {
        let (stage, offset) = self.get_stage_offset(cycle);
        let cur_cycle = &stage.cycles[cycle - offset];
        let is_read = stage.extras[cur_cycle.extra_idx + 0];
        let page_idx = stage.extras[cur_cycle.extra_idx + 1];
        let is_done = stage.extras[cur_cycle.extra_idx + 2];
        // tracing::debug!("page_read: 0x{page_idx:05x}");
        (outs[0], outs[1], outs[2]) = (is_read.into(), page_idx.into(), is_done.into());
        Ok(())
    }

    fn divide(&self, args: &[Elem], outs: &mut [Elem]) -> Result<()> {
        let mut numer: u32 = Quad(args[0], args[1], args[2], args[3]).into();
        let mut denom: u32 = Quad(args[4], args[5], args[6], args[7]).into();
        let sign: u32 = args[8].into();
        // tracing::debug!("divide: [{sign}] {numer} / {denom}");
        let ones_comp = (sign == 2) as u32;
        let neg_numer = sign != 0 && (numer as i32) < 0;
        let neg_denom = sign == 1 && (denom as i32) < 0;
        if neg_numer {
            numer = (!numer).overflowing_add(1 - ones_comp).0;
        }
        if neg_denom {
            denom = (!denom).overflowing_add(1 - ones_comp).0;
        }
        let (mut quot, mut rem) = if denom == 0 {
            (0xffffffff, numer)
        } else {
            (numer / denom, numer % denom)
        };
        let quot_neg_out =
            (neg_numer as u32 ^ neg_denom as u32) - ((denom == 0) as u32 * neg_numer as u32);
        if quot_neg_out != 0 {
            quot = (!quot).overflowing_add(1 - ones_comp).0;
        }
        if neg_numer {
            rem = (!rem).overflowing_add(1 - ones_comp).0;
        }
        // tracing::debug!("  quot: {quot}, rem: {rem}");
        Quad(outs[0], outs[1], outs[2], outs[3]) = quot.into();
        Quad(outs[4], outs[5], outs[6], outs[7]) = rem.into();
        Ok(())
    }

    // Division of two positive byte-limbed bigints. a = q * b + r.
    //
    // Assumes a and b are both normalized with limbs in range [0, 255].
    // Returns q as an array of BabyBearElems. (Drops r).
    //     When the denominator is zero, returns zero to facilitate use of the
    //     BigInt modular multiply circuit as an unreduced "checked
    //     multiply" circuit.
    // Returns an error when:
    // * Input denominator b is 0.
    // * Input denominator b is less than 9 bits.
    // * Quotient result q is greater than [bigint::WIDTH_BYTES] limbs. This
    //   will occur if the numerator `a` is the result of a multiplication of
    //   values `x` and `y` such that `floor(x * y / b) >=
    //   2^bigint::WIDTH_BITS`. If x and/or y is less than b (i.e. the modulus
    //   in bigint modular multiply) this constrain will be satisfied.
    fn bigint_quotient(&self, args: &[Elem], outs: &mut [Elem]) -> Result<()> {
        let (a_elems, b_elems) = args.split_at(bigint::WIDTH_BYTES * 2);

        // This is a variant of school-book multiplication.
        // Reference the Handbook of Elliptic and Hyper-elliptic Cryptography alg.
        // 10.5.1

        // Setup working buffers of u64 elements. We use u64 values here because this
        // implementation does a lot of non-field opperations and so we need to take the
        // inputs out of Montgomery form.
        let mut a = [0u64; bigint::WIDTH_BYTES * 2 + 1];
        for (i, ai) in a_elems.iter().copied().enumerate() {
            a[i] = u64::from(ai)
        }
        let mut b = [0u64; bigint::WIDTH_BYTES + 1];
        for (i, bi) in b_elems.iter().copied().enumerate() {
            b[i] = u64::from(bi)
        }
        let mut q = [0u64; bigint::WIDTH_BYTES];

        // Verify that the inputs are well-formed as byte-limbed BigInts.
        // This would indicate a problem with the circuit, so we panic here.
        for ai in a.iter().copied() {
            if ai > 255 {
                panic!("bigint quotient: input a is not well-formed");
            }
        }
        for bi in b.iter().copied() {
            if bi > 255 {
                panic!("bigint quotient: input b is not well-formed");
            }
        }

        // Determine n, the width of the denominator, and check for divide by zero.
        let mut n = bigint::WIDTH_BYTES;
        while n > 0 && b[n - 1] == 0 {
            n -= 1;
        }
        if n == 0 {
            // Divide by zero is strictly undefined, but the BigInt multiplier circuit uses
            // a modulus of zero as a special case to support "checked multiply"
            // of up to 256-bits. Return zero here to facilitate this.
            outs.copy_from_slice(&[Elem::ZERO; bigint::WIDTH_BYTES]);
            return Ok(());
        }
        if n < 2 {
            // FIXME: This routine should be updated to lift this restriction.
            anyhow::bail!("bigint quotient: denominator must be at least 9 bits");
        }
        let m = a.len() - n - 1;

        // Shift (i.e. multiply by two) the inputs until the leading bit is 1.
        let mut shift_bits = 0u64;
        while (b[n - 1] & (0x80 >> shift_bits)) == 0 {
            shift_bits += 1;
        }
        let mut carry = 0u64;
        for x in b.iter_mut().take(n) {
            let tmp = (*x << shift_bits) + carry;
            *x = tmp & 0xFF;
            carry = tmp >> 8;
        }
        if carry != 0 {
            panic!("bigint quotient: final carry in input shift");
        }
        for i in 0..(a.len() - 1) {
            let tmp = (a[i] << shift_bits) + carry;
            a[i] = tmp & 0xFF;
            carry = tmp >> 8;
        }
        a[a.len() - 1] = carry;

        for i in (0..=m).rev() {
            // Approximate how many multiples of b can be subtracted. May overestimate by up
            // to one.
            let mut q_approx = cmp::min(((a[i + n] << 8) + a[i + n - 1]) / b[n - 1], 255);
            while (q_approx * ((b[n - 1] << 8) + b[n - 2]))
                > ((a[i + n] << 16) + (a[i + n - 1] << 8) + a[i + n - 2])
            {
                q_approx -= 1;
            }

            // Subtract from `a` multiples of the denominator.
            let mut borrow = 0u64;
            for j in 0..=n {
                let sub = q_approx * b[j] + borrow;
                if a[i + j] < (sub & 0xFF) {
                    a[i + j] += 0x100 - (sub & 0xFF);
                    borrow = (sub >> 8) + 1;
                } else {
                    a[i + j] -= sub & 0xFF;
                    borrow = sub >> 8;
                }
            }
            if borrow > 0 {
                // Oops, went negative. Add back one multiple of b.
                q_approx -= 1;
                let mut carry = 0u64;
                for j in 0..=n {
                    let tmp = a[i + j] + b[j] + carry;
                    a[i + j] = tmp & 0xFF;
                    carry = tmp >> 8;
                }
                // Adding back one multiple of b should go from negative back to positive.
                if borrow - carry != 0 {
                    panic!("bigint quotient: underflow in bigint division");
                }
            }

            if i < q.len() {
                q[i] = q_approx;
            } else if q_approx != 0 {
                anyhow::bail!("bigint quotient: quotient exceeds allowed size");
            }
        }

        // Write q into output array, converting back to field representation.
        let mut q_elems = [Elem::ZERO; bigint::WIDTH_BYTES];
        for i in 0..bigint::WIDTH_BYTES {
            q_elems[i] = q[i].into();
        }
        outs.copy_from_slice(&q_elems);
        Ok(())
    }

    fn log(&self, msg: &str, args: &[Elem]) -> Result<()> {
        // Don't bother to format it if we're not even logging.
        if tracing::level_filters::LevelFilter::current()
            .eq(&tracing::level_filters::LevelFilter::OFF)
        {
            return Ok(());
        }

        // "msg" is given to us in C++-style formatting, so interpret it.
        let re = regex!("%([0-9]*)([xudw%])");
        let mut args_left = args;
        let mut next_arg = || {
            if args_left.is_empty() {
                panic!("Log arg mismatch, msg {msg}");
            }
            let arg: u32 = args_left[0].into();
            args_left = &args_left[1..];
            arg
        };
        let formatted = re.replace_all(msg, |captures: &Captures| {
            let width = captures
                .get(1)
                .map_or(0, |x| x.as_str().parse::<usize>().unwrap_or(0));
            let format = captures.get(2).map_or("", |x| x.as_str());
            match format {
                "u" => format!("{:width$}", next_arg()),
                "x" => {
                    let width = width.saturating_sub(2);
                    format!("0x{:0width$x}", next_arg())
                }
                "d" => format!("{:width$}", next_arg() as i32),
                "%" => "%".to_string(),
                "w" => {
                    let nexts = [next_arg(), next_arg(), next_arg(), next_arg()];
                    if nexts.iter().all(|v| *v <= 255) {
                        format!(
                            "0x{:08X}",
                            nexts[0] | (nexts[1] << 8) | (nexts[2] << 16) | (nexts[3] << 24)
                        )
                    } else {
                        format!(
                            "0x{:X}, 0x{:X}, 0x{:X}, 0x{:X}",
                            nexts[0], nexts[1], nexts[2], nexts[3]
                        )
                    }
                }
                _ => panic!("Unhandled printf format specification '{format}'"),
            }
        });
        assert_eq!(
            args_left.len(),
            0,
            "Args missing formatting: {:?} in {msg}",
            args_left
        );
        tracing::trace!("{}", formatted); // here
        Ok(())
    }

    fn syscall_body(&self, _outs: &mut [Elem]) -> Result<()> {
        // Quad(outs[0], outs[1], outs[2], outs[3]) =
        //     self.syscall_out_data.pop_front().unwrap_or_default();
        // Ok(())
        todo!()
    }

    fn syscall_fini(&self, _outs: &mut [Elem]) -> Result<()> {
        // let syscall_out_regs = self
        //     .syscall_out_regs
        //     .pop_front()
        //     .ok_or(anyhow!("Invalid syscall records"))?;
        // tracing::trace!("syscall_fini: {:?}", syscall_out_regs);
        // Quad(outs[0], outs[1], outs[2], outs[3]) = syscall_out_regs.0.into();
        // Quad(outs[4], outs[5], outs[6], outs[7]) = syscall_out_regs.1.into();
        // Ok(())
        todo!()
    }
}
