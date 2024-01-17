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

use std::{
    fmt,
    sync::{Arc, RwLock},
};

use risc0_zkvm::{ExecutorEnv, InnerReceipt, Receipt};
use tokio::sync::mpsc;

use crate::{error::Error, state::BonsaiState};

#[derive(Debug, Clone)]
pub(crate) struct Task {
    pub session_id: String,
    pub image_id: String,
    pub input_id: String,
    pub assumptions: Vec<String>,
}

#[derive(Debug)]
pub(crate) enum ProverMessage {
    #[cfg(not(feature = "prove"))]
    RunSession(Task),
    #[cfg(feature = "prove")]
    RunSnark(Task),
}

impl fmt::Display for ProverMessage {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            #[cfg(not(feature = "prove"))]
            ProverMessage::RunSession(task) => {
                write!(f, "ProverMessage::RunSession: {{ task: {:?} }}", task)
            }
            #[cfg(feature = "prove")]
            ProverMessage::RunSnark(task) => {
                write!(f, "ProverMessage::RunSnark: {{ task: {:?} }}", task)
            }
        }
    }
}

#[derive(Clone)]
pub(crate) struct ProverHandle {
    pub sender: mpsc::Sender<ProverMessage>,
}

impl ProverHandle {
    pub(crate) async fn execute(&self, task: Task) {
        #[cfg(not(feature = "prove"))]
        let msg = ProverMessage::RunSession(task);
        #[cfg(feature = "prove")]
        let msg = ProverMessage::RunSnark(task);

        if (self.sender.send(msg).await).is_err() {
            tracing::info!("receiver dropped");
            assert!(self.sender.is_closed());
        }
    }
}

pub(crate) struct Prover {
    pub(crate) receiver: mpsc::Receiver<ProverMessage>,
    pub(crate) storage: Arc<RwLock<BonsaiState>>,
}

impl Prover {
    pub(crate) fn new(
        receiver: mpsc::Receiver<ProverMessage>,
        storage: Arc<RwLock<BonsaiState>>,
    ) -> Self {
        Prover { receiver, storage }
    }

    pub async fn handle_message(&mut self, msg: &ProverMessage) -> Result<(), Error> {
        match msg {
            #[cfg(not(feature = "prove"))]
            ProverMessage::RunSession(task) => {
                use anyhow::Context;
                use risc0_zkvm::{default_executor, sha::Digest, MaybePruned, ReceiptClaim};
                tracing::info!("Running task...");
                let image = self.get_image(task).await?;
                let input = self.get_input(task).await?;
                let receipts = self.get_receipts(task).await?;
                let elf = image.as_slice();

                let mut env = ExecutorEnv::builder();
                for receipt in receipts {
                    if receipt.len() < 1 {
                        continue;
                    }
                    let deserialized_receipt: Receipt = bincode::deserialize(&receipt)?;
                    env.add_assumption(deserialized_receipt);
                }

                let env = env
                    .write_slice(&input)
                    .session_limit(None)
                    .segment_limit_po2(20)
                    .build()
                    .map_err(|e| {
                        anyhow::anyhow!("failed to build executor environment: {:?}", e)
                    })?;
                let exec = default_executor();
                let session = exec
                    .execute(env, elf)
                    .context("Executor failed to generate a successful session")?;

                let receipt = Receipt {
                    inner: InnerReceipt::Fake {
                        claim: ReceiptClaim {
                            pre: MaybePruned::Pruned(Digest::ZERO),
                            post: MaybePruned::Pruned(Digest::ZERO),
                            exit_code: session.exit_code,
                            input: Digest::ZERO,
                            output: None.into(),
                        },
                    },
                    journal: session.journal,
                };
                let receipt_bytes = bincode::serialize(&receipt)?;
                self.storage
                    .write()?
                    .put_receipt(task.session_id.clone(), receipt_bytes);
                self.storage
                    .write()?
                    .put_session(task.session_id.clone(), "SUCCEEDED".to_string());
            }
            #[cfg(feature = "prove")]
            ProverMessage::RunSnark(task) => {
                use risc0_zkvm::{
                    get_prover_server,
                    recursion::{identity_p254, join, lift},
                    ExecutorImpl, ProverOpts, VerifierContext,
                };
                use std::{fs::File, io::Cursor, path::Path, process::Command};
                use tempfile::tempdir;

                tracing::info!("Running task...");
                let image = self.get_image(task).await?;
                let input = self.get_input(task).await?;
                let receipts = self.get_receipts(task).await?;
                let elf = image.as_slice();

                let mut env = ExecutorEnv::builder();
                for receipt in receipts {
                    if receipt.len() < 1 {
                        continue;
                    }
                    let deserialized_receipt: Receipt = bincode::deserialize(&receipt)?;
                    env.add_assumption(deserialized_receipt);
                }

                let env = env
                    .write_slice(&input)
                    .session_limit(None)
                    .segment_limit_po2(20)
                    .build()
                    .map_err(|e| {
                        anyhow::anyhow!("failed to build executor environment: {:?}", e)
                    })?;

                let tmp_dir = tempdir().expect("Failed to create tmpdir");
                let work_dir = std::env::var("RISC0_WORK_DIR");
                let work_dir = work_dir
                    .as_ref()
                    .map(|x| Path::new(x))
                    .unwrap_or(tmp_dir.path());

                let mut exec = ExecutorImpl::from_elf(env, elf).unwrap();
                let session = exec.run().unwrap();
                let segments = session.resolve().unwrap();

                let opts = ProverOpts::default();
                let ctx = VerifierContext::default();
                let prover = get_prover_server(&opts).unwrap();
                let segment_receipt = prover.prove_segment(&ctx, &segments[0]).unwrap();
                let mut rollup = lift(&segment_receipt).unwrap();

                for segment in &segments[1..] {
                    let segment_receipt = prover.prove_segment(&ctx, &segment).unwrap();
                    let rec_receipt = lift(&segment_receipt).unwrap();
                    rollup = join(&rollup, &rec_receipt).unwrap();
                    rollup.verify_integrity().unwrap();
                }

                let ident_receipt = identity_p254(&rollup).unwrap();
                let seal_bytes = ident_receipt.get_seal_bytes();

                std::fs::write(work_dir.join("seal.r0"), &seal_bytes).unwrap();

                let journal = session.journal.unwrap().bytes;
                let succinct_receipt =
                    Receipt::new(InnerReceipt::Succinct(ident_receipt), journal.clone());

                let seal_path = work_dir.join("input.json");
                let snark_path = work_dir.join("output.json");
                let seal_json = File::create(&seal_path).unwrap();
                let mut seal_reader = Cursor::new(&seal_bytes);
                risc0_seal_to_json::to_json(&mut seal_reader, &seal_json).unwrap();

                let status = Command::new("docker")
                    .arg("run")
                    .arg("--rm")
                    .arg("-v")
                    .arg(&format!("{}:/mnt", work_dir.to_string_lossy()))
                    .arg("risc0-groth16-prover")
                    .status()
                    .unwrap();
                if !status.success() {
                    panic!("docker returned failure exit code: {:?}", status.code());
                }

                let snark_str = std::fs::read_to_string(snark_path).unwrap();
                let snark_str = format!("[{snark_str}]"); // make the output valid json
                let raw_proof: (Vec<String>, Vec<Vec<String>>, Vec<String>, Vec<String>) =
                    serde_json::from_str(&snark_str).unwrap();

                let a: Result<Vec<Vec<u8>>, hex::FromHexError> = raw_proof
                    .0
                    .into_iter()
                    .map(|x| hex::decode(&x[2..]))
                    .collect();
                let a = a.expect("Failed to decode snark 'a' values");

                let b: Result<Vec<Vec<Vec<u8>>>, hex::FromHexError> = raw_proof
                    .1
                    .into_iter()
                    .map(|inner| {
                        inner
                            .into_iter()
                            .map(|x| hex::decode(&x[2..]))
                            .collect::<Result<Vec<Vec<u8>>, hex::FromHexError>>()
                    })
                    .collect();
                let b = b.expect("Failed to decode snark 'b' values");

                let c: Result<Vec<Vec<u8>>, hex::FromHexError> = raw_proof
                    .2
                    .into_iter()
                    .map(|x| hex::decode(&x[2..]))
                    .collect();
                let c = c.expect("Failed to decode snark 'c' values");

                let groth16_seal = risc0_zkvm::Groth16Seal { a, b, c };
                let receipt = Receipt::new(
                    InnerReceipt::Groth16(risc0_zkvm::Groth16Receipt {
                        seal: groth16_seal.to_vec(),
                        claim: succinct_receipt.get_claim().unwrap(),
                    }),
                    journal,
                );

                let receipt_bytes = bincode::serialize(&receipt)?;
                self.storage
                    .write()?
                    .put_receipt(task.session_id.clone(), receipt_bytes);
                self.storage
                    .write()?
                    .put_session(task.session_id.clone(), "SUCCEEDED".to_string());
            }
        }

        Ok(())
    }

    pub(crate) async fn run(&mut self) -> Result<(), Error> {
        while let Some(msg) = self.receiver.recv().await {
            tracing::info!("Receiver: {}", &msg);
            match self.handle_message(&msg).await {
                Ok(_) => tracing::info!("Task done!"),
                Err(err) => {
                    match &msg {
                        #[cfg(not(feature = "prove"))]
                        ProverMessage::RunSession(task) => self
                            .storage
                            .write()?
                            .put_session(task.session_id.clone(), "FAILED".to_string()),
                        #[cfg(feature = "prove")]
                        ProverMessage::RunSnark(task) => self
                            .storage
                            .write()?
                            .put_session(task.session_id.clone(), "FAILED".to_string()),
                    };
                    tracing::error!("Task {} failed! - {:?}", msg, err)
                }
            }
        }
        Ok(())
    }

    async fn get_image(&self, task: &Task) -> Result<Vec<u8>, Error> {
        Ok(self
            .storage
            .read()?
            .get_image(&task.image_id)
            .ok_or_else(|| anyhow::anyhow!("Failed to get image for ID: {:?}", task.image_id))?)
    }

    async fn get_input(&self, task: &Task) -> Result<Vec<u8>, Error> {
        Ok(self
            .storage
            .read()?
            .get_input(&task.input_id)
            .ok_or_else(|| anyhow::anyhow!("Failed to get input for ID: {:?}", task.input_id))?)
    }

    async fn get_receipts(&self, task: &Task) -> Result<Vec<Vec<u8>>, Error> {
        let mut assumptions: Vec<Vec<u8>> = vec![];
        for receipt_id in &task.assumptions {
            let receipt = self
                .storage
                .read()?
                .get_receipt(receipt_id)
                .ok_or_else(|| {
                    anyhow::anyhow!("Failed to get input for ID: {:?}", task.input_id)
                })?;
            assumptions.push(receipt);
        }
        Ok(assumptions)
    }
}
