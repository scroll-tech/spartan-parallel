#![allow(non_snake_case)]
#![doc = include_str!("../README.md")]
#![deny(missing_docs)]
#![allow(clippy::assertions_on_result_states)]

// TODO: Can we allow split in R1CSGens?
// TODO: Can we parallelize the proofs?
// TODO: Problem when there is only one block & one execution

extern crate byteorder;
extern crate core;
extern crate curve25519_dalek;
extern crate digest;
extern crate merlin;
extern crate rand;
extern crate sha3;

#[cfg(feature = "multicore")]
extern crate rayon;

mod commitments;
mod custom_dense_mlpoly;
mod dense_mlpoly;
mod errors;
mod group;
/// R1CS instance used by libspartan
pub mod instance;
mod math;
mod nizk;
mod product_tree;
mod r1csinstance;
mod r1csproof;
mod random;
mod scalar;
mod sparse_mlpoly;
mod sumcheck;
mod timer;
mod transcript;
mod unipoly;

use std::{
  cmp::{max, Ordering},
  fs::File,
  io::Write,
};

use curve25519_dalek::ristretto::{CompressedRistretto, RistrettoPoint};
use dense_mlpoly::{DensePolynomial, PolyCommitment, PolyEvalProof};
use errors::{ProofVerifyError, R1CSError};
use instance::Instance;
use itertools::Itertools;
use math::Math;
use merlin::Transcript;
use r1csinstance::{
  R1CSCommitment, R1CSCommitmentGens, R1CSDecommitment, R1CSEvalProof, R1CSInstance,
};
use r1csproof::{R1CSGens, R1CSProof};
use random::RandomTape;
use scalar::Scalar;
use serde::{Deserialize, Serialize};
use timer::Timer;
use transcript::{AppendToTranscript, ProofTranscript};

use crate::commitments::Commitments;

const ZERO: Scalar = Scalar::zero();
const ONE: Scalar = Scalar::one();

const INIT_PHY_MEM_WIDTH: usize = 4;
const INIT_VIR_MEM_WIDTH: usize = 4;
const PHY_MEM_WIDTH: usize = 4;
const VIR_MEM_WIDTH: usize = 8;
const W3_WIDTH: usize = 8;

/// `ComputationCommitment` holds a public preprocessed NP statement (e.g., R1CS)
#[derive(Clone, Serialize)]
pub struct ComputationCommitment {
  comm: R1CSCommitment,
}

/// `ComputationDecommitment` holds information to decommit `ComputationCommitment`
pub struct ComputationDecommitment {
  decomm: R1CSDecommitment,
}

/// `Assignment` holds an assignment of values to either the inputs or variables in an `Instance`
#[derive(Clone, Serialize, Deserialize)]
pub struct Assignment {
  /// Entries of an assignment
  pub assignment: Vec<Scalar>,
}

impl Assignment {
  /// Constructs a new `Assignment` from a vector
  pub fn new(assignment: &[[u8; 32]]) -> Result<Assignment, R1CSError> {
    let bytes_to_scalar = |vec: &[[u8; 32]]| -> Result<Vec<Scalar>, R1CSError> {
      let mut vec_scalar: Vec<Scalar> = Vec::new();
      for v in vec {
        let val = Scalar::from_bytes(v);
        if val.is_some().unwrap_u8() == 1 {
          vec_scalar.push(val.unwrap());
        } else {
          return Err(R1CSError::InvalidScalar);
        }
      }
      Ok(vec_scalar)
    };

    let assignment_scalar = bytes_to_scalar(assignment);

    // check for any parsing errors
    if assignment_scalar.is_err() {
      return Err(R1CSError::InvalidScalar);
    }

    Ok(Assignment {
      assignment: assignment_scalar.unwrap(),
    })
  }

  /// Write the assignment into a file
  pub fn write(&self, mut f: &File) -> std::io::Result<()> {
    for assg in &self.assignment {
      write_bytes(&mut f, &assg.to_bytes())?;
    }
    Ok(())
  }
}

fn write_bytes(mut f: &File, bytes: &[u8; 32]) -> std::io::Result<()> {
  // Disregard the trailing zeros
  let mut size = 32;
  while size > 0 && bytes[size - 1] == 0 {
    size -= 1;
  }
  for i in 0..size {
    write!(&mut f, "{} ", bytes[i])?;
  }
  writeln!(&mut f, "")?;
  Ok(())
}

/// `VarsAssignment` holds an assignment of values to variables in an `Instance`
pub type VarsAssignment = Assignment;

/// `InputsAssignment` holds an assignment of values to inputs in an `Instance`
pub type InputsAssignment = Assignment;

/// `MemsAssignment` holds an assignment of values to (addr, val) pairs in an `Instance`
pub type MemsAssignment = Assignment;

/// `SNARKGens` holds public parameters for producing and verifying proofs with the Spartan SNARK
#[derive(Serialize)]
pub struct SNARKGens {
  /// Generator for witness commitment
  pub gens_r1cs_sat: R1CSGens,
  gens_r1cs_eval: R1CSCommitmentGens,
}

impl SNARKGens {
  /// Constructs a new `SNARKGens` given the size of the R1CS statement
  /// `num_nz_entries` specifies the maximum number of non-zero entries in any of the three R1CS matrices
  pub fn new(
    num_cons: usize,
    num_vars: usize,
    num_instances: usize,
    num_nz_entries: usize,
  ) -> Self {
    let num_vars_padded = num_vars.next_power_of_two();
    let num_instances_padded: usize = num_instances.next_power_of_two();
    let gens_r1cs_sat = R1CSGens::new(b"gens_r1cs_sat", num_cons, num_vars_padded);
    let gens_r1cs_eval = R1CSCommitmentGens::new(
      b"gens_r1cs_eval",
      num_instances_padded,
      num_cons,
      num_vars_padded,
      num_nz_entries,
    );
    SNARKGens {
      gens_r1cs_sat,
      gens_r1cs_eval,
    }
  }
}

// IOProofs contains a series of proofs that the committed values match the input and output of the program
#[derive(Serialize, Deserialize, Debug)]
struct IOProofs {
  // The prover needs to prove:
  // 1. Input and output block are both valid
  // 2. Block number of the input and output block are correct
  // 3. Input and outputs are correct
  // 4. The constant value of the input is 1
  proofs: Vec<PolyEvalProof>,
}

impl IOProofs {
  // Given the polynomial in execution order, generate all proofs
  fn prove(
    exec_poly_inputs: &DensePolynomial,

    num_ios: usize,
    num_inputs_unpadded: usize,
    num_proofs: usize,
    input_block_num: Scalar,
    output_block_num: Scalar,

    input_liveness: &Vec<bool>,
    input_offset: usize,
    output_offset: usize,
    input: Vec<Scalar>,
    output: Scalar,
    output_exec_num: usize,
    vars_gens: &R1CSGens,
    transcript: &mut Transcript,
    random_tape: &mut RandomTape,
  ) -> IOProofs {
    let r_len = (num_proofs * num_ios).log_2();
    let to_bin_array = |x: usize| {
      (0..r_len)
        .rev()
        .map(|n| (x >> n) & 1)
        .map(|i| Scalar::from(i as u64))
        .collect::<Vec<Scalar>>()
    };

    // input indices are 6(%SP) ++ 5(%AS) ++ [2 + input_offset..](others)
    // Filter out all dead inputs
    let mut input_indices: Vec<usize> = (0..input_liveness.len() - 2)
      .map(|i| 2 + input_offset + i)
      .collect();
    if input_liveness[1] {
      // %AS is alive, add entry 5
      input_indices.insert(0, 5);
    }
    if input_liveness[0] {
      // %SP is alive, add entry 6
      input_indices.insert(0, 6);
    }
    assert_eq!(input_liveness.len(), input.len());
    let mut live_input = Vec::new();
    for i in 0..input_liveness.len() {
      if input_liveness[i] {
        live_input.push(input[i].clone());
      }
    }
    input_indices = input_indices[..live_input.len()].to_vec();

    // batch prove all proofs
    let proofs = PolyEvalProof::prove_batched_points(
      exec_poly_inputs,
      None,
      [
        vec![
          0,                                                                             // input valid
          output_exec_num * num_ios, // output valid
          2,                         // input block num
          output_exec_num * num_ios + 2 + (num_inputs_unpadded - 1), // output block num
          output_exec_num * num_ios + 2 + (num_inputs_unpadded - 1) + output_offset - 1, // output correctness
        ],
        input_indices, // input correctness
      ]
      .concat()
      .iter()
      .map(|i| to_bin_array(*i))
      .collect(),
      vec![
        vec![ONE, ONE, input_block_num, output_block_num, output],
        live_input,
      ]
      .concat(),
      None,
      &vars_gens.gens_pc,
      transcript,
      random_tape,
    );
    IOProofs { proofs }
  }

  fn verify(
    &self,
    comm_poly_inputs: &PolyCommitment,
    num_ios: usize,
    num_inputs_unpadded: usize,
    num_proofs: usize,
    input_block_num: Scalar,
    output_block_num: Scalar,

    input_liveness: &Vec<bool>,
    input_offset: usize,
    output_offset: usize,
    input: Vec<Scalar>,
    output: Scalar,
    output_exec_num: usize,
    vars_gens: &R1CSGens,
    transcript: &mut Transcript,
  ) -> Result<(), ProofVerifyError> {
    let r_len = (num_proofs * num_ios).log_2();
    let to_bin_array = |x: usize| {
      (0..r_len)
        .rev()
        .map(|n| (x >> n) & 1)
        .map(|i| Scalar::from(i as u64))
        .collect::<Vec<Scalar>>()
    };

    // input indices are 6(%SP) ++ 5(%AS) ++ [2 + input_offset..](others)
    // Filter out all dead inputs
    let mut input_indices: Vec<usize> = (0..input_liveness.len() - 2)
      .map(|i| 2 + input_offset + i)
      .collect();
    if input_liveness[1] {
      // %AS is alive, add entry 5
      input_indices.insert(0, 5);
    }
    if input_liveness[0] {
      // %SP is alive, add entry 6
      input_indices.insert(0, 6);
    }
    assert_eq!(input_liveness.len(), input.len());
    let mut live_input = Vec::new();
    for i in 0..input_liveness.len() {
      if input_liveness[i] {
        live_input.push(input[i].clone());
      }
    }
    input_indices = input_indices[..live_input.len()].to_vec();
    // batch verify all proofs
    let _ = PolyEvalProof::verify_plain_batched_points(
      &self.proofs,
      &vars_gens.gens_pc,
      transcript,
      [
        vec![
          0,                                                                             // input valid
          output_exec_num * num_ios, // output valid
          2,                         // input block num
          output_exec_num * num_ios + 2 + (num_inputs_unpadded - 1), // output block num
          output_exec_num * num_ios + 2 + (num_inputs_unpadded - 1) + output_offset - 1, // output correctness
        ],
        input_indices, // input correctness
      ]
      .concat()
      .iter()
      .map(|i| to_bin_array(*i))
      .collect(),
      vec![
        vec![ONE, ONE, input_block_num, output_block_num, output],
        live_input,
      ]
      .concat(),
      comm_poly_inputs,
    )?;
    Ok(())
  }
}

// ShiftProofs contains a series of proofs and openings that a list of polynomials / commitments are indeed shifts of another list of polynomials
// We do so by treating both polynomials as univariate and evaluate on a single point C
// Finally, show shifted(C) = orig(C) * C^(shift_size) + rc * openings, where rc * openings are the first few entries of the original poly dot product with the power series of C
#[derive(Serialize, Deserialize, Debug)]
struct ShiftProofs {
  proof: PolyEvalProof,
  C_orig_evals: Vec<CompressedRistretto>,
  C_shifted_evals: Vec<CompressedRistretto>,
  openings: Vec<Vec<CompressedRistretto>>,
}

impl ShiftProofs {
  fn prove(
    orig_polys: Vec<&DensePolynomial>,
    shifted_polys: Vec<&DensePolynomial>,
    // For each orig_poly, how many entries at the front of proof 0 are non-zero?
    header_len_list: Vec<usize>,
    vars_gens: &R1CSGens,
    transcript: &mut Transcript,
    random_tape: &mut RandomTape,
  ) -> ShiftProofs {
    // Assert that all polynomials are of the same size
    let num_instances = orig_polys.len();
    assert_eq!(num_instances, shifted_polys.len());
    let max_poly_size = orig_polys
      .iter()
      .fold(0, |m, p| if p.len() > m { p.len() } else { m });
    let max_poly_size =
      shifted_polys
        .iter()
        .fold(max_poly_size, |m, p| if p.len() > m { p.len() } else { m });
    // Open entry 0..header_len_list[p] - 1
    let mut openings = vec![Vec::new(); num_instances];
    for p in 0..num_instances {
      for i in 0..header_len_list[p] {
        let entry = orig_polys[p][i]
          .commit(&ZERO, &vars_gens.gens_pc.gens.gens_1)
          .compress();
        entry.append_to_transcript(b"shift_header_entry", transcript);
        openings[p].push(entry);
      }
    }
    let c = transcript.challenge_scalar(b"challenge_c");
    let mut rc = Vec::new();
    let mut next_c = ONE;
    for _ in 0..max_poly_size {
      rc.push(next_c);
      next_c *= c;
    }
    let mut orig_evals = Vec::new();
    let mut shifted_evals = Vec::new();
    let mut C_orig_evals = Vec::new();
    let mut C_shifted_evals = Vec::new();
    for p in 0..num_instances {
      let orig_poly = orig_polys[p];
      let shifted_poly = shifted_polys[p];
      let orig_eval = (0..orig_poly.len()).fold(ZERO, |a, b| a + orig_poly[b] * rc[b]);
      let shifted_eval = (0..shifted_poly.len()).fold(ZERO, |a, b| a + shifted_poly[b] * rc[b]);
      orig_evals.push(orig_eval);
      shifted_evals.push(shifted_eval);
      C_orig_evals.push(
        orig_eval
          .commit(&ZERO, &vars_gens.gens_pc.gens.gens_1)
          .compress(),
      );
      C_shifted_evals.push(
        shifted_eval
          .commit(&ZERO, &vars_gens.gens_pc.gens.gens_1)
          .compress(),
      );
    }
    let (addr_phy_mems_shift_proof, _eval) = PolyEvalProof::prove_uni_batched_instances(
      &[orig_polys, shifted_polys].concat(),
      &c,
      &[orig_evals, shifted_evals].concat(),
      &vars_gens.gens_pc,
      transcript,
      random_tape,
    );
    ShiftProofs {
      proof: addr_phy_mems_shift_proof,
      C_orig_evals,
      C_shifted_evals,
      openings,
    }
  }

  fn verify(
    &self,
    orig_comms: Vec<&PolyCommitment>,
    shifted_comms: Vec<&PolyCommitment>,
    poly_size_list: Vec<usize>,
    shift_size_list: Vec<usize>,
    // For each orig_poly, how many entries at the front of proof 0 are non-zero?
    header_len_list: Vec<usize>,
    vars_gens: &R1CSGens,
    transcript: &mut Transcript,
  ) -> Result<(), ProofVerifyError> {
    let num_instances = orig_comms.len();
    // Open entry 0..header_len_list[p] - 1
    for p in 0..num_instances {
      for i in 0..header_len_list[p] {
        self.openings[p][i].append_to_transcript(b"shift_header_entry", transcript);
      }
    }
    let max_shift_size = shift_size_list
      .iter()
      .fold(0, |m, i| if *i > m { *i } else { m });
    let c = transcript.challenge_scalar(b"challenge_c");
    let mut rc = Vec::new();
    let mut next_c = ONE;
    for _ in 0..max_shift_size + 1 {
      rc.push(next_c);
      next_c *= c;
    }
    let C_evals_orig_decompressed: Vec<RistrettoPoint> = self
      .C_orig_evals
      .iter()
      .map(|i| i.decompress().unwrap())
      .collect();
    let C_evals_shifted_decompressed: Vec<RistrettoPoint> = self
      .C_shifted_evals
      .iter()
      .map(|i| i.decompress().unwrap())
      .collect();
    // shifted(C) = orig(C) * C^(shift_size) + rc * openings
    /*
    for p in 0..num_instances {
      let orig = C_evals_orig_decompressed[p];
      let shifted = C_evals_shifted_decompressed[p];
      let reverse_shifted = (0..header_len_list[p]).fold(shifted * rc[shift_size_list[p]], |s, i| s + rc[i] * self.openings[p][i].decompress().unwrap());
      assert_eq!(orig, reverse_shifted);
    }
    */
    // Proof of opening
    self.proof.verify_uni_batched_instances(
      &vars_gens.gens_pc,
      transcript,
      &c,
      &[C_evals_orig_decompressed, C_evals_shifted_decompressed].concat(),
      &vec![orig_comms, shifted_comms].concat(),
      [poly_size_list.clone(), poly_size_list].concat(),
    )?;
    Ok(())
  }
}

// Information regarding one witness sec
#[derive(Clone)]
struct ProverWitnessSecInfo {
  // Number of inputs per block
  num_inputs: Vec<usize>,
  // num_instances x num_proofs x num_inputs hypermatrix for all values
  w_mat: Vec<Vec<Vec<Scalar>>>,
  // One dense polynomial per instance
  poly_w: Vec<DensePolynomial>,
}

impl ProverWitnessSecInfo {
  fn new(w_mat: Vec<Vec<Vec<Scalar>>>, poly_w: Vec<DensePolynomial>) -> ProverWitnessSecInfo {
    ProverWitnessSecInfo {
      num_inputs: w_mat.iter().map(|i| i[0].len()).collect(),
      w_mat,
      poly_w,
    }
  }

  fn dummy() -> ProverWitnessSecInfo {
    ProverWitnessSecInfo {
      num_inputs: Vec::new(),
      w_mat: Vec::new(),
      poly_w: Vec::new(),
    }
  }

  // Concatenate the components in the given order to a new prover witness sec
  fn concat(components: Vec<&ProverWitnessSecInfo>) -> ProverWitnessSecInfo {
    let mut num_inputs = Vec::new();
    let mut w_mat = Vec::new();
    let mut poly_w = Vec::new();

    for c in components {
      num_inputs.extend(c.num_inputs.clone());
      w_mat.extend(c.w_mat.clone());
      poly_w.extend(c.poly_w.clone());
    }
    ProverWitnessSecInfo {
      num_inputs,
      w_mat,
      poly_w,
    }
  }

  // Merge multiple ProverWitnessSec, sort them by decreasing number of proofs
  // Assume all components are sorted
  // Returns: 1. the merged ProverWitnessSec,
  //          2. for each instance in the merged ProverWitnessSec, the component it orignally belongs to
  fn merge(components: Vec<&ProverWitnessSecInfo>) -> (ProverWitnessSecInfo, Vec<usize>) {
    // Merge algorithm with pointer on each component
    let mut pointers = vec![0; components.len()];
    let merged_size = components.iter().fold(0, |a, b| a + b.num_inputs.len());
    // Map from instances of the merged ProverWitnessSec to each component
    let mut inst_map = Vec::new();
    let mut merged_num_inputs = Vec::new();
    let mut merged_w_mat = Vec::new();
    let mut merged_poly_w = Vec::new();
    while inst_map.len() < merged_size {
      // Choose the next instance with the most proofs
      let mut next_max_num_proofs = 0;
      let mut next_component = 0;
      for i in 0..components.len() {
        if pointers[i] < components[i].w_mat.len() {
          let next_num_proofs = components[i].w_mat[pointers[i]].len();
          if next_num_proofs > next_max_num_proofs {
            next_max_num_proofs = next_num_proofs;
            next_component = i;
          }
        }
      }

      // Append the selected instance
      inst_map.push(next_component);
      merged_num_inputs.push(components[next_component].num_inputs[pointers[next_component]]);
      merged_w_mat.push(components[next_component].w_mat[pointers[next_component]].clone());
      merged_poly_w.push(components[next_component].poly_w[pointers[next_component]].clone());
      pointers[next_component] = pointers[next_component] + 1;
    }

    (
      ProverWitnessSecInfo {
        num_inputs: merged_num_inputs,
        w_mat: merged_w_mat,
        poly_w: merged_poly_w,
      },
      inst_map,
    )
  }
}

// Information regarding one witness sec
#[derive(Clone)]
struct VerifierWitnessSecInfo {
  // Number of inputs per block
  num_inputs: Vec<usize>,
  // Number of proofs per block, used by merge
  num_proofs: Vec<usize>,
  // One commitment per instance
  comm_w: Vec<PolyCommitment>,
}

impl VerifierWitnessSecInfo {
  // Unfortunately, cannot obtain all metadata from the commitment
  fn new(
    num_inputs: Vec<usize>,
    num_proofs: &Vec<usize>,
    comm_w: Vec<PolyCommitment>,
  ) -> VerifierWitnessSecInfo {
    assert!(
      comm_w.len() == 0 || (num_inputs.len() == comm_w.len() && num_proofs.len() >= comm_w.len())
    );
    VerifierWitnessSecInfo {
      num_inputs,
      num_proofs: num_proofs[..comm_w.len()].to_vec(),
      comm_w: comm_w,
    }
  }

  fn dummy() -> VerifierWitnessSecInfo {
    VerifierWitnessSecInfo {
      num_inputs: Vec::new(),
      num_proofs: Vec::new(),
      comm_w: Vec::new(),
    }
  }

  // Concatenate the components in the given order to a new verifier witness sec
  fn concat(components: Vec<&VerifierWitnessSecInfo>) -> VerifierWitnessSecInfo {
    let mut num_inputs = Vec::new();
    let mut num_proofs = Vec::new();
    let mut comm_w = Vec::new();

    for c in components {
      num_inputs.extend(c.num_inputs.clone());
      num_proofs.extend(c.num_proofs.clone());
      comm_w.extend(c.comm_w.clone());
    }

    VerifierWitnessSecInfo {
      num_inputs,
      num_proofs,
      comm_w,
    }
  }

  // Merge multiple VerifierWitnessSec, sort them by decreasing number of proofs
  // Assume all components are sorted
  // Returns: 1. the merged VerifierWitnessSec,
  //          2. for each instance in the merged VerifierWitnessSec, the component it orignally belong to
  fn merge(components: Vec<&VerifierWitnessSecInfo>) -> (VerifierWitnessSecInfo, Vec<usize>) {
    // Merge algorithm with pointer on each component
    let mut pointers = vec![0; components.len()];
    let merged_size = components.iter().fold(0, |a, b| a + b.num_inputs.len());
    // Map from instances of the merged ProverWitnessSec to each component
    let mut inst_map = Vec::new();
    let mut merged_num_inputs = Vec::new();
    let mut merged_num_proofs = Vec::new();
    let mut merged_comm_w = Vec::new();
    while inst_map.len() < merged_size {
      // Choose the next instance with the most proofs
      let mut next_max_num_proofs = 0;
      let mut next_component = 0;
      for i in 0..components.len() {
        if pointers[i] < components[i].num_proofs.len() {
          let next_num_proofs = components[i].num_proofs[pointers[i]];
          if next_num_proofs > next_max_num_proofs {
            next_max_num_proofs = next_num_proofs;
            next_component = i;
          }
        }
      }
      // Append the selected instance
      inst_map.push(next_component);
      merged_num_inputs.push(components[next_component].num_inputs[pointers[next_component]]);
      merged_num_proofs.push(components[next_component].num_proofs[pointers[next_component]]);
      merged_comm_w.push(components[next_component].comm_w[pointers[next_component]].clone());
      pointers[next_component] = pointers[next_component] + 1;
    }

    (
      VerifierWitnessSecInfo {
        num_inputs: merged_num_inputs,
        num_proofs: merged_num_proofs,
        comm_w: merged_comm_w,
      },
      inst_map,
    )
  }
}

/// `SNARK` holds a proof produced by Spartan SNARK
#[derive(Serialize, Deserialize, Debug)]
pub struct SNARK {
  block_comm_vars_list: Vec<PolyCommitment>,
  exec_comm_inputs: Vec<PolyCommitment>,
  // comm_init_mems: Vec<PolyCommitment>, HANDLED BY THE VERIFIER
  addr_comm_phy_mems: PolyCommitment,
  addr_comm_phy_mems_shifted: PolyCommitment,
  addr_comm_vir_mems: PolyCommitment,
  addr_comm_vir_mems_shifted: PolyCommitment,
  addr_comm_ts_bits: PolyCommitment,

  perm_exec_comm_w2_list: PolyCommitment,
  perm_exec_comm_w3_list: PolyCommitment,
  perm_exec_comm_w3_shifted: PolyCommitment,

  block_comm_w2_list: Vec<PolyCommitment>,
  block_comm_w3_list: Vec<PolyCommitment>,
  block_comm_w3_list_shifted: Vec<PolyCommitment>,

  init_phy_mem_comm_w2: PolyCommitment,
  init_phy_mem_comm_w3: PolyCommitment,
  init_phy_mem_comm_w3_shifted: PolyCommitment,

  init_vir_mem_comm_w2: PolyCommitment,
  init_vir_mem_comm_w3: PolyCommitment,
  init_vir_mem_comm_w3_shifted: PolyCommitment,

  phy_mem_addr_comm_w2: PolyCommitment,
  phy_mem_addr_comm_w3: PolyCommitment,
  phy_mem_addr_comm_w3_shifted: PolyCommitment,

  vir_mem_addr_comm_w2: PolyCommitment,
  vir_mem_addr_comm_w3: PolyCommitment,
  vir_mem_addr_comm_w3_shifted: PolyCommitment,

  block_r1cs_sat_proof: R1CSProof,
  block_inst_evals_bound_rp: [Scalar; 3],
  block_inst_evals_list: Vec<Scalar>,
  block_r1cs_eval_proof_list: Vec<R1CSEvalProof>,

  pairwise_check_r1cs_sat_proof: R1CSProof,
  pairwise_check_inst_evals_bound_rp: [Scalar; 3],
  pairwise_check_inst_evals_list: Vec<Scalar>,
  pairwise_check_r1cs_eval_proof: R1CSEvalProof,

  perm_root_r1cs_sat_proof: R1CSProof,
  perm_root_inst_evals: [Scalar; 3],
  perm_root_r1cs_eval_proof: R1CSEvalProof,

  // Product proof for permutation
  perm_poly_poly_list: Vec<Scalar>,
  proof_eval_perm_poly_prod_list: Vec<PolyEvalProof>,

  shift_proof: ShiftProofs,
  io_proof: IOProofs,
}

// Sort block_num_proofs and record where each entry is
struct InstanceSortHelper {
  num_exec: usize,
  index: usize,
}
impl InstanceSortHelper {
  fn new(num_exec: usize, index: usize) -> InstanceSortHelper {
    InstanceSortHelper { num_exec, index }
  }
}

// Ordering of InstanceSortHelper solely by num_exec
impl Ord for InstanceSortHelper {
  fn cmp(&self, other: &Self) -> Ordering {
    self.num_exec.cmp(&other.num_exec)
  }
}
impl PartialOrd for InstanceSortHelper {
  fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
    Some(self.cmp(other))
  }
}
impl PartialEq for InstanceSortHelper {
  fn eq(&self, other: &Self) -> bool {
    self.num_exec == other.num_exec
  }
}
impl Eq for InstanceSortHelper {}

impl SNARK {
  fn protocol_name() -> &'static [u8] {
    b"Spartan SNARK proof"
  }

  /// A public computation to create a commitment to a list of R1CS instances
  pub fn multi_encode(
    inst: &Instance,
    gens: &SNARKGens,
  ) -> (
    Vec<Vec<usize>>,
    Vec<ComputationCommitment>,
    Vec<ComputationDecommitment>,
  ) {
    let timer_encode = Timer::new("SNARK::encode");
    let (label_map, mut comm, mut decomm) = inst.inst.multi_commit(&gens.gens_r1cs_eval);
    timer_encode.stop();
    (
      label_map,
      comm
        .drain(..)
        .map(|i| ComputationCommitment { comm: i })
        .collect(),
      decomm
        .drain(..)
        .map(|i| ComputationDecommitment { decomm: i })
        .collect(),
    )
  }

  /// A public computation to create a commitment to a single R1CS instance
  pub fn encode(
    inst: &Instance,
    gens: &SNARKGens,
  ) -> (ComputationCommitment, ComputationDecommitment) {
    let timer_encode = Timer::new("SNARK::encode");
    let (comm, decomm) = inst.inst.commit(&gens.gens_r1cs_eval);
    timer_encode.stop();
    (
      ComputationCommitment { comm },
      ComputationDecommitment { decomm },
    )
  }

  // Given information regarding a group of memory assignments, generate w2, w3, and w3_shifted
  fn mem_gen<const MEM_WIDTH: usize>(
    total_num_mem_accesses: usize,
    mems_list: &Vec<Vec<Scalar>>,
    comb_r: &Scalar,
    comb_tau: &Scalar,
    vars_gens: &R1CSGens,
    transcript: &mut Transcript,
  ) -> (
    ProverWitnessSecInfo,
    PolyCommitment,
    ProverWitnessSecInfo,
    PolyCommitment,
    ProverWitnessSecInfo,
    PolyCommitment,
  ) {
    if total_num_mem_accesses > 0 {
      // init_mem_w2 is (I, O, ZO, r * data, 0, 0)
      // where ZO = 0,

      let mut mem_w2 = Vec::new();
      for q in 0..total_num_mem_accesses {
        mem_w2.push(vec![ZERO; MEM_WIDTH]);
        mem_w2[q][3] = comb_r * mems_list[q][3];
      }
      // init_mems_w3 is (v, x, pi, D, I, O)
      // where I = v * (v + addr + r * data + r^2 * ls + r^3 * ts),
      //       O = v * v = v
      // are used by (dummy) consistency check
      let mut mem_w3 = vec![vec![ZERO; W3_WIDTH]; total_num_mem_accesses];
      for q in (0..total_num_mem_accesses).rev() {
        // v
        mem_w3[q][0] = mems_list[q][0];
        // x = v * (tau - addr - r * data - r^2 * ls - r^3 * ts)
        mem_w3[q][1] = mems_list[q][0] * (comb_tau - mems_list[q][2] - mem_w2[q][3]);
        // pi and D
        if q != total_num_mem_accesses - 1 {
          mem_w3[q][3] = mem_w3[q][1] * (mem_w3[q + 1][2] + ONE - mem_w3[q + 1][0]);
        } else {
          mem_w3[q][3] = mem_w3[q][1];
        }
        mem_w3[q][2] = mem_w3[q][0] * mem_w3[q][3];
        mem_w3[q][4] = mems_list[q][0] * (mems_list[q][0] + mems_list[q][2] + mem_w2[q][3]);
        mem_w3[q][5] = mems_list[q][0];
      }

      let (
        mem_poly_w2,
        mem_comm_w2,
        mem_poly_w3,
        mem_comm_w3,
        mem_poly_w3_shifted,
        mem_comm_w3_shifted,
      ) = {
        let (mem_poly_w2, mem_comm_w2) = {
          // Flatten the witnesses into a Q_i * X list
          let w2_list_p = mem_w2.clone().into_iter().flatten().collect();
          // create a multilinear polynomial using the supplied assignment for variables
          let mem_poly_w2 = DensePolynomial::new(w2_list_p);

          // produce a commitment to the satisfying assignment
          let (mem_comm_w2, _blinds_vars) = mem_poly_w2.commit(&vars_gens.gens_pc, None);

          // add the commitment to the prover's transcript
          mem_comm_w2.append_to_transcript(b"poly_commitment", transcript);
          (mem_poly_w2, mem_comm_w2)
        };

        let (mem_poly_w3, mem_comm_w3) = {
          // Flatten the witnesses into a Q_i * X list
          let w3_list_p = mem_w3.clone().into_iter().flatten().collect();
          // create a multilinear polynomial using the supplied assignment for variables
          let mem_poly_w3 = DensePolynomial::new(w3_list_p);

          // produce a commitment to the satisfying assignment
          let (mem_comm_w3, _blinds_vars) = mem_poly_w3.commit(&vars_gens.gens_pc, None);

          // add the commitment to the prover's transcript
          mem_comm_w3.append_to_transcript(b"poly_commitment", transcript);
          (mem_poly_w3, mem_comm_w3)
        };

        let (mem_poly_w3_shifted, mem_comm_w3_shifted) = {
          // Flatten the witnesses into a Q_i * X list
          let w3_list_p = [
            mem_w3[1..].to_vec().clone().into_iter().flatten().collect(),
            vec![ZERO; W3_WIDTH],
          ]
          .concat();
          // create a multilinear polynomial using the supplied assignment for variables
          let mem_poly_w3_shifted = DensePolynomial::new(w3_list_p);

          // produce a commitment to the satisfying assignment
          let (mem_comm_w3_shifted, _blinds_vars) =
            mem_poly_w3_shifted.commit(&vars_gens.gens_pc, None);

          // add the commitment to the prover's transcript
          mem_comm_w3_shifted.append_to_transcript(b"poly_commitment", transcript);
          (mem_poly_w3_shifted, mem_comm_w3_shifted)
        };

        (
          mem_poly_w2,
          mem_comm_w2,
          mem_poly_w3,
          mem_comm_w3,
          mem_poly_w3_shifted,
          mem_comm_w3_shifted,
        )
      };

      let mem_w2_prover = ProverWitnessSecInfo::new(vec![mem_w2], vec![mem_poly_w2]);
      let mem_w3_prover = ProverWitnessSecInfo::new(vec![mem_w3.clone()], vec![mem_poly_w3]);
      let mem_w3_shifted_prover = ProverWitnessSecInfo::new(
        vec![[mem_w3[1..].to_vec(), vec![vec![ZERO; W3_WIDTH]]].concat()],
        vec![mem_poly_w3_shifted],
      );

      (
        mem_w2_prover,
        mem_comm_w2,
        mem_w3_prover,
        mem_comm_w3,
        mem_w3_shifted_prover,
        mem_comm_w3_shifted,
      )
    } else {
      (
        ProverWitnessSecInfo::dummy(),
        PolyCommitment::empty(),
        ProverWitnessSecInfo::dummy(),
        PolyCommitment::empty(),
        ProverWitnessSecInfo::dummy(),
        PolyCommitment::empty(),
      )
    }
  }

  /// A method to produce a SNARK proof of the satisfiability of an R1CS instance
  pub fn prove(
    input_block_num: usize,
    output_block_num: usize,
    input_liveness: &Vec<bool>,
    func_input_width: usize,
    input_offset: usize,
    output_offset: usize,
    input: &Vec<[u8; 32]>,
    output: &[u8; 32],
    output_exec_num: usize,

    num_vars: usize,
    num_ios: usize,
    max_block_num_phy_ops: usize,
    block_num_phy_ops: &Vec<usize>,
    max_block_num_vir_ops: usize,
    block_num_vir_ops: &Vec<usize>,
    mem_addr_ts_bits_size: usize,
    num_inputs_unpadded: usize,
    block_num_vars: &Vec<usize>,

    block_num_instances_bound: usize,
    block_max_num_proofs: usize,
    block_num_proofs: &Vec<usize>,
    block_inst: &mut Instance,
    block_comm_map: &Vec<Vec<usize>>,
    block_comm_list: &Vec<ComputationCommitment>,
    block_decomm_list: &Vec<ComputationDecommitment>,
    block_gens: &SNARKGens,

    consis_num_proofs: usize,
    total_num_init_phy_mem_accesses: usize,
    total_num_init_vir_mem_accesses: usize,
    total_num_phy_mem_accesses: usize,
    total_num_vir_mem_accesses: usize,
    pairwise_check_inst: &mut Instance,
    pairwise_check_comm: &ComputationCommitment,
    pairwise_check_decomm: &ComputationDecommitment,
    pairwise_check_gens: &SNARKGens,

    block_vars_mat: Vec<Vec<VarsAssignment>>,
    exec_inputs_list: Vec<InputsAssignment>,
    init_phy_mems_list: Vec<MemsAssignment>,
    init_vir_mems_list: Vec<MemsAssignment>,
    addr_phy_mems_list: Vec<MemsAssignment>,
    addr_vir_mems_list: Vec<MemsAssignment>,
    addr_ts_bits_list: Vec<MemsAssignment>,

    perm_root_inst: &Instance,
    perm_root_comm: &ComputationCommitment,
    perm_root_decomm: &ComputationDecommitment,
    perm_root_gens: &SNARKGens,

    vars_gens: &R1CSGens,
    transcript: &mut Transcript,
  ) -> Self {
    let timer_prove = Timer::new("SNARK::prove");

    // we create a Transcript object seeded with a random Scalar
    // to aid the prover produce its randomness
    let mut random_tape = RandomTape::new(b"proof");

    transcript.append_protocol_name(SNARK::protocol_name());

    // --
    // ASSERTIONS
    // --
    assert!(0 < consis_num_proofs);
    for p in 0..block_num_instances_bound {
      assert!(block_num_proofs[p] <= block_max_num_proofs);
    }
    let io_width = 2 * num_inputs_unpadded;

    // --
    // PREPROCESSING
    // --
    // unwrap the assignments
    let mut block_vars_mat = block_vars_mat
      .into_iter()
      .map(|a| a.into_iter().map(|v| v.assignment).collect_vec())
      .collect_vec();
    let mut exec_inputs_list = exec_inputs_list
      .into_iter()
      .map(|v| v.assignment)
      .collect_vec();
    let mut init_phy_mems_list = init_phy_mems_list
      .into_iter()
      .map(|v| v.assignment)
      .collect_vec();
    let mut init_vir_mems_list = init_vir_mems_list
      .into_iter()
      .map(|v| v.assignment)
      .collect_vec();
    let mut addr_phy_mems_list = addr_phy_mems_list
      .into_iter()
      .map(|v| v.assignment)
      .collect_vec();
    let mut addr_vir_mems_list = addr_vir_mems_list
      .into_iter()
      .map(|v| v.assignment)
      .collect_vec();
    let mut addr_ts_bits_list = addr_ts_bits_list
      .into_iter()
      .map(|v| v.assignment)
      .collect_vec();

    // --
    // INSTANCE COMMITMENTS
    // --
    let input_block_num = Scalar::from(input_block_num as u64);
    let output_block_num = Scalar::from(output_block_num as u64);
    let input: Vec<Scalar> = input
      .iter()
      .map(|i| Scalar::from_bytes(i).unwrap())
      .collect();
    let output: Scalar = Scalar::from_bytes(output).unwrap();
    {
      let timer_commit = Timer::new("inst_commit");
      // Commit public parameters
      Scalar::from(func_input_width as u64).append_to_transcript(b"func_input_width", transcript);
      Scalar::from(input_offset as u64).append_to_transcript(b"input_offset", transcript);
      Scalar::from(output_offset as u64).append_to_transcript(b"output_offset", transcript);
      Scalar::from(output_exec_num as u64).append_to_transcript(b"output_exec_num", transcript);
      Scalar::from(num_ios as u64).append_to_transcript(b"num_ios", transcript);
      for n in block_num_vars {
        Scalar::from(*n as u64).append_to_transcript(b"block_num_vars", transcript);
      }
      Scalar::from(mem_addr_ts_bits_size as u64)
        .append_to_transcript(b"mem_addr_ts_bits_size", transcript);
      Scalar::from(num_inputs_unpadded as u64)
        .append_to_transcript(b"num_inputs_unpadded", transcript);
      Scalar::from(block_num_instances_bound as u64)
        .append_to_transcript(b"block_num_instances_bound", transcript);
      Scalar::from(block_max_num_proofs as u64)
        .append_to_transcript(b"block_max_num_proofs", transcript);
      for p in block_num_phy_ops {
        Scalar::from(*p as u64).append_to_transcript(b"block_num_phy_ops", transcript);
      }
      for v in block_num_vir_ops {
        Scalar::from(*v as u64).append_to_transcript(b"block_num_vir_ops", transcript);
      }
      Scalar::from(total_num_init_phy_mem_accesses as u64)
        .append_to_transcript(b"total_num_init_phy_mem_accesses", transcript);
      Scalar::from(total_num_init_vir_mem_accesses as u64)
        .append_to_transcript(b"total_num_init_vir_mem_accesses", transcript);
      Scalar::from(total_num_phy_mem_accesses as u64)
        .append_to_transcript(b"total_num_phy_mem_accesses", transcript);
      Scalar::from(total_num_vir_mem_accesses as u64)
        .append_to_transcript(b"total_num_vir_mem_accesses", transcript);

      // commit num_proofs
      Scalar::from(block_max_num_proofs as u64)
        .append_to_transcript(b"block_max_num_proofs", transcript);
      for n in block_num_proofs {
        Scalar::from(*n as u64).append_to_transcript(b"block_num_proofs", transcript);
      }

      // append a commitment to the computation to the transcript
      for b in block_comm_map {
        for l in b {
          Scalar::from(*l as u64).append_to_transcript(b"block_comm_map", transcript);
        }
      }
      for c in block_comm_list {
        c.comm.append_to_transcript(b"block_comm", transcript);
      }
      pairwise_check_comm
        .comm
        .append_to_transcript(b"pairwise_comm", transcript);
      perm_root_comm
        .comm
        .append_to_transcript(b"perm_comm", transcript);

      // Commit io
      input_block_num.append_to_transcript(b"input_block_num", transcript);
      output_block_num.append_to_transcript(b"output_block_num", transcript);
      input.append_to_transcript(b"input_list", transcript);
      output.append_to_transcript(b"output_list", transcript);

      timer_commit.stop();
    }

    // --
    // BLOCK SORT
    // --
    let timer_sort = Timer::new("block_sort");
    // Block_num_instance is the number of non-zero entries in block_num_proofs
    let block_num_instances = block_num_proofs
      .iter()
      .fold(0, |i, j| if *j > 0 { i + 1 } else { i });
    // Sort the following based on block_num_proofs:
    // - block_num_proofs
    // - block_inst, block_comm, block_decomm
    // - block_num_phy_mem_accesses
    // - mem_extract_inst, mem_extract_comm, mem_extract_decomm
    let mut inst_sorter = Vec::new();
    for i in 0..block_num_instances_bound {
      inst_sorter.push(InstanceSortHelper::new(block_num_proofs[i], i))
    }
    // Sort from high -> low
    inst_sorter.sort_by(|a, b| b.cmp(a));

    let inst_sorter = &inst_sorter[..block_num_instances];
    let mut block_num_proofs: Vec<usize> = inst_sorter.iter().map(|i| i.num_exec).collect();
    // index[i] = j => the original jth entry should now be at the ith position
    let index: Vec<usize> = inst_sorter.iter().map(|i| i.index).collect();
    let block_inst_unsorted = block_inst.clone();
    block_inst.sort(block_num_instances, &index);
    let block_num_vars: Vec<usize> = (0..block_num_instances)
      .map(|i| block_num_vars[index[i]])
      .collect();
    let block_num_phy_ops: Vec<usize> = (0..block_num_instances)
      .map(|i| block_num_phy_ops[index[i]])
      .collect();
    let block_num_vir_ops: Vec<usize> = (0..block_num_instances)
      .map(|i| block_num_vir_ops[index[i]])
      .collect();

    // --
    // PADDING
    // --
    let dummy_inputs = vec![ZERO; num_ios];
    // For every block that num_proofs is not a power of 2, pad vars_mat and inputs_mat until the length is a power of 2
    let block_max_num_proofs = block_max_num_proofs.next_power_of_two();
    for i in 0..block_num_instances {
      let dummy_vars = vec![ZERO; block_vars_mat[i][0].len()];
      let gap = block_num_proofs[i].next_power_of_two() - block_num_proofs[i];
      block_vars_mat[i].extend(vec![dummy_vars.clone(); gap]);
      block_num_proofs[i] = block_num_proofs[i].next_power_of_two();
    }
    // Pad exec_inputs with dummys so the length is a power of 2
    exec_inputs_list.extend(vec![
      dummy_inputs;
      consis_num_proofs.next_power_of_two()
        - consis_num_proofs
    ]);
    let consis_num_proofs = consis_num_proofs.next_power_of_two();

    // Pad init_mems with dummys so the length is a power of 2
    if total_num_init_phy_mem_accesses > 0 {
      let dummy_addr = vec![ZERO; INIT_PHY_MEM_WIDTH];
      init_phy_mems_list.extend(vec![
        dummy_addr;
        total_num_init_phy_mem_accesses.next_power_of_two()
          - total_num_init_phy_mem_accesses
      ]);
    }
    let total_num_init_phy_mem_accesses = if total_num_init_phy_mem_accesses == 0 {
      0
    } else {
      total_num_init_phy_mem_accesses.next_power_of_two()
    };
    if total_num_init_vir_mem_accesses > 0 {
      let dummy_addr = vec![ZERO; INIT_VIR_MEM_WIDTH];
      init_vir_mems_list.extend(vec![
        dummy_addr;
        total_num_init_vir_mem_accesses.next_power_of_two()
          - total_num_init_vir_mem_accesses
      ]);
    }
    let total_num_init_vir_mem_accesses = if total_num_init_vir_mem_accesses == 0 {
      0
    } else {
      total_num_init_vir_mem_accesses.next_power_of_two()
    };
    // Pad addr_phy_mems with dummys so the length is a power of 2
    if total_num_phy_mem_accesses > 0 {
      let dummy_addr = vec![ZERO; PHY_MEM_WIDTH];
      addr_phy_mems_list.extend(vec![
        dummy_addr;
        total_num_phy_mem_accesses.next_power_of_two()
          - total_num_phy_mem_accesses
      ]);
    }
    let total_num_phy_mem_accesses = if total_num_phy_mem_accesses == 0 {
      0
    } else {
      total_num_phy_mem_accesses.next_power_of_two()
    };
    // Pad addr_vir_mems with dummys so the length is a power of 2
    if total_num_vir_mem_accesses > 0 {
      let dummy_addr = vec![ZERO; VIR_MEM_WIDTH];
      addr_vir_mems_list.extend(vec![
        dummy_addr;
        total_num_vir_mem_accesses.next_power_of_two()
          - total_num_vir_mem_accesses
      ]);
      let dummy_ts = vec![ZERO; mem_addr_ts_bits_size];
      addr_ts_bits_list.extend(vec![
        dummy_ts;
        total_num_vir_mem_accesses.next_power_of_two()
          - total_num_vir_mem_accesses
      ]);
    }
    let total_num_vir_mem_accesses = if total_num_vir_mem_accesses == 0 {
      0
    } else {
      total_num_vir_mem_accesses.next_power_of_two()
    };
    let block_num_proofs = &block_num_proofs;

    // --
    // PAIRWISE SORT
    // --
    // Note: perform pairwise sort after padding because pairwise sort uses padded values as parameter
    // Sort the pairwise instances: CONSIS_CHECK, PHY_MEM_COHERE
    let mut inst_sorter = Vec::new();
    inst_sorter.push(InstanceSortHelper::new(consis_num_proofs, 0));
    inst_sorter.push(InstanceSortHelper::new(total_num_phy_mem_accesses, 1));
    inst_sorter.push(InstanceSortHelper::new(total_num_vir_mem_accesses, 2));
    // Sort from high -> low
    inst_sorter.sort_by(|a, b| b.cmp(a));

    let pairwise_num_instances = 1
      + if total_num_phy_mem_accesses > 0 { 1 } else { 0 }
      + if total_num_vir_mem_accesses > 0 { 1 } else { 0 };
    let inst_sorter = &inst_sorter[..pairwise_num_instances];
    // index[i] = j => the original jth entry should now be at the ith position
    let index: Vec<usize> = inst_sorter.iter().map(|i| i.index).collect();
    let pairwise_check_inst_unsorted = pairwise_check_inst.clone();
    pairwise_check_inst.sort(pairwise_num_instances, &index);

    timer_sort.stop();

    // --
    // CHALLENGES AND WITNESSES FOR PERMUTATION
    // --
    let timer_gen = Timer::new("witness_gen");
    // Block
    let timer_sec_gen = Timer::new("block_witness_gen");
    let (
      comb_tau,
      comb_r,
      perm_w0_prover,
      // perm_exec
      perm_exec_w2_prover,
      perm_exec_comm_w2_list,
      perm_exec_w3_prover,
      perm_exec_comm_w3_list,
      perm_exec_w3_shifted_prover, // shifted by W3_WIDTH
      perm_exec_comm_w3_shifted,
      // input_block_w2 | phy_mem_block_w2 | vir_mem_block_w2
      block_w2_prover,
      block_comm_w2_list,
      // block_w3
      block_w3_prover,
      block_comm_w3_list,
      block_w3_shifted_prover, // shifted by W3_WIDTH
      block_comm_w3_list_shifted,
    ) = {
      let comb_tau = transcript.challenge_scalar(b"challenge_tau");
      let comb_r = transcript.challenge_scalar(b"challenge_r");

      // PERM_W0
      // w0 is (tau, r, r^2, ...) for the first 2 * num_inputs_unpadded entries
      // set the first entry to 1 for multiplication and later revert it to tau
      let perm_w0 = {
        let mut perm_w0 = vec![comb_tau];
        let mut r_tmp = comb_r;
        for _ in 1..2 * num_inputs_unpadded {
          perm_w0.push(r_tmp);
          r_tmp *= comb_r;
        }
        perm_w0.extend(vec![ZERO; num_ios - 2 * num_inputs_unpadded]);
        perm_w0
      };
      // create a multilinear polynomial using the supplied assignment for variables
      let perm_poly_w0 = DensePolynomial::new(perm_w0.clone());
      // produce a commitment to the satisfying assignment
      let (perm_comm_w0, _blinds_vars) = perm_poly_w0.commit(&vars_gens.gens_pc, None);
      // add the commitment to the prover's transcript
      perm_comm_w0.append_to_transcript(b"poly_commitment", transcript);

      // PERM_EXEC
      // w2 is _, _, ZO, r * i1, r^2 * i2, r^3 * i3, ...
      // where ZO * r^n = r^n * o0 + r^(n + 1) * o1, ...,
      // are used by the consistency check
      let perm_exec_w2 = {
        let mut perm_exec_w2: Vec<Vec<Scalar>> = exec_inputs_list
          .iter()
          .map(|input| {
            [
              vec![ZERO; 3],
              (1..2 * num_inputs_unpadded - 2)
                .map(|j| perm_w0[j] * input[j + 2])
                .collect(),
              vec![ZERO; num_ios - 2 * num_inputs_unpadded],
            ]
            .concat()
          })
          .collect();
        for q in 0..consis_num_proofs {
          perm_exec_w2[q][0] = exec_inputs_list[q][0];
          perm_exec_w2[q][1] = exec_inputs_list[q][0];
          for i in 0..num_inputs_unpadded - 1 {
            let perm = if i == 0 { ONE } else { perm_w0[i] };
            perm_exec_w2[q][0] += perm * exec_inputs_list[q][2 + i];
            perm_exec_w2[q][2] += perm * exec_inputs_list[q][2 + (num_inputs_unpadded - 1) + i];
          }
          perm_exec_w2[q][0] *= exec_inputs_list[q][0];
          let ZO = perm_exec_w2[q][2];
          perm_exec_w2[q][1] += ZO;
          perm_exec_w2[q][1] *= exec_inputs_list[q][0];
        }
        perm_exec_w2
      };
      // w3 is [v, x, pi, D]
      let perm_exec_w3 = {
        let mut perm_exec_w3: Vec<Vec<Scalar>> = vec![Vec::new(); consis_num_proofs];
        for q in (0..consis_num_proofs).rev() {
          perm_exec_w3[q] = vec![ZERO; 8];
          perm_exec_w3[q][0] = exec_inputs_list[q][0];
          perm_exec_w3[q][1] = perm_exec_w3[q][0]
            * (comb_tau
              - perm_exec_w2[q][3..].iter().fold(ZERO, |a, b| a + b)
              - exec_inputs_list[q][2]);
          perm_exec_w3[q][4] = perm_exec_w2[q][0];
          perm_exec_w3[q][5] = perm_exec_w2[q][1];
          if q != consis_num_proofs - 1 {
            perm_exec_w3[q][3] =
              perm_exec_w3[q][1] * (perm_exec_w3[q + 1][2] + ONE - perm_exec_w3[q + 1][0]);
          } else {
            perm_exec_w3[q][3] = perm_exec_w3[q][1];
          }

          perm_exec_w3[q][2] = perm_exec_w3[q][0] * perm_exec_w3[q][3];
        }
        perm_exec_w3
      };
      // commit the witnesses and inputs separately instance-by-instance
      let (
        perm_exec_poly_w2,
        perm_exec_comm_w2,
        perm_exec_poly_w3,
        perm_exec_comm_w3,
        perm_exec_poly_w3_shifted,
        perm_exec_comm_w3_shifted,
      ) = {
        let (perm_exec_poly_w2, perm_exec_comm_w2) = {
          // Flatten the witnesses into a Q_i * X list
          let w2_list_p = perm_exec_w2.clone().into_iter().flatten().collect();
          // create a multilinear polynomial using the supplied assignment for variables
          let perm_exec_poly_w2 = DensePolynomial::new(w2_list_p);

          // produce a commitment to the satisfying assignment
          let (perm_exec_comm_w2, _blinds_vars) =
            perm_exec_poly_w2.commit(&vars_gens.gens_pc, None);

          // add the commitment to the prover's transcript
          perm_exec_comm_w2.append_to_transcript(b"poly_commitment", transcript);
          (perm_exec_poly_w2, perm_exec_comm_w2)
        };

        let (perm_exec_poly_w3, perm_exec_comm_w3) = {
          // Flatten the witnesses into a Q_i * X list
          let w3_list_p = perm_exec_w3.clone().into_iter().flatten().collect();
          // create a multilinear polynomial using the supplied assignment for variables
          let perm_exec_poly_w3 = DensePolynomial::new(w3_list_p);

          // produce a commitment to the satisfying assignment
          let (perm_exec_comm_w3, _blinds_vars) =
            perm_exec_poly_w3.commit(&vars_gens.gens_pc, None);

          // add the commitment to the prover's transcript
          perm_exec_comm_w3.append_to_transcript(b"poly_commitment", transcript);
          (perm_exec_poly_w3, perm_exec_comm_w3)
        };

        let (perm_exec_poly_w3_shifted, perm_exec_comm_w3_shifted) = {
          // Flatten the witnesses into a Q_i * X list
          let w3_list_p = [
            perm_exec_w3[1..]
              .to_vec()
              .clone()
              .into_iter()
              .flatten()
              .collect(),
            vec![ZERO; 8],
          ]
          .concat();
          // create a multilinear polynomial using the supplied assignment for variables
          let perm_exec_poly_w3_shifted = DensePolynomial::new(w3_list_p);

          // produce a commitment to the satisfying assignment
          let (perm_exec_comm_w3_shifted, _blinds_vars) =
            perm_exec_poly_w3_shifted.commit(&vars_gens.gens_pc, None);

          // add the commitment to the prover's transcript
          perm_exec_comm_w3_shifted.append_to_transcript(b"poly_commitment", transcript);
          (perm_exec_poly_w3_shifted, perm_exec_comm_w3_shifted)
        };

        (
          perm_exec_poly_w2,
          perm_exec_comm_w2,
          perm_exec_poly_w3,
          perm_exec_comm_w3,
          perm_exec_poly_w3_shifted,
          perm_exec_comm_w3_shifted,
        )
      };

      // INPUT_BLOCK_W2 | PHY_MEM_BLOCK_W2 & VIR_MEM_BLOCK_W2
      // BLOCK_W3
      //           INPUT      PHY    VIR
      // w3 is [v, x, pi, D, pi, D, pi, D]
      let mut block_w3: Vec<Vec<Vec<Scalar>>> = Vec::new();
      let (block_w2_prover, block_comm_w2_list) = {
        let mut block_w2 = Vec::new();
        let block_w2_size_list: Vec<usize> = (0..block_num_instances)
          .map(|i| {
            (2 * num_inputs_unpadded + 2 * block_num_phy_ops[i] + 4 * block_num_vir_ops[i])
              .next_power_of_two()
          })
          .collect();

        // PHY_MEM
        // w2 is (MR, MC, MR, MC, MR, MC, ...)
        // w3 is (V, X, PI, D)
        let V_PA = |i: usize| 2 * i;
        let V_PD = |i: usize| 2 * i + 1;
        let V_PMR = |i: usize| 2 * num_inputs_unpadded + 2 * i;
        let V_PMC = |i: usize| 2 * num_inputs_unpadded + 2 * i + 1;
        // VIR_MEM
        // w2 is (MR1, MR2, MR3, MC, MR1, MR2, MR3, MC, ...)
        // w3 is (V, X, PI, D)
        let V_VA = |b: usize, i: usize| 2 * block_num_phy_ops[b] + 4 * i;
        let V_VD = |b: usize, i: usize| 2 * block_num_phy_ops[b] + 4 * i + 1;
        let V_VL = |b: usize, i: usize| 2 * block_num_phy_ops[b] + 4 * i + 2;
        let V_VT = |b: usize, i: usize| 2 * block_num_phy_ops[b] + 4 * i + 3;
        let V_VMR1 =
          |b: usize, i: usize| 2 * num_inputs_unpadded + 2 * block_num_phy_ops[b] + 4 * i;
        let V_VMR2 =
          |b: usize, i: usize| 2 * num_inputs_unpadded + 2 * block_num_phy_ops[b] + 4 * i + 1;
        let V_VMR3 =
          |b: usize, i: usize| 2 * num_inputs_unpadded + 2 * block_num_phy_ops[b] + 4 * i + 2;
        let V_VMC =
          |b: usize, i: usize| 2 * num_inputs_unpadded + 2 * block_num_phy_ops[b] + 4 * i + 3;

        for p in 0..block_num_instances {
          block_w2.push(vec![Vec::new(); block_num_proofs[p]]);
          block_w3.push(vec![Vec::new(); block_num_proofs[p]]);
          for q in (0..block_num_proofs[p]).rev() {
            let V_CNST = block_vars_mat[p][q][0];
            // For INPUT
            block_w2[p][q] = vec![ZERO; block_w2_size_list[p]];

            block_w2[p][q][0] = block_vars_mat[p][q][0];
            block_w2[p][q][1] = block_vars_mat[p][q][0];
            for i in 1..2 * (num_inputs_unpadded - 1) {
              block_w2[p][q][2 + i] += perm_w0[i] * block_vars_mat[p][q][i + 2];
            }
            for i in 0..num_inputs_unpadded - 1 {
              let perm = if i == 0 { ONE } else { perm_w0[i] };
              block_w2[p][q][0] += perm * block_vars_mat[p][q][2 + i];
              block_w2[p][q][2] += perm * block_vars_mat[p][q][2 + (num_inputs_unpadded - 1) + i];
            }
            block_w2[p][q][0] *= block_vars_mat[p][q][0];
            let ZO = block_w2[p][q][2];
            block_w2[p][q][1] += ZO;
            block_w2[p][q][1] *= block_vars_mat[p][q][0];
            block_w3[p][q] = vec![ZERO; 8];
            block_w3[p][q][0] = block_vars_mat[p][q][0];
            block_w3[p][q][1] = block_w3[p][q][0]
              * (comb_tau
                - block_w2[p][q][3..].iter().fold(ZERO, |a, b| a + b)
                - block_vars_mat[p][q][2]);
            if q != block_num_proofs[p] - 1 {
              block_w3[p][q][3] =
                block_w3[p][q][1] * (block_w3[p][q + 1][2] + ONE - block_w3[p][q + 1][0]);
            } else {
              block_w3[p][q][3] = block_w3[p][q][1];
            }
            block_w3[p][q][2] = block_w3[p][q][0] * block_w3[p][q][3];

            // For PHY
            // Compute PMR, PMC
            for i in 0..block_num_phy_ops[p] {
              // PMR = r * PD
              block_w2[p][q][V_PMR(i)] = comb_r * block_vars_mat[p][q][io_width + V_PD(i)];
              // PMC = (1 or PMC[i-1]) * (tau - PA - PMR)
              let t = if i == 0 {
                V_CNST
              } else {
                block_w2[p][q][V_PMC(i - 1)]
              };
              block_w2[p][q][V_PMC(i)] = t
                * (comb_tau - block_vars_mat[p][q][io_width + V_PA(i)] - block_w2[p][q][V_PMR(i)]);
            }
            // Compute x
            let px = if block_num_phy_ops[p] == 0 {
              V_CNST
            } else {
              block_w2[p][q][V_PMC(block_num_phy_ops[p] - 1)]
            };
            // Compute D and pi
            if q != block_num_proofs[p] - 1 {
              block_w3[p][q][5] = px * (block_w3[p][q + 1][4] + ONE - block_w3[p][q + 1][0]);
            } else {
              block_w3[p][q][5] = px;
            }
            block_w3[p][q][4] = V_CNST * block_w3[p][q][5];

            // For VIR
            // Compute VMR1, VMR2, VMR3, VMC
            for i in 0..block_num_vir_ops[p] {
              // VMR1 = r * VD
              block_w2[p][q][V_VMR1(p, i)] = comb_r * block_vars_mat[p][q][io_width + V_VD(p, i)];
              // VMR2 = r^2 * VL
              block_w2[p][q][V_VMR2(p, i)] =
                comb_r * comb_r * block_vars_mat[p][q][io_width + V_VL(p, i)];
              // VMR1 = r^3 * VT
              block_w2[p][q][V_VMR3(p, i)] =
                comb_r * comb_r * comb_r * block_vars_mat[p][q][io_width + V_VT(p, i)];
              // VMC = (1 or VMC[i-1]) * (tau - VA - VMR1 - VMR2 - VMR3)
              let t = if i == 0 {
                V_CNST
              } else {
                block_w2[p][q][V_VMC(p, i - 1)]
              };
              block_w2[p][q][V_VMC(p, i)] = t
                * (comb_tau
                  - block_vars_mat[p][q][io_width + V_VA(p, i)]
                  - block_w2[p][q][V_VMR1(p, i)]
                  - block_w2[p][q][V_VMR2(p, i)]
                  - block_w2[p][q][V_VMR3(p, i)]);
            }
            // Compute x
            let vx = if block_num_vir_ops[p] == 0 {
              V_CNST
            } else {
              block_w2[p][q][V_VMC(p, block_num_vir_ops[p] - 1)]
            };
            // Compute D and pi
            if q != block_num_proofs[p] - 1 {
              block_w3[p][q][7] = vx * (block_w3[p][q + 1][6] + ONE - block_w3[p][q + 1][0]);
            } else {
              block_w3[p][q][7] = vx;
            }
            block_w3[p][q][6] = V_CNST * block_w3[p][q][7];
          }
        }

        // commit the witnesses and inputs separately instance-by-instance
        let mut block_poly_w2_list = Vec::new();
        let mut block_comm_w2_list = Vec::new();

        for p in 0..block_num_instances {
          let (block_poly_w2, block_comm_w2) = {
            // Flatten the witnesses into a Q_i * X list
            let w2_list_p = block_w2[p].clone().into_iter().flatten().collect();
            // create a multilinear polynomial using the supplied assignment for variables
            let block_poly_w2 = DensePolynomial::new(w2_list_p);
            // produce a commitment to the satisfying assignment
            let (block_comm_w2, _blinds_vars) = block_poly_w2.commit(&vars_gens.gens_pc, None);

            // add the commitment to the prover's transcript
            block_comm_w2.append_to_transcript(b"poly_commitment", transcript);
            (block_poly_w2, block_comm_w2)
          };
          block_poly_w2_list.push(block_poly_w2);
          block_comm_w2_list.push(block_comm_w2);
        }

        let block_w2_prover = ProverWitnessSecInfo::new(block_w2.clone(), block_poly_w2_list);
        (block_w2_prover, block_comm_w2_list)
      };

      let (
        block_poly_w3_list,
        block_comm_w3_list,
        block_poly_w3_list_shifted,
        block_comm_w3_list_shifted,
      ) = {
        let mut block_poly_w3_list = Vec::new();
        let mut block_comm_w3_list = Vec::new();
        let mut block_poly_w3_list_shifted = Vec::new();
        let mut block_comm_w3_list_shifted = Vec::new();

        for p in 0..block_num_instances {
          let (block_poly_w3, block_comm_w3) = {
            // Flatten the witnesses into a Q_i * X list
            let w3_list_p = block_w3[p].clone().into_iter().flatten().collect();
            // create a multilinear polynomial using the supplied assignment for variables
            let block_poly_w3 = DensePolynomial::new(w3_list_p);

            // produce a commitment to the satisfying assignment
            let (block_comm_w3, _blinds_vars) = block_poly_w3.commit(&vars_gens.gens_pc, None);

            // add the commitment to the prover's transcript
            block_comm_w3.append_to_transcript(b"poly_commitment", transcript);
            (block_poly_w3, block_comm_w3)
          };

          let (block_poly_w3_shifted, block_comm_w3_shifted) = {
            // Flatten the witnesses into a Q_i * X list
            let w3_list_p = [
              block_w3[p][1..]
                .to_vec()
                .clone()
                .into_iter()
                .flatten()
                .collect(),
              vec![ZERO; 8],
            ]
            .concat();
            // create a multilinear polynomial using the supplied assignment for variables
            let block_poly_w3_shifted = DensePolynomial::new(w3_list_p);

            // produce a commitment to the satisfying assignment
            let (block_comm_w3_shifted, _blinds_vars) =
              block_poly_w3_shifted.commit(&vars_gens.gens_pc, None);

            // add the commitment to the prover's transcript
            block_comm_w3_shifted.append_to_transcript(b"poly_commitment", transcript);
            (block_poly_w3_shifted, block_comm_w3_shifted)
          };
          block_poly_w3_list.push(block_poly_w3);
          block_comm_w3_list.push(block_comm_w3);
          block_poly_w3_list_shifted.push(block_poly_w3_shifted);
          block_comm_w3_list_shifted.push(block_comm_w3_shifted);
        }

        (
          block_poly_w3_list,
          block_comm_w3_list,
          block_poly_w3_list_shifted,
          block_comm_w3_list_shifted,
        )
      };

      let perm_w0_prover = ProverWitnessSecInfo::new(vec![vec![perm_w0]], vec![perm_poly_w0]);
      let perm_exec_w2_prover =
        ProverWitnessSecInfo::new(vec![perm_exec_w2], vec![perm_exec_poly_w2]);
      let perm_exec_w3_prover =
        ProverWitnessSecInfo::new(vec![perm_exec_w3.clone()], vec![perm_exec_poly_w3]);
      let perm_exec_w3_shifted_prover = ProverWitnessSecInfo::new(
        vec![[perm_exec_w3[1..].to_vec(), vec![vec![ZERO; 8]]].concat()],
        vec![perm_exec_poly_w3_shifted],
      );

      let block_w3_prover = ProverWitnessSecInfo::new(block_w3.clone(), block_poly_w3_list);
      let block_w3_shifted_prover = ProverWitnessSecInfo::new(
        block_w3
          .iter()
          .map(|i| [i[1..].to_vec(), vec![vec![ZERO; 8]]].concat())
          .collect(),
        block_poly_w3_list_shifted,
      );

      (
        comb_tau,
        comb_r,
        perm_w0_prover,
        perm_exec_w2_prover,
        perm_exec_comm_w2,
        perm_exec_w3_prover,
        perm_exec_comm_w3,
        perm_exec_w3_shifted_prover,
        perm_exec_comm_w3_shifted,
        block_w2_prover,
        block_comm_w2_list,
        block_w3_prover,
        block_comm_w3_list,
        block_w3_shifted_prover,
        block_comm_w3_list_shifted,
      )
    };
    timer_sec_gen.stop();

    // Initial Physical Memory-as-a-whole
    let timer_sec_gen = Timer::new("init_phy_mem_witness_gen");
    let (
      init_phy_mem_w2_prover,
      init_phy_mem_comm_w2,
      init_phy_mem_w3_prover,
      init_phy_mem_comm_w3,
      init_phy_mem_w3_shifted_prover,
      init_phy_mem_comm_w3_shifted,
    ) = Self::mem_gen::<INIT_PHY_MEM_WIDTH>(
      total_num_init_phy_mem_accesses,
      &init_phy_mems_list,
      &comb_r,
      &comb_tau,
      &vars_gens,
      transcript,
    );
    timer_sec_gen.stop();

    // Initial Virtual Memory-as-a-whole
    let timer_sec_gen = Timer::new("init_vir_mem_witness_gen");
    let (
      init_vir_mem_w2_prover,
      init_vir_mem_comm_w2,
      init_vir_mem_w3_prover,
      init_vir_mem_comm_w3,
      init_vir_mem_w3_shifted_prover,
      init_vir_mem_comm_w3_shifted,
    ) = Self::mem_gen::<INIT_VIR_MEM_WIDTH>(
      total_num_init_vir_mem_accesses,
      &init_vir_mems_list,
      &comb_r,
      &comb_tau,
      &vars_gens,
      transcript,
    );
    timer_sec_gen.stop();

    // Physical Memory-as-a-whole
    let timer_sec_gen = Timer::new("phy_mem_addr_witness_gen");
    let (
      phy_mem_addr_w2_prover,
      phy_mem_addr_comm_w2,
      phy_mem_addr_w3_prover,
      phy_mem_addr_comm_w3,
      phy_mem_addr_w3_shifted_prover,
      phy_mem_addr_comm_w3_shifted,
    ) = Self::mem_gen::<PHY_MEM_WIDTH>(
      total_num_phy_mem_accesses,
      &addr_phy_mems_list,
      &comb_r,
      &comb_tau,
      &vars_gens,
      transcript,
    );
    timer_sec_gen.stop();

    // Virtual Memory-as-a-whole
    let timer_sec_gen = Timer::new("vir_mem_addr_witness_gen");
    let (
      vir_mem_addr_w2_prover,
      vir_mem_addr_comm_w2,
      vir_mem_addr_w3_prover,
      vir_mem_addr_comm_w3,
      vir_mem_addr_w3_shifted_prover,
      vir_mem_addr_comm_w3_shifted,
    ) = {
      if total_num_vir_mem_accesses > 0 {
        // vir_mem_addr_w2 is (I, O, ZO, r * data, r^2 * ls, r^3 * ts)
        // where ZO = 0,

        let mut vir_mem_addr_w2 = Vec::new();
        for q in 0..total_num_vir_mem_accesses {
          vir_mem_addr_w2.push(vec![ZERO; VIR_MEM_WIDTH]);
          vir_mem_addr_w2[q][3] = comb_r * addr_vir_mems_list[q][3];
          vir_mem_addr_w2[q][4] = comb_r * comb_r * addr_vir_mems_list[q][4];
          vir_mem_addr_w2[q][5] = comb_r * comb_r * comb_r * addr_vir_mems_list[q][5];
        }
        // vir_mem_addr_w3 is (v, x, pi, D, I, O)
        // where I = v * (v + addr + r * data + r^2 * ls + r^3 * ts),
        //       O = v * v = v
        // are used by (dummy) consistency check
        let mut vir_mem_addr_w3 = vec![vec![ZERO; W3_WIDTH]; total_num_vir_mem_accesses];
        for q in (0..total_num_vir_mem_accesses).rev() {
          // v
          vir_mem_addr_w3[q][0] = addr_vir_mems_list[q][0];
          // x = v * (tau - addr - r * data - r^2 * ls - r^3 * ts)
          vir_mem_addr_w3[q][1] = addr_vir_mems_list[q][0]
            * (comb_tau
              - addr_vir_mems_list[q][2]
              - vir_mem_addr_w2[q][3]
              - vir_mem_addr_w2[q][4]
              - vir_mem_addr_w2[q][5]);
          // pi and D
          if q != total_num_vir_mem_accesses - 1 {
            vir_mem_addr_w3[q][3] =
              vir_mem_addr_w3[q][1] * (vir_mem_addr_w3[q + 1][2] + ONE - vir_mem_addr_w3[q + 1][0]);
          } else {
            vir_mem_addr_w3[q][3] = vir_mem_addr_w3[q][1];
          }
          vir_mem_addr_w3[q][2] = vir_mem_addr_w3[q][0] * vir_mem_addr_w3[q][3];
          vir_mem_addr_w3[q][4] = addr_vir_mems_list[q][0]
            * (addr_vir_mems_list[q][0]
              + addr_vir_mems_list[q][2]
              + vir_mem_addr_w2[q][3]
              + vir_mem_addr_w2[q][4]
              + vir_mem_addr_w2[q][5]);
          vir_mem_addr_w3[q][5] = addr_vir_mems_list[q][0];
        }

        let (
          vir_mem_addr_poly_w2,
          vir_mem_addr_comm_w2,
          vir_mem_addr_poly_w3,
          vir_mem_addr_comm_w3,
          vir_mem_addr_poly_w3_shifted,
          vir_mem_addr_comm_w3_shifted,
        ) = {
          let (vir_mem_addr_poly_w2, vir_mem_addr_comm_w2) = {
            // Flatten the witnesses into a Q_i * X list
            let w2_list_p = vir_mem_addr_w2.clone().into_iter().flatten().collect();
            // create a multilinear polynomial using the supplied assignment for variables
            let vir_mem_addr_poly_w2 = DensePolynomial::new(w2_list_p);

            // produce a commitment to the satisfying assignment
            let (vir_mem_addr_comm_w2, _blinds_vars) =
              vir_mem_addr_poly_w2.commit(&vars_gens.gens_pc, None);

            // add the commitment to the prover's transcript
            vir_mem_addr_comm_w2.append_to_transcript(b"poly_commitment", transcript);
            (vir_mem_addr_poly_w2, vir_mem_addr_comm_w2)
          };

          let (vir_mem_addr_poly_w3, vir_mem_addr_comm_w3) = {
            // Flatten the witnesses into a Q_i * X list
            let w3_list_p = vir_mem_addr_w3.clone().into_iter().flatten().collect();
            // create a multilinear polynomial using the supplied assignment for variables
            let vir_mem_addr_poly_w3 = DensePolynomial::new(w3_list_p);

            // produce a commitment to the satisfying assignment
            let (vir_mem_addr_comm_w3, _blinds_vars) =
              vir_mem_addr_poly_w3.commit(&vars_gens.gens_pc, None);

            // add the commitment to the prover's transcript
            vir_mem_addr_comm_w3.append_to_transcript(b"poly_commitment", transcript);
            (vir_mem_addr_poly_w3, vir_mem_addr_comm_w3)
          };

          let (vir_mem_addr_poly_w3_shifted, vir_mem_addr_comm_w3_shifted) = {
            // Flatten the witnesses into a Q_i * X list
            let w3_list_p = [
              vir_mem_addr_w3[1..]
                .to_vec()
                .clone()
                .into_iter()
                .flatten()
                .collect(),
              vec![ZERO; W3_WIDTH],
            ]
            .concat();
            // create a multilinear polynomial using the supplied assignment for variables
            let vir_mem_addr_poly_w3_shifted = DensePolynomial::new(w3_list_p);

            // produce a commitment to the satisfying assignment
            let (vir_mem_addr_comm_w3_shifted, _blinds_vars) =
              vir_mem_addr_poly_w3_shifted.commit(&vars_gens.gens_pc, None);

            // add the commitment to the prover's transcript
            vir_mem_addr_comm_w3_shifted.append_to_transcript(b"poly_commitment", transcript);
            (vir_mem_addr_poly_w3_shifted, vir_mem_addr_comm_w3_shifted)
          };

          (
            vir_mem_addr_poly_w2,
            vir_mem_addr_comm_w2,
            vir_mem_addr_poly_w3,
            vir_mem_addr_comm_w3,
            vir_mem_addr_poly_w3_shifted,
            vir_mem_addr_comm_w3_shifted,
          )
        };

        let vir_mem_addr_w2_prover =
          ProverWitnessSecInfo::new(vec![vir_mem_addr_w2], vec![vir_mem_addr_poly_w2]);
        let vir_mem_addr_w3_prover =
          ProverWitnessSecInfo::new(vec![vir_mem_addr_w3.clone()], vec![vir_mem_addr_poly_w3]);
        let vir_mem_addr_w3_shifted_prover = ProverWitnessSecInfo::new(
          vec![[vir_mem_addr_w3[1..].to_vec(), vec![vec![ZERO; W3_WIDTH]]].concat()],
          vec![vir_mem_addr_poly_w3_shifted],
        );

        (
          vir_mem_addr_w2_prover,
          vir_mem_addr_comm_w2,
          vir_mem_addr_w3_prover,
          vir_mem_addr_comm_w3,
          vir_mem_addr_w3_shifted_prover,
          vir_mem_addr_comm_w3_shifted,
        )
      } else {
        (
          ProverWitnessSecInfo::dummy(),
          PolyCommitment::empty(),
          ProverWitnessSecInfo::dummy(),
          PolyCommitment::empty(),
          ProverWitnessSecInfo::dummy(),
          PolyCommitment::empty(),
        )
      }
    };
    timer_sec_gen.stop();

    timer_gen.stop();

    // --
    // WITNESS COMMITMENTS
    // --
    let timer_commit = Timer::new("input_commit");
    let (block_poly_vars_list, block_comm_vars_list, exec_poly_inputs, exec_comm_inputs) = {
      // commit the witnesses and inputs separately instance-by-instance
      let mut block_poly_vars_list = Vec::new();
      let mut block_comm_vars_list = Vec::new();

      for p in 0..block_num_instances {
        let (block_poly_vars, block_comm_vars) = {
          // Flatten the witnesses into a Q_i * X list
          let vars_list_p: Vec<Scalar> = block_vars_mat[p].clone().into_iter().flatten().collect();
          // create a multilinear polynomial using the supplied assignment for variables
          let block_poly_vars = DensePolynomial::new(vars_list_p);

          // produce a commitment to the satisfying assignment
          let (block_comm_vars, _blinds_vars) = block_poly_vars.commit(&vars_gens.gens_pc, None);

          // add the commitment to the prover's transcript
          block_comm_vars.append_to_transcript(b"poly_commitment", transcript);
          (block_poly_vars, block_comm_vars)
        };
        block_poly_vars_list.push(block_poly_vars);
        block_comm_vars_list.push(block_comm_vars);
      }

      let (exec_poly_inputs, exec_comm_inputs) = {
        let exec_inputs = exec_inputs_list.clone().into_iter().flatten().collect();
        // create a multilinear polynomial using the supplied assignment for variables
        let exec_poly_inputs = DensePolynomial::new(exec_inputs);

        // produce a commitment to the satisfying assignment
        let (exec_comm_inputs, _blinds_inputs) = exec_poly_inputs.commit(&vars_gens.gens_pc, None);

        // add the commitment to the prover's transcript
        exec_comm_inputs.append_to_transcript(b"poly_commitment", transcript);
        (exec_poly_inputs, exec_comm_inputs)
      };

      (
        block_poly_vars_list,
        block_comm_vars_list,
        vec![exec_poly_inputs],
        vec![exec_comm_inputs],
      )
    };
    let (poly_init_phy_mems, _comm_init_phy_mems) = {
      if total_num_init_phy_mem_accesses > 0 {
        let (poly_init_mems, comm_init_mems) = {
          let init_mems = init_phy_mems_list.clone().into_iter().flatten().collect();
          // create a multilinear polynomial using the supplied assignment for variables
          let poly_init_mems = DensePolynomial::new(init_mems);

          // produce a commitment to the satisfying assignment
          let (comm_init_mems, _blinds_inputs) = poly_init_mems.commit(&vars_gens.gens_pc, None);

          // add the commitment to the prover's transcript
          comm_init_mems.append_to_transcript(b"poly_commitment", transcript);
          (poly_init_mems, comm_init_mems)
        };
        (vec![poly_init_mems], vec![comm_init_mems])
      } else {
        (Vec::new(), Vec::new())
      }
    };
    let (poly_init_vir_mems, _comm_init_vir_mems) = {
      if total_num_init_vir_mem_accesses > 0 {
        let (poly_init_mems, comm_init_mems) = {
          let init_mems = init_vir_mems_list.clone().into_iter().flatten().collect();
          // create a multilinear polynomial using the supplied assignment for variables
          let poly_init_mems = DensePolynomial::new(init_mems);

          // produce a commitment to the satisfying assignment
          let (comm_init_mems, _blinds_inputs) = poly_init_mems.commit(&vars_gens.gens_pc, None);

          // add the commitment to the prover's transcript
          comm_init_mems.append_to_transcript(b"poly_commitment", transcript);
          (poly_init_mems, comm_init_mems)
        };
        (vec![poly_init_mems], vec![comm_init_mems])
      } else {
        (Vec::new(), Vec::new())
      }
    };

    let (
      addr_poly_phy_mems,
      addr_comm_phy_mems,
      addr_phy_mems_shifted_prover,
      addr_comm_phy_mems_shifted,
    ) = {
      if total_num_phy_mem_accesses > 0 {
        let (addr_poly_phy_mems, addr_comm_phy_mems) = {
          let addr_phy_mems = addr_phy_mems_list.clone().into_iter().flatten().collect();
          // create a multilinear polynomial using the supplied assignment for variables
          let addr_poly_phy_mems = DensePolynomial::new(addr_phy_mems);

          // produce a commitment to the satisfying assignment
          let (addr_comm_phy_mems, _blinds_inputs) =
            addr_poly_phy_mems.commit(&vars_gens.gens_pc, None);

          // add the commitment to the prover's transcript
          addr_comm_phy_mems.append_to_transcript(b"poly_commitment", transcript);
          (addr_poly_phy_mems, addr_comm_phy_mems)
        };
        // Remove the first entry and shift the remaining entries up by one
        // Used later by coherence check
        let (addr_phy_mems_shifted_prover, addr_comm_phy_mems_shifted) = {
          let addr_phy_mems_shifted = [
            addr_phy_mems_list[1..]
              .to_vec()
              .clone()
              .into_iter()
              .flatten()
              .collect(),
            vec![ZERO; PHY_MEM_WIDTH],
          ]
          .concat();
          // create a multilinear polynomial using the supplied assignment for variables
          let addr_poly_phy_mems_shifted = DensePolynomial::new(addr_phy_mems_shifted);

          // produce a commitment to the satisfying assignment
          let (addr_comm_phy_mems_shifted, _blinds_inputs) =
            addr_poly_phy_mems_shifted.commit(&vars_gens.gens_pc, None);

          // add the commitment to the prover's transcript
          addr_comm_phy_mems_shifted.append_to_transcript(b"poly_commitment", transcript);

          let addr_phy_mems_shifted_prover = ProverWitnessSecInfo::new(
            vec![[
              addr_phy_mems_list[1..].to_vec(),
              vec![vec![ZERO; PHY_MEM_WIDTH]],
            ]
            .concat()],
            vec![addr_poly_phy_mems_shifted],
          );

          (addr_phy_mems_shifted_prover, addr_comm_phy_mems_shifted)
        };
        (
          vec![addr_poly_phy_mems],
          addr_comm_phy_mems,
          addr_phy_mems_shifted_prover,
          addr_comm_phy_mems_shifted,
        )
      } else {
        (
          Vec::new(),
          PolyCommitment::empty(),
          ProverWitnessSecInfo::dummy(),
          PolyCommitment::empty(),
        )
      }
    };
    let (
      addr_poly_vir_mems,
      addr_comm_vir_mems,
      addr_vir_mems_shifted_prover,
      addr_comm_vir_mems_shifted,
      addr_ts_bits_prover,
      addr_comm_ts_bits,
    ) = {
      if total_num_vir_mem_accesses > 0 {
        let (addr_poly_vir_mems, addr_comm_vir_mems) = {
          let addr_vir_mems = addr_vir_mems_list.clone().into_iter().flatten().collect();
          // create a multilinear polynomial using the supplied assignment for variables
          let addr_poly_vir_mems = DensePolynomial::new(addr_vir_mems);

          // produce a commitment to the satisfying assignment
          let (addr_comm_vir_mems, _blinds_inputs) =
            addr_poly_vir_mems.commit(&vars_gens.gens_pc, None);

          // add the commitment to the prover's transcript
          addr_comm_vir_mems.append_to_transcript(b"poly_commitment", transcript);
          (addr_poly_vir_mems, addr_comm_vir_mems)
        };
        // Remove the first entry and shift the remaining entries up by one
        // Used later by coherence check
        let (addr_vir_mems_shifted_prover, addr_comm_vir_mems_shifted) = {
          let addr_vir_mems_shifted = [
            addr_vir_mems_list[1..]
              .to_vec()
              .clone()
              .into_iter()
              .flatten()
              .collect(),
            vec![ZERO; VIR_MEM_WIDTH],
          ]
          .concat();
          // create a multilinear polynomial using the supplied assignment for variables
          let addr_poly_vir_mems_shifted = DensePolynomial::new(addr_vir_mems_shifted);

          // produce a commitment to the satisfying assignment
          let (addr_comm_vir_mems_shifted, _blinds_inputs) =
            addr_poly_vir_mems_shifted.commit(&vars_gens.gens_pc, None);
          // add the commitment to the prover's transcript
          addr_comm_vir_mems_shifted.append_to_transcript(b"poly_commitment", transcript);

          let addr_vir_mems_shifted_prover = ProverWitnessSecInfo::new(
            vec![[
              addr_vir_mems_list[1..].to_vec(),
              vec![vec![ZERO; VIR_MEM_WIDTH]],
            ]
            .concat()],
            vec![addr_poly_vir_mems_shifted],
          );
          (addr_vir_mems_shifted_prover, addr_comm_vir_mems_shifted)
        };
        let (addr_ts_bits_prover, addr_comm_ts_bits) = {
          let addr_ts_bits = addr_ts_bits_list.clone().into_iter().flatten().collect();
          // create a multilinear polynomial using the supplied assignment for variables
          let addr_poly_ts_bits = DensePolynomial::new(addr_ts_bits);

          // produce a commitment to the satisfying assignment
          let (addr_comm_ts_bits, _blinds_inputs) =
            addr_poly_ts_bits.commit(&vars_gens.gens_pc, None);
          // add the commitment to the prover's transcript
          addr_comm_ts_bits.append_to_transcript(b"poly_commitment", transcript);

          let addr_ts_bits_prover =
            ProverWitnessSecInfo::new(vec![addr_ts_bits_list], vec![addr_poly_ts_bits]);
          (addr_ts_bits_prover, addr_comm_ts_bits)
        };
        (
          vec![addr_poly_vir_mems],
          addr_comm_vir_mems,
          addr_vir_mems_shifted_prover,
          addr_comm_vir_mems_shifted,
          addr_ts_bits_prover,
          addr_comm_ts_bits,
        )
      } else {
        (
          Vec::new(),
          PolyCommitment::empty(),
          ProverWitnessSecInfo::dummy(),
          PolyCommitment::empty(),
          ProverWitnessSecInfo::dummy(),
          PolyCommitment::empty(),
        )
      }
    };
    let block_vars_prover = ProverWitnessSecInfo::new(block_vars_mat, block_poly_vars_list);
    let exec_inputs_prover = ProverWitnessSecInfo::new(vec![exec_inputs_list], exec_poly_inputs);
    let init_phy_mems_prover = if total_num_init_phy_mem_accesses > 0 {
      ProverWitnessSecInfo::new(vec![init_phy_mems_list.clone()], poly_init_phy_mems)
    } else {
      ProverWitnessSecInfo::dummy()
    };
    let init_vir_mems_prover = if total_num_init_vir_mem_accesses > 0 {
      ProverWitnessSecInfo::new(vec![init_vir_mems_list.clone()], poly_init_vir_mems)
    } else {
      ProverWitnessSecInfo::dummy()
    };
    let addr_phy_mems_prover = if total_num_phy_mem_accesses > 0 {
      ProverWitnessSecInfo::new(vec![addr_phy_mems_list.clone()], addr_poly_phy_mems)
    } else {
      ProverWitnessSecInfo::dummy()
    };
    let addr_vir_mems_prover = if total_num_vir_mem_accesses > 0 {
      ProverWitnessSecInfo::new(vec![addr_vir_mems_list.clone()], addr_poly_vir_mems)
    } else {
      ProverWitnessSecInfo::dummy()
    };
    timer_commit.stop();

    // --
    // BLOCK_CORRECTNESS_EXTRACT
    // --
    let timer_proof = Timer::new("Block Correctness Extract");
    let block_wit_secs = vec![
      &block_vars_prover,
      &perm_w0_prover,
      &block_w2_prover,
      &block_w3_prover,
      &block_w3_shifted_prover,
    ];
    let (block_r1cs_sat_proof, block_challenges) = {
      let (proof, block_challenges) = {
        R1CSProof::prove(
          block_num_instances,
          block_max_num_proofs,
          block_num_proofs,
          num_vars,
          &block_num_vars,
          block_wit_secs,
          &block_inst.inst,
          &vars_gens,
          transcript,
          &mut random_tape,
        )
      };

      let proof_encoded: Vec<u8> = bincode::serialize(&proof).unwrap();
      Timer::print(&format!("len_r1cs_sat_proof {:?}", proof_encoded.len()));

      (proof, block_challenges)
    };

    // Final evaluation on BLOCK
    let (block_inst_evals_bound_rp, block_inst_evals_list, block_r1cs_eval_proof_list) = {
      let [rp, _, rx, ry] = block_challenges;
      let timer_eval = Timer::new("eval_sparse_polys");

      // Per instance evaluation is unsorted
      let inst_evals_list = block_inst_unsorted.inst.multi_evaluate(&rx, &ry);
      // RP-bound evaluation is sorted
      let (_, inst_evals_bound_rp) = block_inst.inst.multi_evaluate_bound_rp(&rp, &rx, &ry);
      timer_eval.stop();

      for r in &inst_evals_list {
        r.append_to_transcript(b"ABCr_claim", transcript);
      }
      // Sample random combinations of A, B, C for inst_evals_bound_rp check in the Verifier
      // The random values are not used by the prover, but need to be appended to the transcript
      let _ = transcript.challenge_scalar(b"challenge_c0");
      let _ = transcript.challenge_scalar(b"challenge_c1");
      let _ = transcript.challenge_scalar(b"challenge_c2");

      let r1cs_eval_proof_list = {
        let mut r1cs_eval_proof_list = Vec::new();
        for i in 0..block_comm_list.len() {
          let proof = R1CSEvalProof::prove(
            &block_decomm_list[i].decomm,
            &rx,
            &ry,
            &block_comm_map[i]
              .iter()
              .map(|i| inst_evals_list[*i])
              .collect(),
            &block_gens.gens_r1cs_eval,
            transcript,
            &mut random_tape,
          );
          let proof_encoded: Vec<u8> = bincode::serialize(&proof).unwrap();
          Timer::print(&format!("len_r1cs_eval_proof {:?}", proof_encoded.len()));

          r1cs_eval_proof_list.push(proof);
        }
        r1cs_eval_proof_list
      };

      (
        [
          inst_evals_bound_rp.0,
          inst_evals_bound_rp.1,
          inst_evals_bound_rp.2,
        ],
        inst_evals_list,
        r1cs_eval_proof_list,
      )
    };
    timer_proof.stop();

    // --
    // PAIRWISE_CHECK
    // --
    let timer_proof = Timer::new("Pairwise Check");
    let pairwise_size = [
      consis_num_proofs,
      total_num_phy_mem_accesses,
      total_num_vir_mem_accesses,
    ]
    .iter()
    .max()
    .unwrap()
    .clone();
    let (pairwise_prover, inst_map) = ProverWitnessSecInfo::merge(vec![
      &perm_exec_w3_prover,
      &addr_phy_mems_prover,
      &addr_vir_mems_prover,
    ]);
    let (pairwise_shifted_prover, _) = ProverWitnessSecInfo::merge(vec![
      &perm_exec_w3_shifted_prover,
      &addr_phy_mems_shifted_prover,
      &addr_vir_mems_shifted_prover,
    ]);
    let addr_ts_bits_prover = {
      let mut components = vec![&perm_w0_prover; inst_map.len()];
      for i in 0..inst_map.len() {
        if inst_map[i] == 2 {
          components[i] = &addr_ts_bits_prover;
        }
      }
      ProverWitnessSecInfo::concat(components)
    };
    let pairwise_num_instances = pairwise_prover.w_mat.len();
    let pairwise_num_proofs: Vec<usize> = pairwise_prover.w_mat.iter().map(|i| i.len()).collect();
    let (pairwise_check_r1cs_sat_proof, pairwise_check_challenges) = {
      let (proof, pairwise_check_challenges) = {
        R1CSProof::prove(
          pairwise_num_instances,
          pairwise_size,
          &pairwise_num_proofs,
          max(8, mem_addr_ts_bits_size),
          &vec![max(8, mem_addr_ts_bits_size); pairwise_num_instances],
          vec![
            &pairwise_prover,
            &pairwise_shifted_prover,
            &addr_ts_bits_prover,
          ],
          &pairwise_check_inst.inst,
          &vars_gens,
          transcript,
          &mut random_tape,
        )
      };

      let proof_encoded: Vec<u8> = bincode::serialize(&proof).unwrap();
      Timer::print(&format!("len_r1cs_sat_proof {:?}", proof_encoded.len()));

      (proof, pairwise_check_challenges)
    };

    // Final evaluation on PAIRWISE_CHECK
    let (
      pairwise_check_inst_evals_bound_rp,
      pairwise_check_inst_evals_list,
      pairwise_check_r1cs_eval_proof,
    ) = {
      let [rp, _, rx, ry] = pairwise_check_challenges;
      let timer_eval = Timer::new("eval_sparse_polys");

      // Per instance evaluation is unsorted
      let inst_evals_list = pairwise_check_inst_unsorted.inst.multi_evaluate(&rx, &ry);
      // RP-bound evaluation is sorted
      let (_, inst_evals_bound_rp) = pairwise_check_inst
        .inst
        .multi_evaluate_bound_rp(&rp, &rx, &ry);
      timer_eval.stop();

      for r in &inst_evals_list {
        r.append_to_transcript(b"ABCr_claim", transcript);
      }
      // Sample random combinations of A, B, C for inst_evals_bound_rp check in the Verifier
      // The random values are not used by the prover, but need to be appended to the transcript
      let _ = transcript.challenge_scalar(b"challenge_c0");
      let _ = transcript.challenge_scalar(b"challenge_c1");
      let _ = transcript.challenge_scalar(b"challenge_c2");

      let r1cs_eval_proof = {
        let proof = R1CSEvalProof::prove(
          &pairwise_check_decomm.decomm,
          &rx,
          &ry,
          &inst_evals_list,
          &pairwise_check_gens.gens_r1cs_eval,
          transcript,
          &mut random_tape,
        );

        let proof_encoded: Vec<u8> = bincode::serialize(&proof).unwrap();
        Timer::print(&format!("len_r1cs_eval_proof {:?}", proof_encoded.len()));
        proof
      };

      (
        [
          inst_evals_bound_rp.0,
          inst_evals_bound_rp.1,
          inst_evals_bound_rp.2,
        ],
        inst_evals_list,
        r1cs_eval_proof,
      )
    };
    // Correctness of the shift will be handled in SHIFT_PROOFS
    timer_proof.stop();

    // --
    // PERM_EXEC_ROOT, MEM_ADDR_ROOT
    // --
    let timer_proof = Timer::new("Perm Root");
    let perm_size = [
      consis_num_proofs,
      total_num_init_phy_mem_accesses,
      total_num_init_vir_mem_accesses,
      total_num_phy_mem_accesses,
      total_num_vir_mem_accesses,
    ]
    .iter()
    .max()
    .unwrap()
    .clone();
    let (perm_root_w1_prover, _) = ProverWitnessSecInfo::merge(vec![
      &exec_inputs_prover,
      &init_phy_mems_prover,
      &init_vir_mems_prover,
      &addr_phy_mems_prover,
      &addr_vir_mems_prover,
    ]);
    let (perm_root_w2_prover, _) = ProverWitnessSecInfo::merge(vec![
      &perm_exec_w2_prover,
      &init_phy_mem_w2_prover,
      &init_vir_mem_w2_prover,
      &phy_mem_addr_w2_prover,
      &vir_mem_addr_w2_prover,
    ]);
    let (perm_root_w3_prover, _) = ProverWitnessSecInfo::merge(vec![
      &perm_exec_w3_prover,
      &init_phy_mem_w3_prover,
      &init_vir_mem_w3_prover,
      &phy_mem_addr_w3_prover,
      &vir_mem_addr_w3_prover,
    ]);
    let (perm_root_w3_shifted_prover, _) = ProverWitnessSecInfo::merge(vec![
      &perm_exec_w3_shifted_prover,
      &init_phy_mem_w3_shifted_prover,
      &init_vir_mem_w3_shifted_prover,
      &phy_mem_addr_w3_shifted_prover,
      &vir_mem_addr_w3_shifted_prover,
    ]);
    let perm_root_num_instances = perm_root_w1_prover.w_mat.len();
    let perm_root_num_proofs: Vec<usize> =
      perm_root_w1_prover.w_mat.iter().map(|i| i.len()).collect();
    let (perm_root_r1cs_sat_proof, perm_root_challenges) = {
      let (proof, perm_root_challenges) = {
        R1CSProof::prove(
          perm_root_num_instances,
          perm_size,
          &perm_root_num_proofs,
          num_ios,
          &vec![num_ios; perm_root_num_instances],
          vec![
            &perm_w0_prover,
            &perm_root_w1_prover,
            &perm_root_w2_prover,
            &perm_root_w3_prover,
            &perm_root_w3_shifted_prover,
          ],
          &perm_root_inst.inst,
          &vars_gens,
          transcript,
          &mut random_tape,
        )
      };

      let proof_encoded: Vec<u8> = bincode::serialize(&proof).unwrap();

      Timer::print(&format!("len_r1cs_sat_proof {:?}", proof_encoded.len()));

      (proof, perm_root_challenges)
    };

    // Final evaluation on PERM_ROOT
    let (perm_root_inst_evals, perm_root_r1cs_eval_proof) = {
      let [_, _, rx, ry] = perm_root_challenges;
      let inst = perm_root_inst;
      let timer_eval = Timer::new("eval_sparse_polys");
      let inst_evals = {
        let (Ar, Br, Cr) = inst.inst.evaluate(&rx, &ry);
        Ar.append_to_transcript(b"Ar_claim", transcript);
        Br.append_to_transcript(b"Br_claim", transcript);
        Cr.append_to_transcript(b"Cr_claim", transcript);
        [Ar, Br, Cr]
      };
      timer_eval.stop();

      let r1cs_eval_proof = {
        let proof = R1CSEvalProof::prove(
          &perm_root_decomm.decomm,
          &rx,
          &ry,
          &inst_evals.to_vec(),
          &perm_root_gens.gens_r1cs_eval,
          transcript,
          &mut random_tape,
        );

        let proof_encoded: Vec<u8> = bincode::serialize(&proof).unwrap();
        Timer::print(&format!("len_r1cs_eval_proof {:?}", proof_encoded.len()));
        proof
      };

      (inst_evals, r1cs_eval_proof)
    };
    timer_proof.stop();

    // --
    // PERM_PRODUCT_PROOF
    // --
    let timer_proof = Timer::new("Perm Product");
    // Record the prod of exec, blocks, mem_block, & mem_addr
    let (perm_poly_poly_list, proof_eval_perm_poly_prod_list) = {
      let (perm_poly_w3_prover, inst_map) = {
        let mut components = vec![
          &perm_exec_w3_prover,
          &init_phy_mem_w3_prover,
          &init_vir_mem_w3_prover,
          &phy_mem_addr_w3_prover,
          &vir_mem_addr_w3_prover,
          &block_w3_prover,
        ];
        if max_block_num_phy_ops > 0 {
          components.push(&block_w3_prover);
        }
        if max_block_num_vir_ops > 0 {
          components.push(&block_w3_prover);
        }
        ProverWitnessSecInfo::merge(components)
      };
      let pm_bl_id = 6;
      let vm_bl_id = if max_block_num_phy_ops > 0 { 7 } else { 6 };
      // PHY_MEM_BLOCK takes r = 4, VIR_MEM_BLOCK takes r = 6, everything else takes r = 2
      let perm_poly_poly_list: Vec<Scalar> = (0..inst_map.len())
        .map(|i| {
          let p = &perm_poly_w3_prover.poly_w[i];
          let i = inst_map[i];
          if i == vm_bl_id {
            p[6]
          } else if i == pm_bl_id {
            p[4]
          } else {
            p[2]
          }
        })
        .collect();
      let two_b = vec![ONE, ZERO];
      let four_b = vec![ONE, ZERO, ZERO];
      let six_b = vec![ONE, ONE, ZERO];
      let r_list: Vec<&Vec<Scalar>> = inst_map
        .iter()
        .map(|i| {
          if *i == vm_bl_id {
            &six_b
          } else if *i == pm_bl_id {
            &four_b
          } else {
            &two_b
          }
        })
        .collect();
      let proof_eval_perm_poly_prod_list = PolyEvalProof::prove_batched_instances(
        &perm_poly_w3_prover.poly_w,
        None,
        r_list,
        &perm_poly_poly_list,
        None,
        &vars_gens.gens_pc,
        transcript,
        &mut random_tape,
      );
      (perm_poly_poly_list, proof_eval_perm_poly_prod_list)
    };

    timer_proof.stop();

    // --
    // SHIFT_PROOFS
    // --
    // Prove in the order of
    // - perm_block_w3 => shift by 4
    // - perm_exec_w3 => shift by 8
    // - (if exist) init_mem_w3 => shift by 8
    // - (if exist) addr_phy_mems => shift by 4
    // - (if exist) phy_mem_addr_w3 => shift by 8
    // - (if exist) addr_vir_mems => shift by 8
    // - (if exist) vir_mem_addr_w3 => shift by 8
    let timer_proof = Timer::new("Shift Proofs");
    let shift_proof = {
      // perm_exec_w3
      let mut orig_polys = vec![&perm_exec_w3_prover.poly_w[0]];
      let mut shifted_polys = vec![&perm_exec_w3_shifted_prover.poly_w[0]];
      let mut header_len_list = vec![6];
      // block_w3
      for poly in &block_w3_prover.poly_w {
        orig_polys.push(poly);
      }
      for poly in &block_w3_shifted_prover.poly_w {
        shifted_polys.push(poly);
      }
      header_len_list.extend(vec![8; block_num_instances]);
      // init_phy_mem_w3, init_vir_mem_w3
      if total_num_init_phy_mem_accesses > 0 {
        orig_polys.push(&init_phy_mem_w3_prover.poly_w[0]);
        shifted_polys.push(&init_phy_mem_w3_shifted_prover.poly_w[0]);
        header_len_list.push(6);
      }
      if total_num_init_vir_mem_accesses > 0 {
        orig_polys.push(&init_vir_mem_w3_prover.poly_w[0]);
        shifted_polys.push(&init_vir_mem_w3_shifted_prover.poly_w[0]);
        header_len_list.push(6);
      }
      // addr_phy_mems, phy_mem_addr_w3
      if total_num_phy_mem_accesses > 0 {
        orig_polys.push(&addr_phy_mems_prover.poly_w[0]);
        shifted_polys.push(&addr_phy_mems_shifted_prover.poly_w[0]);
        header_len_list.push(4);
        orig_polys.push(&phy_mem_addr_w3_prover.poly_w[0]);
        shifted_polys.push(&phy_mem_addr_w3_shifted_prover.poly_w[0]);
        header_len_list.push(6);
      }
      // addr_vir_mems, vir_mem_addr_w3
      if total_num_vir_mem_accesses > 0 {
        orig_polys.push(&addr_vir_mems_prover.poly_w[0]);
        shifted_polys.push(&addr_vir_mems_shifted_prover.poly_w[0]);
        header_len_list.push(6);
        orig_polys.push(&vir_mem_addr_w3_prover.poly_w[0]);
        shifted_polys.push(&vir_mem_addr_w3_shifted_prover.poly_w[0]);
        header_len_list.push(6);
      }
      let shift_proof = ShiftProofs::prove(
        orig_polys,
        shifted_polys,
        header_len_list,
        vars_gens,
        transcript,
        &mut random_tape,
      );
      shift_proof
    };
    timer_proof.stop();

    // --
    // IO_PROOFS
    // --

    let timer_proof = Timer::new("IO Proofs");
    let io_proof = IOProofs::prove(
      &exec_inputs_prover.poly_w[0],
      num_ios,
      num_inputs_unpadded,
      consis_num_proofs,
      input_block_num,
      output_block_num,
      input_liveness,
      input_offset,
      output_offset,
      input,
      output,
      output_exec_num,
      vars_gens,
      transcript,
      &mut random_tape,
    );
    timer_proof.stop();

    timer_prove.stop();
    SNARK {
      block_comm_vars_list,
      exec_comm_inputs,
      addr_comm_phy_mems,
      addr_comm_phy_mems_shifted,
      addr_comm_vir_mems,
      addr_comm_vir_mems_shifted,
      addr_comm_ts_bits,

      perm_exec_comm_w2_list,
      perm_exec_comm_w3_list,
      perm_exec_comm_w3_shifted,

      block_comm_w2_list,
      block_comm_w3_list,
      block_comm_w3_list_shifted,

      init_phy_mem_comm_w2,
      init_phy_mem_comm_w3,
      init_phy_mem_comm_w3_shifted,

      init_vir_mem_comm_w2,
      init_vir_mem_comm_w3,
      init_vir_mem_comm_w3_shifted,

      phy_mem_addr_comm_w2,
      phy_mem_addr_comm_w3,
      phy_mem_addr_comm_w3_shifted,

      vir_mem_addr_comm_w2,
      vir_mem_addr_comm_w3,
      vir_mem_addr_comm_w3_shifted,

      block_r1cs_sat_proof,
      block_inst_evals_bound_rp,
      block_inst_evals_list,
      block_r1cs_eval_proof_list,

      pairwise_check_r1cs_sat_proof,
      pairwise_check_inst_evals_bound_rp,
      pairwise_check_inst_evals_list,
      pairwise_check_r1cs_eval_proof,

      perm_root_r1cs_sat_proof,
      perm_root_inst_evals,
      perm_root_r1cs_eval_proof,

      perm_poly_poly_list,
      proof_eval_perm_poly_prod_list,

      shift_proof,
      io_proof,
    }
  }

  /// A method to verify the SNARK proof of the satisfiability of an R1CS instance
  pub fn verify(
    &self,
    input_block_num: usize,
    output_block_num: usize,
    input_liveness: &Vec<bool>,
    func_input_width: usize,
    input_offset: usize,
    output_offset: usize,
    input: &Vec<[u8; 32]>,
    input_stack: &Vec<[u8; 32]>,
    input_mem: &Vec<[u8; 32]>,
    output: &[u8; 32],
    output_exec_num: usize,

    num_vars: usize,
    num_ios: usize,
    max_block_num_phy_ops: usize,
    block_num_phy_ops: &Vec<usize>,
    max_block_num_vir_ops: usize,
    block_num_vir_ops: &Vec<usize>,
    mem_addr_ts_bits_size: usize,

    num_inputs_unpadded: usize,
    // How many variables (witnesses) are used by each block? Round to the next power of 2
    block_num_vars: &Vec<usize>,
    block_num_instances_bound: usize,

    block_max_num_proofs: usize,
    block_num_proofs: &Vec<usize>,
    block_num_cons: usize,
    block_comm_map: &Vec<Vec<usize>>,
    block_comm_list: &Vec<ComputationCommitment>,
    block_gens: &SNARKGens,

    consis_num_proofs: usize,
    total_num_init_phy_mem_accesses: usize,
    total_num_init_vir_mem_accesses: usize,
    total_num_phy_mem_accesses: usize,
    total_num_vir_mem_accesses: usize,
    pairwise_check_num_cons: usize,
    pairwise_check_comm: &ComputationCommitment,
    pairwise_check_gens: &SNARKGens,

    perm_root_num_cons: usize,
    perm_root_comm: &ComputationCommitment,
    perm_root_gens: &SNARKGens,

    vars_gens: &R1CSGens,
    transcript: &mut Transcript,
  ) -> Result<(), ProofVerifyError> {
    let proof_size = bincode::serialize(&self).unwrap().len();
    let commit_size = bincode::serialize(&block_comm_list).unwrap().len() +
      // bincode::serialize(&block_gens).unwrap().len() + 
      bincode::serialize(&pairwise_check_comm).unwrap().len() +
      // bincode::serialize(&pairwise_check_gens).unwrap().len() + 
      bincode::serialize(&perm_root_comm).unwrap().len();
    // bincode::serialize(&perm_root_gens).unwrap().len();
    let meta_size =
      // usize
      19 * std::mem::size_of::<usize>() +
      // Vec<usize> or Vec<Vec<usize>>
      bincode::serialize(block_num_phy_ops).unwrap().len() +
      bincode::serialize(block_num_vir_ops).unwrap().len() +
      bincode::serialize(block_num_vars).unwrap().len() +
      bincode::serialize(block_num_proofs).unwrap().len() +
      bincode::serialize(block_comm_map).unwrap().len() +
      // Other vectors
      bincode::serialize(input).unwrap().len() +
      bincode::serialize(output).unwrap().len();
    // Everything else
    // bincode::serialize(vars_gens).unwrap().len();

    let timer_verify = Timer::new("SNARK::verify");
    transcript.append_protocol_name(SNARK::protocol_name());

    // --
    // ASSERTIONS
    // --
    assert!(0 < consis_num_proofs);
    for p in 0..block_num_instances_bound {
      assert!(block_num_proofs[p] <= block_max_num_proofs);
    }

    // --
    // COMMITMENTS
    // --
    let input_block_num = Scalar::from(input_block_num as u64);
    let output_block_num = Scalar::from(output_block_num as u64);
    let input: Vec<Scalar> = input
      .iter()
      .map(|i| Scalar::from_bytes(i).unwrap())
      .collect();
    let input_stack: Vec<Scalar> = input_stack
      .iter()
      .map(|i| Scalar::from_bytes(i).unwrap())
      .collect();
    let input_mem: Vec<Scalar> = input_mem
      .iter()
      .map(|i| Scalar::from_bytes(i).unwrap())
      .collect();
    let output: Scalar = Scalar::from_bytes(output).unwrap();
    {
      let timer_commit = Timer::new("inst_commit");
      // Commit public parameters
      Scalar::from(func_input_width as u64).append_to_transcript(b"func_input_width", transcript);
      Scalar::from(input_offset as u64).append_to_transcript(b"input_offset", transcript);
      Scalar::from(output_offset as u64).append_to_transcript(b"output_offset", transcript);
      Scalar::from(output_exec_num as u64).append_to_transcript(b"output_exec_num", transcript);
      Scalar::from(num_ios as u64).append_to_transcript(b"num_ios", transcript);
      for n in block_num_vars {
        Scalar::from(*n as u64).append_to_transcript(b"block_num_vars", transcript);
      }
      Scalar::from(mem_addr_ts_bits_size as u64)
        .append_to_transcript(b"mem_addr_ts_bits_size", transcript);
      Scalar::from(num_inputs_unpadded as u64)
        .append_to_transcript(b"num_inputs_unpadded", transcript);
      Scalar::from(block_num_instances_bound as u64)
        .append_to_transcript(b"block_num_instances_bound", transcript);
      Scalar::from(block_max_num_proofs as u64)
        .append_to_transcript(b"block_max_num_proofs", transcript);
      for p in block_num_phy_ops {
        Scalar::from(*p as u64).append_to_transcript(b"block_num_phy_ops", transcript);
      }
      for v in block_num_vir_ops {
        Scalar::from(*v as u64).append_to_transcript(b"block_num_vir_ops", transcript);
      }
      Scalar::from(total_num_init_phy_mem_accesses as u64)
        .append_to_transcript(b"total_num_init_phy_mem_accesses", transcript);
      Scalar::from(total_num_init_vir_mem_accesses as u64)
        .append_to_transcript(b"total_num_init_vir_mem_accesses", transcript);
      Scalar::from(total_num_phy_mem_accesses as u64)
        .append_to_transcript(b"total_num_phy_mem_accesses", transcript);
      Scalar::from(total_num_vir_mem_accesses as u64)
        .append_to_transcript(b"total_num_vir_mem_accesses", transcript);

      // commit num_proofs
      Scalar::from(block_max_num_proofs as u64)
        .append_to_transcript(b"block_max_num_proofs", transcript);
      for n in block_num_proofs {
        Scalar::from(*n as u64).append_to_transcript(b"block_num_proofs", transcript);
      }

      // append a commitment to the computation to the transcript
      for b in block_comm_map {
        for l in b {
          Scalar::from(*l as u64).append_to_transcript(b"block_comm_map", transcript);
        }
      }
      for c in block_comm_list {
        c.comm.append_to_transcript(b"block_comm", transcript);
      }
      pairwise_check_comm
        .comm
        .append_to_transcript(b"pairwise_comm", transcript);
      perm_root_comm
        .comm
        .append_to_transcript(b"perm_comm", transcript);

      // Commit io
      input_block_num.append_to_transcript(b"input_block_num", transcript);
      output_block_num.append_to_transcript(b"output_block_num", transcript);
      input.append_to_transcript(b"input_list", transcript);
      output.append_to_transcript(b"output_list", transcript);

      timer_commit.stop();
    }

    // --
    // BLOCK SORT
    // --
    // Block_num_instance is the number of non-zero entries in block_num_proofs
    let timer_sort = Timer::new("block_sort");
    let block_num_instances = block_num_proofs
      .iter()
      .fold(0, |i, j| if *j > 0 { i + 1 } else { i });
    // Sort the following based on block_num_proofs:
    // - block_num_proofs
    // - block_inst, block_comm, block_decomm
    // - block_num_phy_mem_accesses
    // - mem_extract_inst, mem_extract_decomm
    let mut inst_sorter = Vec::new();
    for i in 0..block_num_instances_bound {
      inst_sorter.push(InstanceSortHelper::new(block_num_proofs[i], i))
    }
    // Sort from high -> low
    inst_sorter.sort_by(|a, b| b.cmp(a));

    let inst_sorter = &inst_sorter[..block_num_instances];
    let mut block_num_proofs: Vec<usize> = inst_sorter.iter().map(|i| i.num_exec).collect();
    // index[i] = j => the original jth entry should now be at the ith position
    let block_index: Vec<usize> = inst_sorter.iter().map(|i| i.index).collect();
    let block_num_vars: Vec<usize> = (0..block_num_instances)
      .map(|i| block_num_vars[block_index[i]])
      .collect();
    let block_num_phy_ops: Vec<usize> = (0..block_num_instances)
      .map(|i| block_num_phy_ops[block_index[i]])
      .collect();
    let block_num_vir_ops: Vec<usize> = (0..block_num_instances)
      .map(|i| block_num_vir_ops[block_index[i]])
      .collect();

    // --
    // PADDING
    // --
    // Pad entries of block_num_proofs to a power of 2
    let block_max_num_proofs = block_max_num_proofs.next_power_of_two();
    for i in 0..block_num_instances {
      block_num_proofs[i] = block_num_proofs[i].next_power_of_two();
    }
    // Pad exec_inputs, addr_phy_mems, addr_vir_mems with dummys so the length is a power of 2
    let consis_num_proofs = consis_num_proofs.next_power_of_two();
    let total_num_init_phy_mem_accesses = if total_num_init_phy_mem_accesses == 0 {
      0
    } else {
      total_num_init_phy_mem_accesses.next_power_of_two()
    };
    let total_num_init_vir_mem_accesses = if total_num_init_vir_mem_accesses == 0 {
      0
    } else {
      total_num_init_vir_mem_accesses.next_power_of_two()
    };
    let total_num_phy_mem_accesses = if total_num_phy_mem_accesses == 0 {
      0
    } else {
      total_num_phy_mem_accesses.next_power_of_two()
    };
    let total_num_vir_mem_accesses = if total_num_vir_mem_accesses == 0 {
      0
    } else {
      total_num_vir_mem_accesses.next_power_of_two()
    };

    // Pad num_proofs with 1 until the next power of 2
    block_num_proofs.extend(vec![
      1;
      block_num_instances.next_power_of_two()
        - block_num_instances
    ]);
    let block_num_proofs = &block_num_proofs;

    // --
    // PAIRWISE SORT
    // --
    // Sort the pairwise instances: CONSIS_CHECK, PHY_MEM_COHERE
    let mut inst_sorter = Vec::new();
    inst_sorter.push(InstanceSortHelper::new(consis_num_proofs, 0));
    inst_sorter.push(InstanceSortHelper::new(total_num_phy_mem_accesses, 1));
    inst_sorter.push(InstanceSortHelper::new(total_num_vir_mem_accesses, 2));
    // Sort from high -> low
    inst_sorter.sort_by(|a, b| b.cmp(a));

    let pairwise_num_instances = 1
      + if total_num_phy_mem_accesses > 0 { 1 } else { 0 }
      + if total_num_vir_mem_accesses > 0 { 1 } else { 0 };
    let inst_sorter = &inst_sorter[..pairwise_num_instances];
    // index[i] = j => the original jth entry should now be at the ith position
    let pairwise_index: Vec<usize> = inst_sorter.iter().map(|i| i.index).collect();
    timer_sort.stop();

    // --
    // SAMPLE CHALLENGES, COMMIT WITNESSES, & CONSTRUCT WITNESS_SEC_INFO
    // --
    let timer_commit = Timer::new("witness_commit");

    let comb_tau = transcript.challenge_scalar(b"challenge_tau");
    let comb_r = transcript.challenge_scalar(b"challenge_r");

    let (
      perm_w0_verifier,
      perm_exec_w2_verifier,
      perm_exec_w3_verifier,
      perm_exec_w3_shifted_verifier,
      block_w2_verifier,
      block_w3_verifier,
      block_w3_shifted_verifier,
    ) = {
      // Let the verifier generate perm_w0 itself
      let mut perm_w0 = vec![comb_tau];
      let mut r_tmp = comb_r;
      for _ in 1..2 * num_inputs_unpadded {
        perm_w0.push(r_tmp);
        r_tmp *= comb_r;
      }
      perm_w0.extend(vec![ZERO; num_ios - 2 * num_inputs_unpadded]);
      // create a multilinear polynomial using the supplied assignment for variables
      let perm_poly_w0 = DensePolynomial::new(perm_w0.clone());
      // produce a commitment to the satisfying assignment
      let (perm_comm_w0, _blinds_vars) = perm_poly_w0.commit(&vars_gens.gens_pc, None);
      // add the commitment to the prover's transcript
      perm_comm_w0.append_to_transcript(b"poly_commitment", transcript);

      // perm_exec
      self
        .perm_exec_comm_w2_list
        .append_to_transcript(b"poly_commitment", transcript);
      self
        .perm_exec_comm_w3_list
        .append_to_transcript(b"poly_commitment", transcript);
      self
        .perm_exec_comm_w3_shifted
        .append_to_transcript(b"poly_commitment", transcript);

      // block_w2
      let block_w2_verifier = {
        let block_w2_size_list: Vec<usize> = (0..block_num_instances)
          .map(|i| {
            (2 * num_inputs_unpadded + 2 * block_num_phy_ops[i] + 4 * block_num_vir_ops[i])
              .next_power_of_two()
          })
          .collect();
        for p in 0..block_num_instances {
          self.block_comm_w2_list[p].append_to_transcript(b"poly_commitment", transcript);
        }
        VerifierWitnessSecInfo::new(
          block_w2_size_list,
          &block_num_proofs,
          self.block_comm_w2_list.clone(),
        )
      };
      // block_w3
      for p in 0..block_num_instances {
        self.block_comm_w3_list[p].append_to_transcript(b"poly_commitment", transcript);
        self.block_comm_w3_list_shifted[p].append_to_transcript(b"poly_commitment", transcript);
      }
      (
        VerifierWitnessSecInfo::new(vec![num_ios], &vec![1], vec![perm_comm_w0.clone()]),
        VerifierWitnessSecInfo::new(
          vec![num_ios],
          &vec![consis_num_proofs],
          vec![self.perm_exec_comm_w2_list.clone()],
        ),
        VerifierWitnessSecInfo::new(
          vec![W3_WIDTH],
          &vec![consis_num_proofs],
          vec![self.perm_exec_comm_w3_list.clone()],
        ),
        VerifierWitnessSecInfo::new(
          vec![W3_WIDTH],
          &vec![consis_num_proofs],
          vec![self.perm_exec_comm_w3_shifted.clone()],
        ),
        block_w2_verifier,
        VerifierWitnessSecInfo::new(
          vec![W3_WIDTH; block_num_instances],
          &block_num_proofs.clone(),
          self.block_comm_w3_list.clone(),
        ),
        VerifierWitnessSecInfo::new(
          vec![W3_WIDTH; block_num_instances],
          &block_num_proofs.clone(),
          self.block_comm_w3_list_shifted.clone(),
        ),
      )
    };

    let (init_phy_mem_w2_verifier, init_phy_mem_w3_verifier, init_phy_mem_w3_shifted_verifier) = {
      if total_num_init_phy_mem_accesses > 0 {
        self
          .init_phy_mem_comm_w2
          .append_to_transcript(b"poly_commitment", transcript);
        self
          .init_phy_mem_comm_w3
          .append_to_transcript(b"poly_commitment", transcript);
        self
          .init_phy_mem_comm_w3_shifted
          .append_to_transcript(b"poly_commitment", transcript);
        (
          VerifierWitnessSecInfo::new(
            vec![INIT_PHY_MEM_WIDTH],
            &vec![total_num_init_phy_mem_accesses],
            vec![self.init_phy_mem_comm_w2.clone()],
          ),
          VerifierWitnessSecInfo::new(
            vec![W3_WIDTH],
            &vec![total_num_init_phy_mem_accesses],
            vec![self.init_phy_mem_comm_w3.clone()],
          ),
          VerifierWitnessSecInfo::new(
            vec![W3_WIDTH],
            &vec![total_num_init_phy_mem_accesses],
            vec![self.init_phy_mem_comm_w3_shifted.clone()],
          ),
        )
      } else {
        (
          VerifierWitnessSecInfo::dummy(),
          VerifierWitnessSecInfo::dummy(),
          VerifierWitnessSecInfo::dummy(),
        )
      }
    };

    let (init_vir_mem_w2_verifier, init_vir_mem_w3_verifier, init_vir_mem_w3_shifted_verifier) = {
      if total_num_init_vir_mem_accesses > 0 {
        self
          .init_vir_mem_comm_w2
          .append_to_transcript(b"poly_commitment", transcript);
        self
          .init_vir_mem_comm_w3
          .append_to_transcript(b"poly_commitment", transcript);
        self
          .init_vir_mem_comm_w3_shifted
          .append_to_transcript(b"poly_commitment", transcript);
        (
          VerifierWitnessSecInfo::new(
            vec![INIT_VIR_MEM_WIDTH],
            &vec![total_num_init_vir_mem_accesses],
            vec![self.init_vir_mem_comm_w2.clone()],
          ),
          VerifierWitnessSecInfo::new(
            vec![W3_WIDTH],
            &vec![total_num_init_vir_mem_accesses],
            vec![self.init_vir_mem_comm_w3.clone()],
          ),
          VerifierWitnessSecInfo::new(
            vec![W3_WIDTH],
            &vec![total_num_init_vir_mem_accesses],
            vec![self.init_vir_mem_comm_w3_shifted.clone()],
          ),
        )
      } else {
        (
          VerifierWitnessSecInfo::dummy(),
          VerifierWitnessSecInfo::dummy(),
          VerifierWitnessSecInfo::dummy(),
        )
      }
    };

    let (phy_mem_addr_w2_verifier, phy_mem_addr_w3_verifier, phy_mem_addr_w3_shifted_verifier) = {
      if total_num_phy_mem_accesses > 0 {
        self
          .phy_mem_addr_comm_w2
          .append_to_transcript(b"poly_commitment", transcript);
        self
          .phy_mem_addr_comm_w3
          .append_to_transcript(b"poly_commitment", transcript);
        self
          .phy_mem_addr_comm_w3_shifted
          .append_to_transcript(b"poly_commitment", transcript);
        (
          VerifierWitnessSecInfo::new(
            vec![PHY_MEM_WIDTH],
            &vec![total_num_phy_mem_accesses],
            vec![self.phy_mem_addr_comm_w2.clone()],
          ),
          VerifierWitnessSecInfo::new(
            vec![W3_WIDTH],
            &vec![total_num_phy_mem_accesses],
            vec![self.phy_mem_addr_comm_w3.clone()],
          ),
          VerifierWitnessSecInfo::new(
            vec![W3_WIDTH],
            &vec![total_num_phy_mem_accesses],
            vec![self.phy_mem_addr_comm_w3_shifted.clone()],
          ),
        )
      } else {
        (
          VerifierWitnessSecInfo::dummy(),
          VerifierWitnessSecInfo::dummy(),
          VerifierWitnessSecInfo::dummy(),
        )
      }
    };

    let (vir_mem_addr_w2_verifier, vir_mem_addr_w3_verifier, vir_mem_addr_w3_shifted_verifier) = {
      if total_num_vir_mem_accesses > 0 {
        self
          .vir_mem_addr_comm_w2
          .append_to_transcript(b"poly_commitment", transcript);
        self
          .vir_mem_addr_comm_w3
          .append_to_transcript(b"poly_commitment", transcript);
        self
          .vir_mem_addr_comm_w3_shifted
          .append_to_transcript(b"poly_commitment", transcript);
        (
          VerifierWitnessSecInfo::new(
            vec![VIR_MEM_WIDTH],
            &vec![total_num_vir_mem_accesses],
            vec![self.vir_mem_addr_comm_w2.clone()],
          ),
          VerifierWitnessSecInfo::new(
            vec![W3_WIDTH],
            &vec![total_num_vir_mem_accesses],
            vec![self.vir_mem_addr_comm_w3.clone()],
          ),
          VerifierWitnessSecInfo::new(
            vec![W3_WIDTH],
            &vec![total_num_vir_mem_accesses],
            vec![self.vir_mem_addr_comm_w3_shifted.clone()],
          ),
        )
      } else {
        (
          VerifierWitnessSecInfo::dummy(),
          VerifierWitnessSecInfo::dummy(),
          VerifierWitnessSecInfo::dummy(),
        )
      }
    };

    let (block_vars_verifier, exec_inputs_verifier) = {
      // add the commitment to the verifier's transcript
      for p in 0..block_num_instances {
        self.block_comm_vars_list[p].append_to_transcript(b"poly_commitment", transcript);
      }
      self.exec_comm_inputs[0].append_to_transcript(b"poly_commitment", transcript);
      (
        VerifierWitnessSecInfo::new(
          block_num_vars,
          &block_num_proofs,
          self.block_comm_vars_list.clone(),
        ),
        VerifierWitnessSecInfo::new(
          vec![num_ios],
          &vec![consis_num_proofs],
          self.exec_comm_inputs.clone(),
        ),
      )
    };

    let init_phy_mems_verifier = {
      if input_stack.len() > 0 {
        assert_eq!(
          total_num_init_phy_mem_accesses,
          input_stack.len().next_power_of_two()
        );
        // Let the verifier generate init_mems itself
        let init_stacks = [
          (0..input_stack.len())
            .map(|i| vec![ONE, ZERO, Scalar::from(i as u64), input_stack[i].clone()])
            .concat(),
          vec![ZERO; INIT_PHY_MEM_WIDTH * (total_num_init_phy_mem_accesses - input_stack.len())],
        ]
        .concat();
        // create a multilinear polynomial using the supplied assignment for variables
        let poly_init_stacks = DensePolynomial::new(init_stacks.clone());
        // produce a commitment to the satisfying assignment
        let (comm_init_stacks, _blinds_vars) = poly_init_stacks.commit(&vars_gens.gens_pc, None);
        // add the commitment to the prover's transcript
        comm_init_stacks.append_to_transcript(b"poly_commitment", transcript);

        VerifierWitnessSecInfo::new(
          vec![INIT_PHY_MEM_WIDTH],
          &vec![total_num_init_phy_mem_accesses],
          vec![comm_init_stacks],
        )
      } else {
        VerifierWitnessSecInfo::dummy()
      }
    };
    let init_vir_mems_verifier = {
      if input_mem.len() > 0 {
        assert_eq!(
          total_num_init_vir_mem_accesses,
          input_mem.len().next_power_of_two()
        );
        // Let the verifier generate init_mems itself
        let init_mems = [
          (0..input_mem.len())
            .map(|i| vec![ONE, ZERO, Scalar::from(i as u64), input_mem[i].clone()])
            .concat(),
          vec![ZERO; INIT_VIR_MEM_WIDTH * (total_num_init_vir_mem_accesses - input_mem.len())],
        ]
        .concat();
        // create a multilinear polynomial using the supplied assignment for variables
        let poly_init_mems = DensePolynomial::new(init_mems.clone());
        // produce a commitment to the satisfying assignment
        let (comm_init_mems, _blinds_vars) = poly_init_mems.commit(&vars_gens.gens_pc, None);
        // add the commitment to the prover's transcript
        comm_init_mems.append_to_transcript(b"poly_commitment", transcript);

        VerifierWitnessSecInfo::new(
          vec![INIT_VIR_MEM_WIDTH],
          &vec![total_num_init_vir_mem_accesses],
          vec![comm_init_mems],
        )
      } else {
        VerifierWitnessSecInfo::dummy()
      }
    };

    let (addr_phy_mems_verifier, addr_phy_mems_shifted_verifier) = {
      if total_num_phy_mem_accesses > 0 {
        self
          .addr_comm_phy_mems
          .append_to_transcript(b"poly_commitment", transcript);
        self
          .addr_comm_phy_mems_shifted
          .append_to_transcript(b"poly_commitment", transcript);
        (
          VerifierWitnessSecInfo::new(
            vec![PHY_MEM_WIDTH],
            &vec![total_num_phy_mem_accesses],
            vec![self.addr_comm_phy_mems.clone()],
          ),
          VerifierWitnessSecInfo::new(
            vec![PHY_MEM_WIDTH],
            &vec![total_num_phy_mem_accesses],
            vec![self.addr_comm_phy_mems_shifted.clone()],
          ),
        )
      } else {
        (
          VerifierWitnessSecInfo::dummy(),
          VerifierWitnessSecInfo::dummy(),
        )
      }
    };

    let (addr_vir_mems_verifier, addr_vir_mems_shifted_verifier, addr_ts_bits_verifier) = {
      if total_num_vir_mem_accesses > 0 {
        self
          .addr_comm_vir_mems
          .append_to_transcript(b"poly_commitment", transcript);
        self
          .addr_comm_vir_mems_shifted
          .append_to_transcript(b"poly_commitment", transcript);
        self
          .addr_comm_ts_bits
          .append_to_transcript(b"poly_commitment", transcript);
        (
          VerifierWitnessSecInfo::new(
            vec![VIR_MEM_WIDTH],
            &vec![total_num_vir_mem_accesses],
            vec![self.addr_comm_vir_mems.clone()],
          ),
          VerifierWitnessSecInfo::new(
            vec![VIR_MEM_WIDTH],
            &vec![total_num_vir_mem_accesses],
            vec![self.addr_comm_vir_mems_shifted.clone()],
          ),
          VerifierWitnessSecInfo::new(
            vec![mem_addr_ts_bits_size],
            &vec![total_num_vir_mem_accesses],
            vec![self.addr_comm_ts_bits.clone()],
          ),
        )
      } else {
        (
          VerifierWitnessSecInfo::dummy(),
          VerifierWitnessSecInfo::dummy(),
          VerifierWitnessSecInfo::dummy(),
        )
      }
    };
    timer_commit.stop();

    // --
    // BLOCK_CORRECTNESS_EXTRACT
    // --
    {
      let timer_sat_proof = Timer::new("Block Correctness Extract Sat");
      let block_wit_secs = vec![
        &block_vars_verifier,
        &perm_w0_verifier,
        &block_w2_verifier,
        &block_w3_verifier,
        &block_w3_shifted_verifier,
      ];
      let block_challenges = self.block_r1cs_sat_proof.verify(
        block_num_instances,
        block_max_num_proofs,
        block_num_proofs,
        num_vars,
        block_wit_secs,
        block_num_cons,
        &vars_gens,
        &self.block_inst_evals_bound_rp,
        transcript,
      )?;
      timer_sat_proof.stop();

      let timer_eval_proof = Timer::new("Block Correctness Extract Eval");
      // Verify Evaluation on BLOCK
      let [rp, _, rx, ry] = block_challenges;

      for r in &self.block_inst_evals_list {
        r.append_to_transcript(b"ABCr_claim", transcript);
      }
      // Sample random combinations of A, B, C for inst_evals_bound_rp check
      let c0 = transcript.challenge_scalar(b"challenge_c0");
      let c1 = transcript.challenge_scalar(b"challenge_c1");
      let c2 = transcript.challenge_scalar(b"challenge_c2");

      let ABC_evals: Vec<Scalar> = (0..block_num_instances_bound)
        .map(|i| {
          c0 * self.block_inst_evals_list[3 * i]
            + c1 * self.block_inst_evals_list[3 * i + 1]
            + c2 * self.block_inst_evals_list[3 * i + 2]
        })
        .collect();

      for i in 0..block_comm_list.len() {
        self.block_r1cs_eval_proof_list[i].verify(
          &block_comm_list[i].comm,
          &rx,
          &ry,
          &block_comm_map[i]
            .iter()
            .map(|i| self.block_inst_evals_list[*i])
            .collect(),
          &block_gens.gens_r1cs_eval,
          transcript,
        )?;
      }
      // Permute block_inst_evals_list to the correct order for RP evaluation
      let ABC_evals: Vec<Scalar> = (0..block_num_instances)
        .map(|i| ABC_evals[block_index[i]])
        .collect();
      // Verify that block_inst_evals_bound_rp is block_inst_evals_list bind rp
      assert_eq!(
        DensePolynomial::new(ABC_evals).evaluate(&rp),
        c0 * self.block_inst_evals_bound_rp[0]
          + c1 * self.block_inst_evals_bound_rp[1]
          + c2 * self.block_inst_evals_bound_rp[2]
      );
      timer_eval_proof.stop();
    }

    // --
    // PAIRWISE_CHECK
    // --
    {
      let timer_sat_proof = Timer::new("Pairwise Check Sat");

      let pairwise_size = [
        consis_num_proofs,
        total_num_phy_mem_accesses,
        total_num_vir_mem_accesses,
      ]
      .iter()
      .max()
      .unwrap()
      .clone();
      let (pairwise_verifier, inst_map) = VerifierWitnessSecInfo::merge(vec![
        &perm_exec_w3_verifier,
        &addr_phy_mems_verifier,
        &addr_vir_mems_verifier,
      ]);
      let (pairwise_shifted_verifier, _) = VerifierWitnessSecInfo::merge(vec![
        &perm_exec_w3_shifted_verifier,
        &addr_phy_mems_shifted_verifier,
        &addr_vir_mems_shifted_verifier,
      ]);
      let addr_ts_bits_verifier = {
        let mut components = vec![&perm_w0_verifier; inst_map.len()];
        for i in 0..inst_map.len() {
          if inst_map[i] == 2 {
            components[i] = &addr_ts_bits_verifier;
          }
        }
        VerifierWitnessSecInfo::concat(components)
      };
      let pairwise_num_instances = pairwise_verifier.num_proofs.len();
      let pairwise_num_proofs: Vec<usize> = pairwise_verifier.num_proofs.clone();

      let pairwise_check_challenges = self.pairwise_check_r1cs_sat_proof.verify(
        pairwise_num_instances,
        pairwise_size,
        &pairwise_num_proofs,
        max(8, mem_addr_ts_bits_size),
        vec![
          &pairwise_verifier,
          &pairwise_shifted_verifier,
          &addr_ts_bits_verifier,
        ],
        pairwise_check_num_cons,
        &vars_gens,
        &self.pairwise_check_inst_evals_bound_rp,
        transcript,
      )?;
      timer_sat_proof.stop();

      let timer_eval_proof = Timer::new("Pairwise Check Eval");
      // Verify Evaluation on CONSIS_CHECK
      let [rp, _, rx, ry] = pairwise_check_challenges;

      for r in &self.pairwise_check_inst_evals_list {
        r.append_to_transcript(b"ABCr_claim", transcript);
      }
      // Sample random combinations of A, B, C for inst_evals_bound_rp check
      let c0 = transcript.challenge_scalar(b"challenge_c0");
      let c1 = transcript.challenge_scalar(b"challenge_c1");
      let c2 = transcript.challenge_scalar(b"challenge_c2");

      let ABC_evals: Vec<Scalar> = (0..3)
        .map(|i| {
          c0 * self.pairwise_check_inst_evals_list[3 * i]
            + c1 * self.pairwise_check_inst_evals_list[3 * i + 1]
            + c2 * self.pairwise_check_inst_evals_list[3 * i + 2]
        })
        .collect();

      self.pairwise_check_r1cs_eval_proof.verify(
        &pairwise_check_comm.comm,
        &rx,
        &ry,
        &self.pairwise_check_inst_evals_list,
        &pairwise_check_gens.gens_r1cs_eval,
        transcript,
      )?;
      // Permute pairwise_check_inst_evals_list to the correct order for RP evaluation
      let ABC_evals: Vec<Scalar> = (0..pairwise_num_instances)
        .map(|i| ABC_evals[pairwise_index[i]])
        .collect();
      // Verify that pairwise_check_inst_evals_bound_rp is pairwise_check_inst_evals_list bind rp
      assert_eq!(
        DensePolynomial::new(ABC_evals).evaluate(&rp),
        c0 * self.pairwise_check_inst_evals_bound_rp[0]
          + c1 * self.pairwise_check_inst_evals_bound_rp[1]
          + c2 * self.pairwise_check_inst_evals_bound_rp[2]
      );
      // Correctness of the shift will be handled in SHIFT_PROOFS
      timer_eval_proof.stop();
    };

    // --
    // PERM_EXEC_ROOT, MEM_ADDR_ROOT
    // --
    {
      let perm_size = [
        consis_num_proofs,
        total_num_init_phy_mem_accesses,
        total_num_init_vir_mem_accesses,
        total_num_phy_mem_accesses,
        total_num_vir_mem_accesses,
      ]
      .iter()
      .max()
      .unwrap()
      .clone();
      let timer_sat_proof = Timer::new("Perm Root Sat");
      let (perm_root_w1_verifier, _) = VerifierWitnessSecInfo::merge(vec![
        &exec_inputs_verifier,
        &init_phy_mems_verifier,
        &init_vir_mems_verifier,
        &addr_phy_mems_verifier,
        &addr_vir_mems_verifier,
      ]);
      let (perm_root_w2_verifier, _) = VerifierWitnessSecInfo::merge(vec![
        &perm_exec_w2_verifier,
        &init_phy_mem_w2_verifier,
        &init_vir_mem_w2_verifier,
        &phy_mem_addr_w2_verifier,
        &vir_mem_addr_w2_verifier,
      ]);
      let (perm_root_w3_verifier, _) = VerifierWitnessSecInfo::merge(vec![
        &perm_exec_w3_verifier,
        &init_phy_mem_w3_verifier,
        &init_vir_mem_w3_verifier,
        &phy_mem_addr_w3_verifier,
        &vir_mem_addr_w3_verifier,
      ]);
      let (perm_root_w3_shifted_verifier, _) = VerifierWitnessSecInfo::merge(vec![
        &perm_exec_w3_shifted_verifier,
        &init_phy_mem_w3_shifted_verifier,
        &init_vir_mem_w3_shifted_verifier,
        &phy_mem_addr_w3_shifted_verifier,
        &vir_mem_addr_w3_shifted_verifier,
      ]);
      let perm_root_num_instances = perm_root_w1_verifier.num_proofs.len();
      let perm_root_num_proofs: Vec<usize> = perm_root_w1_verifier.num_proofs.clone();
      let perm_block_root_challenges = self.perm_root_r1cs_sat_proof.verify(
        perm_root_num_instances,
        perm_size,
        &perm_root_num_proofs,
        num_ios,
        vec![
          &perm_w0_verifier,
          &perm_root_w1_verifier,
          &perm_root_w2_verifier,
          &perm_root_w3_verifier,
          &perm_root_w3_shifted_verifier,
        ],
        perm_root_num_cons,
        &vars_gens,
        &self.perm_root_inst_evals,
        transcript,
      )?;
      timer_sat_proof.stop();

      let timer_eval_proof = Timer::new("Perm Root Eval");
      // Verify Evaluation on PERM_BLOCK_ROOT
      let [Ar, Br, Cr] = &self.perm_root_inst_evals;
      Ar.append_to_transcript(b"Ar_claim", transcript);
      Br.append_to_transcript(b"Br_claim", transcript);
      Cr.append_to_transcript(b"Cr_claim", transcript);
      let [_, _, rx, ry] = perm_block_root_challenges;
      self.perm_root_r1cs_eval_proof.verify(
        &perm_root_comm.comm,
        &rx,
        &ry,
        &self.perm_root_inst_evals.to_vec(),
        &perm_root_gens.gens_r1cs_eval,
        transcript,
      )?;
      timer_eval_proof.stop();
    }

    // --
    // PERM_PRODUCT_PROOF
    // --
    {
      let timer_eval_opening = Timer::new("Perm Product");
      // Verify prod of exec, blocks, mem_block, & mem_addr
      let (perm_poly_w3_verifier, inst_map) = {
        let mut components = vec![
          &perm_exec_w3_verifier,
          &init_phy_mem_w3_verifier,
          &init_vir_mem_w3_verifier,
          &phy_mem_addr_w3_verifier,
          &vir_mem_addr_w3_verifier,
          &block_w3_verifier,
        ];
        if max_block_num_phy_ops > 0 {
          components.push(&block_w3_verifier);
        }
        if max_block_num_vir_ops > 0 {
          components.push(&block_w3_verifier);
        }
        VerifierWitnessSecInfo::merge(components)
      };
      let pm_bl_id = 6;
      let vm_bl_id = if max_block_num_phy_ops > 0 { 7 } else { 6 };

      let perm_poly_num_instances = perm_poly_w3_verifier.num_proofs.len();
      let mut perm_poly_num_proofs: Vec<usize> = perm_poly_w3_verifier.num_proofs.clone();
      perm_poly_num_proofs.extend(vec![
        1;
        perm_poly_num_instances.next_power_of_two()
          - perm_poly_num_instances
      ]);
      let perm_poly_num_inputs: Vec<usize> = vec![8; perm_poly_num_instances];

      // Commitment Opening
      let num_vars_list = (0..perm_poly_num_instances)
        .map(|i| (perm_poly_num_proofs[i] * perm_poly_num_inputs[i]).log_2())
        .collect();
      let two_b = vec![ONE, ZERO];
      let four_b = vec![ONE, ZERO, ZERO];
      let six_b = vec![ONE, ONE, ZERO];
      let r_list: Vec<&Vec<Scalar>> = inst_map
        .iter()
        .map(|i| {
          if *i == vm_bl_id {
            &six_b
          } else if *i == pm_bl_id {
            &four_b
          } else {
            &two_b
          }
        })
        .collect();
      PolyEvalProof::verify_plain_batched_instances(
        &self.proof_eval_perm_poly_prod_list,
        &vars_gens.gens_pc,
        transcript,
        r_list,
        &self.perm_poly_poly_list,
        &perm_poly_w3_verifier.comm_w,
        &num_vars_list,
      )?;

      // Compute poly for PERM_EXEC, PERM_BLOCK, MEM_BLOCK, MEM_ADDR base on INST_MAP
      let mut perm_block_poly_bound_tau = ONE;
      let mut perm_exec_poly_bound_tau = ONE;
      let mut phy_mem_block_poly_bound_tau = ONE;
      let mut phy_mem_addr_poly_bound_tau = ONE;
      let mut vir_mem_block_poly_bound_tau = ONE;
      let mut vir_mem_addr_poly_bound_tau = ONE;
      // INST_MAP:
      //   0 -> perm_exec,
      //   1 -> init_phy_mem, count towards phy_mem_block
      //   2 -> init_mem, count towards vir_mem_block
      //   3 -> phy_mem_block,
      //   4 -> vir_mem_block,
      //   5 -> perm_block,
      //   6 -> phy_mem_addr,
      //   7 -> vir_mem_addr
      for p in 0..perm_poly_num_instances {
        match inst_map[p] {
          0 => {
            perm_exec_poly_bound_tau *= self.perm_poly_poly_list[p];
          }
          1 => {
            phy_mem_block_poly_bound_tau *= self.perm_poly_poly_list[p];
          }
          2 => {
            vir_mem_block_poly_bound_tau *= self.perm_poly_poly_list[p];
          }
          3 => {
            phy_mem_addr_poly_bound_tau *= self.perm_poly_poly_list[p];
          }
          4 => {
            vir_mem_addr_poly_bound_tau *= self.perm_poly_poly_list[p];
          }
          5 => {
            perm_block_poly_bound_tau *= self.perm_poly_poly_list[p];
          }
          6 => {
            if max_block_num_phy_ops > 0 {
              phy_mem_block_poly_bound_tau *= self.perm_poly_poly_list[p];
            } else {
              vir_mem_block_poly_bound_tau *= self.perm_poly_poly_list[p];
            }
          }
          7 => {
            vir_mem_block_poly_bound_tau *= self.perm_poly_poly_list[p];
          }
          _ => {}
        }
      }
      timer_eval_opening.stop();

      // Correctness of Permutation
      assert_eq!(perm_block_poly_bound_tau, perm_exec_poly_bound_tau);
      // Correctness of Memory
      assert_eq!(phy_mem_block_poly_bound_tau, phy_mem_addr_poly_bound_tau);
      assert_eq!(vir_mem_block_poly_bound_tau, vir_mem_addr_poly_bound_tau);
    };

    // --
    // SHIFT_PROOFS
    // --
    let timer_proof = Timer::new("Shift Proofs");
    {
      // perm_exec_w3
      let mut orig_comms = vec![&perm_exec_w3_verifier.comm_w[0]];
      let mut shifted_comms = vec![&perm_exec_w3_shifted_verifier.comm_w[0]];
      // block_w3
      for comm in &block_w3_verifier.comm_w {
        orig_comms.push(comm);
      }
      for comm in &block_w3_shifted_verifier.comm_w {
        shifted_comms.push(comm);
      }
      let mut poly_size_list = [
        vec![8 * consis_num_proofs],
        (0..block_num_instances)
          .map(|i| 8 * block_num_proofs[i])
          .collect(),
      ]
      .concat();
      let mut shift_size_list = [vec![8], vec![8; block_num_instances]].concat();
      let mut header_len_list = [vec![6], vec![8; block_num_instances]].concat();
      // init_phy_mem_w3, init_vir_mem_w3
      if total_num_init_phy_mem_accesses > 0 {
        orig_comms.push(&init_phy_mem_w3_verifier.comm_w[0]);
        shifted_comms.push(&init_phy_mem_w3_shifted_verifier.comm_w[0]);
        poly_size_list.push(8 * total_num_init_phy_mem_accesses);
        shift_size_list.push(8);
        header_len_list.push(6);
      }
      if total_num_init_vir_mem_accesses > 0 {
        orig_comms.push(&init_vir_mem_w3_verifier.comm_w[0]);
        shifted_comms.push(&init_vir_mem_w3_shifted_verifier.comm_w[0]);
        poly_size_list.push(8 * total_num_init_vir_mem_accesses);
        shift_size_list.push(8);
        header_len_list.push(6);
      }
      // addr_phy_mems, phy_mem_addr_w3
      if total_num_phy_mem_accesses > 0 {
        orig_comms.push(&addr_phy_mems_verifier.comm_w[0]);
        shifted_comms.push(&addr_phy_mems_shifted_verifier.comm_w[0]);
        poly_size_list.push(4 * total_num_phy_mem_accesses);
        shift_size_list.push(4);
        header_len_list.push(4);
        orig_comms.push(&phy_mem_addr_w3_verifier.comm_w[0]);
        shifted_comms.push(&phy_mem_addr_w3_shifted_verifier.comm_w[0]);
        poly_size_list.push(8 * total_num_phy_mem_accesses);
        shift_size_list.push(8);
        header_len_list.push(6);
      }
      // addr_vir_mems, vir_mem_addr_w3
      if total_num_vir_mem_accesses > 0 {
        orig_comms.push(&addr_vir_mems_verifier.comm_w[0]);
        shifted_comms.push(&addr_vir_mems_shifted_verifier.comm_w[0]);
        poly_size_list.push(8 * total_num_vir_mem_accesses);
        shift_size_list.push(8);
        header_len_list.push(6);
        orig_comms.push(&vir_mem_addr_w3_verifier.comm_w[0]);
        shifted_comms.push(&vir_mem_addr_w3_shifted_verifier.comm_w[0]);
        poly_size_list.push(8 * total_num_vir_mem_accesses);
        shift_size_list.push(8);
        header_len_list.push(6);
      }

      self.shift_proof.verify(
        orig_comms,
        shifted_comms,
        poly_size_list,
        shift_size_list,
        header_len_list,
        vars_gens,
        transcript,
      )?;
    }
    timer_proof.stop();

    // --
    // IO_PROOFS
    // --
    let timer_proof = Timer::new("IO Proofs");
    self.io_proof.verify(
      &self.exec_comm_inputs[0],
      num_ios,
      num_inputs_unpadded,
      consis_num_proofs,
      input_block_num,
      output_block_num,
      input_liveness,
      input_offset,
      output_offset,
      input,
      output,
      output_exec_num,
      vars_gens,
      transcript,
    )?;

    timer_proof.stop();
    timer_verify.stop();

    println!("PROOF SIZE: {}", proof_size);
    println!("COMMIT SIZE: {}", commit_size);
    println!("META SIZE: {}", meta_size);
    println!("Total Proof Size: {}", proof_size + commit_size + meta_size);

    Ok(())
  }
}

/*
/// `NIZKGens` holds public parameters for producing and verifying proofs with the Spartan NIZK
pub struct NIZKGens {
  gens_r1cs_sat: R1CSGens,
}

impl NIZKGens {
  /// Constructs a new `NIZKGens` given the size of the R1CS statement
  pub fn new(num_cons: usize, num_vars: usize, num_inputs: usize) -> Self {
    let num_vars_padded = {
      let mut num_vars_padded = max(num_vars, num_inputs + 1);
      if num_vars_padded != num_vars_padded.next_power_of_two() {
        num_vars_padded = num_vars_padded.next_power_of_two();
      }
      num_vars_padded
    };

    let gens_r1cs_sat = R1CSGens::new(b"gens_r1cs_sat", num_cons, num_vars_padded);
    NIZKGens { gens_r1cs_sat }
  }
}

/// `NIZK` holds a proof produced by Spartan NIZK
#[derive(Serialize, Deserialize, Debug)]
pub struct NIZK {
  r1cs_sat_proof: R1CSProof,
  r: (Vec<Scalar>, Vec<Scalar>),
}

impl NIZK {
  fn protocol_name() -> &'static [u8] {
    b"Spartan NIZK proof"
  }

  /// A method to produce a NIZK proof of the satisfiability of an R1CS instance
  pub fn prove(
    inst: &Instance,
    vars: VarsAssignment,
    input: &InputsAssignment,
    gens: &NIZKGens,
    transcript: &mut Transcript,
  ) -> Self {
    let timer_prove = Timer::new("NIZK::prove");
    // we create a Transcript object seeded with a random Scalar
    // to aid the prover produce its randomness
    let mut random_tape = RandomTape::new(b"proof");

    transcript.append_protocol_name(NIZK::protocol_name());
    transcript.append_message(b"R1CSInstanceDigest", &inst.digest);

    let (r1cs_sat_proof, rx, ry) = {
      // we might need to pad variables
      let padded_vars = {
        let num_padded_vars = inst.inst.get_num_vars();
        let num_vars = vars.assignment.len();
        if num_padded_vars > num_vars {
          vars.pad(num_padded_vars)
        } else {
          vars
        }
      };

      let (proof, rx, ry) = R1CSProof::prove(
        &inst.inst,
        padded_vars.assignment,
        &input.assignment,
        &gens.gens_r1cs_sat,
        transcript,
        &mut random_tape,
      );
      let proof_encoded: Vec<u8> = bincode::serialize(&proof).unwrap();
      Timer::print(&format!("len_r1cs_sat_proof {:?}", proof_encoded.len()));
      (proof, rx, ry)
    };

    timer_prove.stop();
    NIZK {
      r1cs_sat_proof,
      r: (rx, ry),
    }
  }

  /// A method to verify a NIZK proof of the satisfiability of an R1CS instance
  pub fn verify(
    &self,
    inst: &Instance,
    input: &InputsAssignment,
    transcript: &mut Transcript,
    gens: &NIZKGens,
  ) -> Result<(), ProofVerifyError> {
    let timer_verify = Timer::new("NIZK::verify");

    transcript.append_protocol_name(NIZK::protocol_name());
    transcript.append_message(b"R1CSInstanceDigest", &inst.digest);

    // We send evaluations of A, B, C at r = (rx, ry) as claims
    // to enable the verifier complete the first sum-check
    let timer_eval = Timer::new("eval_sparse_polys");
    let (claimed_rx, claimed_ry) = &self.r;
    let inst_evals = inst.inst.evaluate(claimed_rx, claimed_ry);
    timer_eval.stop();

    let timer_sat_proof = Timer::new("verify_sat_proof");
    assert_eq!(input.assignment.len(), inst.inst.get_num_inputs());
    let (rx, ry) = self.r1cs_sat_proof.verify(
      inst.inst.get_num_vars(),
      inst.inst.get_num_cons(),
      &input.assignment,
      &inst_evals,
      transcript,
      &gens.gens_r1cs_sat,
    )?;

    // verify if claimed rx and ry are correct
    assert_eq!(rx, *claimed_rx);
    assert_eq!(ry, *claimed_ry);
    timer_sat_proof.stop();
    timer_verify.stop();

    Ok(())
  }
}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  pub fn check_snark() {
    let num_vars = 256;
    let num_cons = num_vars;
    let num_inputs = 10;

    // produce public generators
    let gens = SNARKGens::new(num_cons, num_vars, num_inputs, num_cons);

    // produce a synthetic R1CSInstance
    let (inst, vars, inputs) = Instance::produce_synthetic_r1cs(num_cons, num_vars, num_inputs);

    // create a commitment to R1CSInstance
    let (comm, decomm) = SNARK::encode(&inst, &gens);

    // produce a proof
    let mut prover_transcript = Transcript::new(b"example");
    let proof = SNARK::prove(
      &inst,
      &comm,
      &decomm,
      vars,
      &inputs,
      &gens,
      &mut prover_transcript,
    );

    // verify the proof
    let mut verifier_transcript = Transcript::new(b"example");
    assert!(proof
      .verify(&comm, &inputs, &mut verifier_transcript, &gens)
      .is_ok());
  }

  #[test]
  pub fn check_r1cs_invalid_index() {
    let num_cons = 4;
    let num_vars = 8;
    let num_inputs = 1;

    let zero: [u8; 32] = [
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0,
    ];

    let A = vec![(0, 0, zero)];
    let B = vec![(100, 1, zero)];
    let C = vec![(1, 1, zero)];

    let inst = Instance::new(num_cons, num_vars, num_inputs, &A, &B, &C);
    assert!(inst.is_err());
    assert_eq!(inst.err(), Some(R1CSError::InvalidIndex));
  }

  #[test]
  pub fn check_r1cs_invalid_scalar() {
    let num_cons = 4;
    let num_vars = 8;
    let num_inputs = 1;

    let zero: [u8; 32] = [
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0,
    ];

    let larger_than_mod = [
      3, 0, 0, 0, 255, 255, 255, 255, 254, 91, 254, 255, 2, 164, 189, 83, 5, 216, 161, 9, 8, 216,
      57, 51, 72, 125, 157, 41, 83, 167, 237, 115,
    ];

    let A = vec![(0, 0, zero)];
    let B = vec![(1, 1, larger_than_mod)];
    let C = vec![(1, 1, zero)];

    let inst = Instance::new(num_cons, num_vars, num_inputs, &A, &B, &C);
    assert!(inst.is_err());
    assert_eq!(inst.err(), Some(R1CSError::InvalidScalar));
  }

  #[test]
  fn test_padded_constraints() {
    // parameters of the R1CS instance
    let num_cons = 1;
    let num_vars = 0;
    let num_inputs = 3;
    let num_non_zero_entries = 3;

    // We will encode the above constraints into three matrices, where
    // the coefficients in the matrix are in the little-endian byte order
    let mut A: Vec<(usize, usize, [u8; 32])> = Vec::new();
    let mut B: Vec<(usize, usize, [u8; 32])> = Vec::new();
    let mut C: Vec<(usize, usize, [u8; 32])> = Vec::new();

    // Create a^2 + b + 13
    A.push((0, num_vars + 2, Scalar::one().to_bytes())); // 1*a
    B.push((0, num_vars + 2, Scalar::one().to_bytes())); // 1*a
    C.push((0, num_vars + 1, Scalar::one().to_bytes())); // 1*z
    C.push((0, num_vars, (-Scalar::from(13u64)).to_bytes())); // -13*1
    C.push((0, num_vars + 3, (-Scalar::one()).to_bytes())); // -1*b

    // Var Assignments (Z_0 = 16 is the only output)
    let vars = vec![Scalar::zero().to_bytes(); num_vars];

    // create an InputsAssignment (a = 1, b = 2)
    let mut inputs = vec![Scalar::zero().to_bytes(); num_inputs];
    inputs[0] = Scalar::from(16u64).to_bytes();
    inputs[1] = Scalar::from(1u64).to_bytes();
    inputs[2] = Scalar::from(2u64).to_bytes();

    let assignment_inputs = InputsAssignment::new(&inputs).unwrap();
    let assignment_vars = VarsAssignment::new(&vars).unwrap();

    // Check if instance is satisfiable
    let inst = Instance::new(num_cons, num_vars, num_inputs, &A, &B, &C).unwrap();
    let res = inst.is_sat(&assignment_vars, &assignment_inputs);
    assert!(res.unwrap(), "should be satisfied");

    // SNARK public params
    let gens = SNARKGens::new(num_cons, num_vars, num_inputs, num_non_zero_entries);

    // create a commitment to the R1CS instance
    let (comm, decomm) = SNARK::encode(&inst, &gens);

    // produce a SNARK
    let mut prover_transcript = Transcript::new(b"snark_example");
    let proof = SNARK::prove(
      &inst,
      &comm,
      &decomm,
      assignment_vars.clone(),
      &assignment_inputs,
      &gens,
      &mut prover_transcript,
    );

    // verify the SNARK
    let mut verifier_transcript = Transcript::new(b"snark_example");
    assert!(proof
      .verify(&comm, &assignment_inputs, &mut verifier_transcript, &gens)
      .is_ok());

    // NIZK public params
    let gens = NIZKGens::new(num_cons, num_vars, num_inputs);

    // produce a NIZK
    let mut prover_transcript = Transcript::new(b"nizk_example");
    let proof = NIZK::prove(
      &inst,
      assignment_vars,
      &assignment_inputs,
      &gens,
      &mut prover_transcript,
    );

    // verify the NIZK
    let mut verifier_transcript = Transcript::new(b"nizk_example");
    assert!(proof
      .verify(&inst, &assignment_inputs, &mut verifier_transcript, &gens)
      .is_ok());
  }
}
*/
