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
mod dense_mlpoly;
mod custom_dense_mlpoly;
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

use std::cmp::{max, Ordering};

use instance::Instance;
use dense_mlpoly::{DensePolynomial, PolyCommitment, PolyEvalProof};
use errors::{ProofVerifyError, R1CSError};
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
use std::thread;

const ZERO: Scalar = Scalar::zero();
const ONE: Scalar = Scalar::one();

/// `ComputationCommitment` holds a public preprocessed NP statement (e.g., R1CS)
#[derive(Clone)]
pub struct ComputationCommitment {
  comm: R1CSCommitment,
}

/// `ComputationDecommitment` holds information to decommit `ComputationCommitment`
pub struct ComputationDecommitment {
  decomm: R1CSDecommitment,
}

/// `Assignment` holds an assignment of values to either the inputs or variables in an `Instance`
#[derive(Clone)]
pub struct Assignment {
  assignment: Vec<Scalar>,
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
}

/// `VarsAssignment` holds an assignment of values to variables in an `Instance`
pub type VarsAssignment = Assignment;

/// `InputsAssignment` holds an assignment of values to inputs in an `Instance`
pub type InputsAssignment = Assignment;

/// `MemsAssignment` holds an assignment of values to (addr, val) pairs in an `Instance`
pub type MemsAssignment = Assignment;

/// `SNARKGens` holds public parameters for producing and verifying proofs with the Spartan SNARK
pub struct SNARKGens {
  /// Generator for witness commitment
  pub gens_r1cs_sat: R1CSGens,
  gens_r1cs_eval: R1CSCommitmentGens,
}

impl SNARKGens {
  /// Constructs a new `SNARKGens` given the size of the R1CS statement
  /// `num_nz_entries` specifies the maximum number of non-zero entries in any of the three R1CS matrices
  pub fn new(num_cons: usize, num_vars: usize, num_instances: usize, num_nz_entries: usize) -> Self {
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
  input_valid_proof: PolyEvalProof,
  output_valid_proof: PolyEvalProof,
  input_block_num_proof: PolyEvalProof,
  output_block_num_proof: PolyEvalProof,
  input_correctness_proof_list: Vec<PolyEvalProof>,
  output_correctness_proof: PolyEvalProof,
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
    func_input_width: usize,
    input_offset: usize,
    output_offset: usize,
    input: Vec<Scalar>,
    output: Scalar,
    output_exec_num: usize,
    vars_gens: &R1CSGens,
    transcript: &mut Transcript,
    random_tape: &mut RandomTape
  ) -> IOProofs {
    let r_len = (num_proofs * num_ios).log_2();
    let to_bin_array = |x: usize| (0..r_len).rev().map(|n| (x >> n) & 1).map(|i| Scalar::from(i as u64)).collect::<Vec::<Scalar>>();

    // input_valid_proof
    let (input_valid_proof, _comm) = PolyEvalProof::prove(
      exec_poly_inputs,
      None,
      &to_bin_array(0),
      &ONE,
      None,
      &vars_gens.gens_pc,
      transcript,
      random_tape,
    );
    // output_valid_proof
    let (output_valid_proof, _comm) = PolyEvalProof::prove(
      exec_poly_inputs,
      None,
      &to_bin_array(output_exec_num * num_ios),
      &ONE,
      None,
      &vars_gens.gens_pc,
      transcript,
      random_tape,
    );
    // input_block_num_proof
    let (input_block_num_proof, _comm) = PolyEvalProof::prove(
      exec_poly_inputs,
      None,
      &to_bin_array(2),
      &input_block_num,
      None,
      &vars_gens.gens_pc,
      transcript,
      random_tape,
    );
    // output_block_num_proof
    let (output_block_num_proof, _comm) = PolyEvalProof::prove(
      exec_poly_inputs,
      None,
      &to_bin_array(output_exec_num * num_ios + 2 + (num_inputs_unpadded - 1)),
      &output_block_num,
      None,
      &vars_gens.gens_pc,
      transcript,
      random_tape,
    );
    // correctness_proofs
    let mut input_correctness_proof_list = Vec::new();
    for i in 0..func_input_width {
      let (input_correctness_proof, _comm) = PolyEvalProof::prove(
        exec_poly_inputs,
        None,
        // Skips: V, _, BN, RP, SP, BP, RET
        &to_bin_array(2 + input_offset + i),
        &input[i],
        None,
        &vars_gens.gens_pc,
        transcript,
        random_tape,
      );
      input_correctness_proof_list.push(input_correctness_proof);
    }
    let (output_correctness_proof, _comm) = PolyEvalProof::prove(
      exec_poly_inputs,
      None,
      &to_bin_array(output_exec_num * num_ios + 2 + (num_inputs_unpadded - 1) + output_offset - 1),
      &output,
      None,
      &vars_gens.gens_pc,
      transcript,
      random_tape,
    );
    IOProofs {
      input_valid_proof,
      output_valid_proof,
      input_block_num_proof,
      output_block_num_proof,
      input_correctness_proof_list,
      output_correctness_proof,
    }
  }

  fn verify(
    &self,
    comm_poly_inputs: &PolyCommitment,

    num_ios: usize,
    num_inputs_unpadded: usize,
    num_proofs: usize,
    input_block_num: Scalar,
    output_block_num: Scalar,
    func_input_width: usize,
    input_offset: usize,
    output_offset: usize,
    input: Vec<Scalar>,
    output: Scalar,
    output_exec_num: usize,
    vars_gens: &R1CSGens,
    transcript: &mut Transcript,
  ) -> Result<(), ProofVerifyError> {
    let r_len = (num_proofs * num_ios).log_2();
    let to_bin_array = |x: usize| (0..r_len).rev().map(|n| (x >> n) & 1).map(|i| Scalar::from(i as u64)).collect::<Vec::<Scalar>>();

    // input_valid_proof
    self.input_valid_proof.verify_plain(
      &vars_gens.gens_pc,
      transcript,
      &to_bin_array(0),
      &ONE,
      comm_poly_inputs,
    )?;

    // output_valid_proof
    self.output_valid_proof.verify_plain(
      &vars_gens.gens_pc,
      transcript,
      &to_bin_array(output_exec_num * num_ios),
      &ONE,
      comm_poly_inputs,
    )?;

    // input_block_num_proof
    self.input_block_num_proof.verify_plain(
      &vars_gens.gens_pc,
      transcript,
      &to_bin_array(2),
      &input_block_num,
      comm_poly_inputs,
    )?;

    // output_block_num_proof
    self.output_block_num_proof.verify_plain(
      &vars_gens.gens_pc,
      transcript,
      &to_bin_array(output_exec_num * num_ios + 2 + (num_inputs_unpadded - 1)),
      &output_block_num,
      comm_poly_inputs,
    )?;

    // correctness_proofs
    for i in 0..func_input_width {
      self.input_correctness_proof_list[i].verify_plain(
        &vars_gens.gens_pc,
        transcript,
        &to_bin_array(2 + input_offset + i),
        &input[i],
        comm_poly_inputs,
      )?;
    }

    self.output_correctness_proof.verify_plain(
      &vars_gens.gens_pc,
      transcript,
      &to_bin_array(output_exec_num * num_ios + 2 + (num_inputs_unpadded - 1) + output_offset - 1),
      &output,
      comm_poly_inputs,
    )?;

    Ok(())
  }
}

// Information regarding one witness sec
#[derive(Clone)]
struct ProverWitnessSecInfo {
  // Does it have just one copy across all blocks?
  is_single: bool,
  // Does it have only one copy per block? A single witness sect must also be short
  is_short: bool,
  // Number of inputs per block
  num_inputs: Vec<usize>,

  // num_instances x num_proofs x num_inputs hypermatrix for all values
  w_mat: Vec<Vec<Vec<Scalar>>>,
  // One dense polynomial per instance
  poly_w: Vec<DensePolynomial>,
}

impl ProverWitnessSecInfo {
  fn new(w_mat: Vec<Vec<Vec<Scalar>>>, poly_w: Vec<DensePolynomial>) -> ProverWitnessSecInfo {
    let is_short = w_mat.iter().fold(true, |a, b| a && b.len() == 1);
    ProverWitnessSecInfo {
      is_single: w_mat.len() == 1 && is_short,
      is_short,
      num_inputs: w_mat.iter().map(|i| i[0].len()).collect(),
      w_mat,
      poly_w,
    }
  }

  fn dummy() -> ProverWitnessSecInfo {
    ProverWitnessSecInfo {
      is_single: false,
      is_short: false,
      num_inputs: Vec::new(),
      w_mat: Vec::new(),
      poly_w: Vec::new(),
    }
  }

  // Merge multiple ProverWitnessSec, sort them by decreasing number of proofs
  // Assume all components are sorted
  // Returns: 1. the merged ProverWitnessSec, 
  //          2. for each instance in the merged ProverWitnessSec, the component it orignally belong to
  fn merge(components: Vec<&ProverWitnessSecInfo>) -> (ProverWitnessSecInfo, Vec<usize>) {
    // No component should be single && either all components are short or none of them are short
    let is_single = false;
    let is_short = components[0].is_short;
    for i in 0..components.len() {
      assert_eq!(components[i].is_single, is_single);
      assert_eq!(components[i].is_short, is_short);
    }
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
        is_single,
        is_short,
        num_inputs: merged_num_inputs,
        w_mat: merged_w_mat,
        poly_w: merged_poly_w,
      },
      inst_map
    )
  }
}

// Information regarding one witness sec
#[derive(Clone)]
struct VerifierWitnessSecInfo {
  // Does it have just one copy across all blocks?
  is_single: bool,
  // Does it have only one copy per block? A single witness sect must also be short
  is_short: bool,
  // Number of inputs per block
  num_inputs: Vec<usize>,

  // Number of proofs per block, used by merge
  num_proofs: Vec<usize>,
  // One commitment per instance
  comm_w: Vec<PolyCommitment>
}

impl VerifierWitnessSecInfo {
  // Unfortunately, cannot obtain all metadata from the commitment
  fn new(is_short: bool, num_inputs: Vec<usize>, num_proofs: &Vec<usize>, comm_w: &Vec<PolyCommitment>) -> VerifierWitnessSecInfo {
    assert!(comm_w.len() == 0 || (num_inputs.len() == comm_w.len() && num_proofs.len() >= comm_w.len()));
    VerifierWitnessSecInfo {
      is_single: comm_w.len() == 1 && is_short,
      is_short,
      num_inputs,
      num_proofs: num_proofs[..comm_w.len()].to_vec(),
      comm_w: comm_w.clone(),
    }
  }

  fn dummy() -> VerifierWitnessSecInfo {
    VerifierWitnessSecInfo {
      is_single: false,
      is_short: false,
      num_inputs: Vec::new(),
      num_proofs: Vec::new(),
      comm_w: Vec::new(),
    }
  }

  // Merge multiple VerifierWitnessSec, sort them by decreasing number of proofs
  // Assume all components are sorted
  // Returns: 1. the merged VerifierWitnessSec, 
  //          2. for each instance in the merged VerifierWitnessSec, the component it orignally belong to
  fn merge(components: Vec<&VerifierWitnessSecInfo>) -> (VerifierWitnessSecInfo, Vec<usize>) {
    // No component should be single && either all components are short or none of them are short
    let is_single = false;
    let is_short = components[0].is_short;
    for i in 0..components.len() {
      assert_eq!(components[i].is_single, is_single);
      assert_eq!(components[i].is_short, is_short);
    }
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
        is_single,
        is_short,
        num_inputs: merged_num_inputs,
        num_proofs: merged_num_proofs,
        comm_w: merged_comm_w,
      },
      inst_map
    )
  }
}

/// `SNARK` holds a proof produced by Spartan SNARK
#[derive(Serialize, Deserialize, Debug)]
pub struct SNARK {
  block_comm_vars_list: Vec<PolyCommitment>,
  block_comm_inputs_list: Vec<PolyCommitment>,
  exec_comm_inputs: Vec<PolyCommitment>,
  addr_comm_mems: Vec<PolyCommitment>,

  perm_exec_comm_w2_list: Vec<PolyCommitment>,
  perm_block_comm_w2_list: Vec<PolyCommitment>,
  perm_comm_w3_list: Vec<PolyCommitment>,
  mem_block_comm_w3_list: Vec<PolyCommitment>,
  mem_addr_comm_w2: Vec<PolyCommitment>,
  mem_addr_comm_w3: Vec<PolyCommitment>,

  block_r1cs_sat_proof: R1CSProof,
  block_inst_evals_bound_rp: (Scalar, Scalar, Scalar),
  block_inst_evals_list: Vec<(Scalar, Scalar, Scalar)>,
  block_r1cs_eval_proof: Vec<R1CSEvalProof>,

  consis_check_r1cs_sat_proof: R1CSProof,
  consis_check_inst_evals: (Scalar, Scalar, Scalar),
  consis_check_r1cs_eval_proof: R1CSEvalProof,

  perm_root_r1cs_sat_proof: R1CSProof,
  perm_root_inst_evals: (Scalar, Scalar, Scalar),
  perm_root_r1cs_eval_proof: R1CSEvalProof,

  // If the circuit contains no memory accesses, then ignore everything about memory access
  mem_block_proofs: Option<MemBlockProofs>,

  // If the prover claims that no memory access is performed,
  // no need to construct mem addr proofs
  // However, we still need to construct mem proofs per block to ensure
  // that all executed blocks contain no memory accesses
  mem_addr_proofs: Option<MemAddrProofs>,

  // One proof for all permutations
  perm_mem_poly_r1cs_sat_proof: R1CSProof,
  perm_mem_poly_inst_evals: (Scalar, Scalar, Scalar),
  perm_mem_poly_r1cs_eval_proof: R1CSEvalProof,
  perm_mem_poly_list: Vec<Scalar>,
  proof_eval_perm_mem_prod_list: Vec<PolyEvalProof>,

  io_proof: IOProofs
}

// Proofs regarding memory accesses within each block
#[derive(Serialize, Deserialize, Debug)]
struct MemBlockProofs {
  mem_extract_r1cs_sat_proof: R1CSProof,
  mem_extract_inst_evals: (Scalar, Scalar, Scalar),
  mem_extract_r1cs_eval_proof: R1CSEvalProof,
}

// Proofs regarding memory accesses as a whole
#[derive(Serialize, Deserialize, Debug)]
struct MemAddrProofs {
  mem_cohere_r1cs_sat_proof: R1CSProof,
  mem_cohere_inst_evals: (Scalar, Scalar, Scalar),
  mem_cohere_r1cs_eval_proof: R1CSEvalProof,
}

// Sort block_num_proofs and record where each entry is
struct InstanceSortHelper {
  num_exec: usize,
  index: usize,
}
impl InstanceSortHelper {
  fn new(num_exec: usize, index: usize) -> InstanceSortHelper {
    InstanceSortHelper {
      num_exec,
      index
    }
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
  ) -> (Vec<ComputationCommitment>, Vec<ComputationDecommitment>) {
    let timer_encode = Timer::new("SNARK::encode");
    let (mut comm, mut decomm) = inst.inst.multi_commit(&gens.gens_r1cs_eval);
    timer_encode.stop();
    (
      comm.drain(..).map(|i| ComputationCommitment { comm: i }).collect(),
      decomm.drain(..).map(|i| ComputationDecommitment { decomm: i }).collect(),
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

  /// A method to produce a SNARK proof of the satisfiability of an R1CS instance
  pub fn prove(
    input_block_num: usize,
    output_block_num: usize,
    func_input_width: usize,
    input_offset: usize,
    output_offset: usize,
    input: &Vec<[u8; 32]>,
    output: &[u8; 32],
    output_exec_num: usize,

    num_vars: usize,
    num_ios: usize,
    addr_block_w3_size: usize,
    num_inputs_unpadded: usize,
    num_vars_per_block: &Vec<usize>,
    total_num_proofs_bound: usize,

    block_num_instances_bound: usize,
    block_max_num_proofs: usize,
    block_num_proofs: &Vec<usize>,
    block_inst: &mut Instance,
    block_comm: &Vec<ComputationCommitment>,
    block_decomm: &Vec<ComputationDecommitment>,
    block_gens: &SNARKGens,

    consis_num_proofs: usize,
    consis_check_num_cons_base: usize,
    consis_check_inst: &Instance,
    consis_check_comm: &ComputationCommitment,
    consis_check_decomm: &ComputationDecommitment,
    consis_check_gens: &SNARKGens,

    perm_root_inst: &Instance,
    perm_root_comm: &ComputationCommitment,
    perm_root_decomm: &ComputationDecommitment,
    perm_root_gens: &SNARKGens,

    perm_poly_num_cons_base: usize,
    perm_poly_inst: &Instance,
    perm_poly_comm: &ComputationCommitment,
    perm_poly_decomm: &ComputationDecommitment,
    perm_poly_gens: &SNARKGens,

    max_block_num_mem_accesses: usize,
    mem_extract_inst: &Instance,
    mem_extract_comm: &ComputationCommitment,
    mem_extract_decomm: &ComputationDecommitment,
    mem_extract_gens: &SNARKGens,

    total_num_mem_accesses_bound: usize,
    total_num_mem_accesses: usize,
    mem_cohere_num_cons_base: usize,
    mem_cohere_inst: &Instance,
    mem_cohere_comm: &ComputationCommitment,
    mem_cohere_decomm: &ComputationDecommitment,
    mem_cohere_gens: &SNARKGens,

    block_vars_mat: Vec<Vec<VarsAssignment>>,
    block_inputs_mat: Vec<Vec<InputsAssignment>>,
    exec_inputs_list: Vec<InputsAssignment>,
    addr_mems_list: Vec<MemsAssignment>,

    mem_block_mask: &Vec<Vec<Vec<Scalar>>>,
    mem_block_poly_mask_list: &Vec<DensePolynomial>,
    mem_block_comm_mask_list: &Vec<PolyCommitment>,

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
    assert!(consis_num_proofs <= total_num_proofs_bound);
    assert!(total_num_mem_accesses <= total_num_mem_accesses_bound);
    assert_eq!(block_num_instances_bound, mem_block_mask.len());
    assert_eq!(block_num_instances_bound, mem_block_poly_mask_list.len());
    assert_eq!(block_num_instances_bound, mem_block_comm_mask_list.len());

    // --
    // PREPROCESSING
    // --
    // unwrap the assignments
    let mut block_vars_mat = block_vars_mat.into_iter().map(|a| a.into_iter().map(|v| v.assignment).collect_vec()).collect_vec();
    let mut block_inputs_mat = block_inputs_mat.into_iter().map(|a| a.into_iter().map(|v| v.assignment).collect_vec()).collect_vec();
    let mut exec_inputs_list = exec_inputs_list.into_iter().map(|v| v.assignment).collect_vec();
    let mut addr_mems_list = addr_mems_list.into_iter().map(|v| v.assignment).collect_vec();

    // --
    // INSTANCE COMMITMENTS
    // --
    let input_block_num = Scalar::from(input_block_num as u64);
    let output_block_num = Scalar::from(output_block_num as u64);
    let input: Vec<Scalar> = input.iter().map(|i| Scalar::from_bytes(i).unwrap()).collect();
    let output: Scalar = Scalar::from_bytes(output).unwrap();
    let timer_commit = Timer::new("inst_commit");
    // Commit public parameters
    Scalar::from(func_input_width as u64).append_to_transcript(b"func_input_width", transcript);
    Scalar::from(input_offset as u64).append_to_transcript(b"input_offset", transcript);
    Scalar::from(output_offset as u64).append_to_transcript(b"output_offset", transcript);
    Scalar::from(output_exec_num as u64).append_to_transcript(b"output_exec_num", transcript);
    Scalar::from(num_ios as u64).append_to_transcript(b"num_ios", transcript);
    for n in num_vars_per_block {
      Scalar::from(*n as u64).append_to_transcript(b"num_vars_per_block", transcript);
    }
    Scalar::from(addr_block_w3_size as u64).append_to_transcript(b"addr_block_w3_size", transcript);
    Scalar::from(num_inputs_unpadded as u64).append_to_transcript(b"num_inputs_unpadded", transcript);
    Scalar::from(total_num_proofs_bound as u64).append_to_transcript(b"total_num_proofs_bound", transcript);
    Scalar::from(block_num_instances_bound as u64).append_to_transcript(b"block_num_instances_bound", transcript);
    Scalar::from(block_max_num_proofs as u64).append_to_transcript(b"block_max_num_proofs", transcript);
    Scalar::from(max_block_num_mem_accesses as u64).append_to_transcript(b"max_block_num_mem_accesses", transcript);
    Scalar::from(total_num_mem_accesses_bound as u64).append_to_transcript(b"total_num_mem_accesses_bound", transcript);
    Scalar::from(total_num_mem_accesses as u64).append_to_transcript(b"total_num_mem_accesses", transcript);
    
    // commit mem_block_mask
    for c in mem_block_comm_mask_list {
      c.append_to_transcript(b"mem_block_masks", transcript);
    }
    // commit num_proofs
    Scalar::from(block_max_num_proofs as u64).append_to_transcript(b"block_max_num_proofs", transcript);
    for n in block_num_proofs {
      Scalar::from(*n as u64).append_to_transcript(b"block_num_proofs", transcript);
    }

    // append a commitment to the computation to the transcript
    for c in block_comm {
      c.comm.append_to_transcript(b"block_comm", transcript);
    }
    consis_check_comm.comm.append_to_transcript(b"consis_comm", transcript);
    perm_root_comm.comm.append_to_transcript(b"block_comm", transcript);
    perm_poly_comm.comm.append_to_transcript(b"block_comm", transcript);
    mem_extract_comm.comm.append_to_transcript(b"block_comm", transcript);
    mem_cohere_comm.comm.append_to_transcript(b"consis_comm", transcript);

    // Commit io
    input_block_num.append_to_transcript(b"input_block_num", transcript);
    output_block_num.append_to_transcript(b"output_block_num", transcript);
    input.append_to_transcript(b"input_list", transcript);
    output.append_to_transcript(b"output_list", transcript);

    timer_commit.stop();

    // --
    // BLOCK SORT
    // --
    let timer_sort = Timer::new("block_sort");
    // Block_num_instance is the number of non-zero entries in block_num_proofs
    let block_num_instances = block_num_proofs.iter().fold(0, |i, j| if *j > 0 { i + 1 } else { i });
    // Sort the following based on block_num_proofs:
    // - block_num_proofs
    // - block_inst, block_comm, block_decomm
    // - block_num_mem_accesses
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
    block_inst.sort(block_num_instances, &index);
    let block_decomm: &Vec<&ComputationDecommitment> = &(0..block_num_instances).map(|i| &block_decomm[index[i]]).collect();
    let mem_block_mask: Vec<Vec<Vec<Scalar>>> = (0..block_num_instances).map(|i| mem_block_mask[index[i]].clone()).collect();
    let mem_block_poly_mask_list: Vec<DensePolynomial> = (0..block_num_instances).map(|i| mem_block_poly_mask_list[index[i]].clone()).collect();

    // --
    // PADDING
    // --
    let zero = ZERO;
    let dummy_inputs = vec![zero; num_ios];
    // For every block that num_proofs is not a power of 2, pad vars_mat and inputs_mat until the length is a power of 2
    let block_max_num_proofs = block_max_num_proofs.next_power_of_two();
    for i in 0..block_num_instances {
      let dummy_vars = vec![zero; block_vars_mat[i][0].len()];
      let gap = block_num_proofs[i].next_power_of_two() - block_num_proofs[i];
      block_vars_mat[i].extend(vec![dummy_vars.clone(); gap]);
      block_inputs_mat[i].extend(vec![dummy_inputs.clone(); gap]);
      block_num_proofs[i] = block_num_proofs[i].next_power_of_two();
    }
    // Pad exec_inputs with dummys so the length is a power of 2
    exec_inputs_list.extend(vec![dummy_inputs; consis_num_proofs.next_power_of_two() - consis_num_proofs]);
    let consis_num_proofs = consis_num_proofs.next_power_of_two();

    // Pad addr_mems with dummys so the length is a power of 2
    if total_num_mem_accesses > 0 {
      let dummy_addr = vec![zero; 4];
      addr_mems_list.extend(vec![dummy_addr; total_num_mem_accesses.next_power_of_two() - total_num_mem_accesses]);
    }
    let total_num_mem_accesses = if total_num_mem_accesses == 0 { 0 } else { total_num_mem_accesses.next_power_of_two() };

    // Compute perm_size_bound & perm_num_proofs
    let perm_size_bound = max(total_num_proofs_bound, total_num_mem_accesses_bound) * 4;
    let mut perm_num_proofs = [vec![consis_num_proofs], block_num_proofs.to_vec()].concat();
    // Pad num_proofs with 1 until the next power of 2
    block_num_proofs.extend(vec![1; block_num_instances.next_power_of_two() - block_num_instances]);
    perm_num_proofs.extend(vec![1; (block_num_instances + 1).next_power_of_two() - (block_num_instances + 1)]);
    let block_num_proofs = &block_num_proofs;
    timer_sort.stop();

    // --
    // WITNESS COMMITMENTS
    // --
    let timer_commit = Timer::new("input_commit");
    let (
      block_poly_vars_list,
      block_comm_vars_list,
      block_poly_inputs_list,
      block_comm_inputs_list,
      exec_poly_inputs,
      exec_comm_inputs
    ) = {

      // commit the witnesses and inputs separately instance-by-instance
      let mut block_poly_vars_list = Vec::new();
      let mut block_comm_vars_list = Vec::new();
      let mut block_poly_inputs_list = Vec::new();
      let mut block_comm_inputs_list = Vec::new();

      for p in 0..block_num_instances {
        let (block_poly_vars, block_comm_vars) = {
          // Flatten the witnesses into a Q_i * X list
          let vars_list_p = block_vars_mat[p].iter().fold(Vec::new(), |a, b| [a, b.to_vec()].concat());
          // create a multilinear polynomial using the supplied assignment for variables
          let block_poly_vars = DensePolynomial::new(vars_list_p);

          // produce a commitment to the satisfying assignment
          let (block_comm_vars, _blinds_vars) = block_poly_vars.commit(&vars_gens.gens_pc, None);

          // add the commitment to the prover's transcript
          block_comm_vars.append_to_transcript(b"poly_commitment", transcript);
          (block_poly_vars, block_comm_vars)
        };
        
        let (block_poly_inputs, block_comm_inputs) = {
          // Flatten the inputs into a Q_i * X list
          let inputs_list_p = block_inputs_mat[p].iter().fold(Vec::new(), |a, b| [a, b.to_vec()].concat());
          // create a multilinear polynomial using the supplied assignment for variables
          let block_poly_inputs = DensePolynomial::new(inputs_list_p);

          // produce a commitment to the satisfying assignment
          let (block_comm_inputs, _blinds_inputs) = block_poly_inputs.commit(&vars_gens.gens_pc, None);

          // add the commitment to the prover's transcript
          block_comm_inputs.append_to_transcript(b"poly_commitment", transcript);
          (block_poly_inputs, block_comm_inputs)
        };
        block_poly_vars_list.push(block_poly_vars);
        block_comm_vars_list.push(block_comm_vars);
        block_poly_inputs_list.push(block_poly_inputs);
        block_comm_inputs_list.push(block_comm_inputs);
      }

      let (exec_poly_inputs, exec_comm_inputs) = {
        let exec_inputs = exec_inputs_list.iter().fold(Vec::new(), |a, b| [a, b.to_vec()].concat());
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
        block_poly_inputs_list,
        block_comm_inputs_list,
        vec![exec_poly_inputs],
        vec![exec_comm_inputs]
      )
    };
    let (
      addr_poly_mems,
      addr_comm_mems
    ) = {
      if total_num_mem_accesses > 0 {
        let (addr_poly_mems, addr_comm_mems) = {
          let addr_mems = addr_mems_list.iter().fold(Vec::new(), |a, b| [a, b.to_vec()].concat());
          // create a multilinear polynomial using the supplied assignment for variables
          let addr_poly_mems = DensePolynomial::new(addr_mems);

          // produce a commitment to the satisfying assignment
          let (addr_comm_mems, _blinds_inputs) = addr_poly_mems.commit(&vars_gens.gens_pc, None);

          // add the commitment to the prover's transcript
          addr_comm_mems.append_to_transcript(b"poly_commitment", transcript);
          (addr_poly_mems, addr_comm_mems)
        };
        (
          vec![addr_poly_mems], 
          vec![addr_comm_mems],
        )
      } else {
        (
          Vec::new(),
          Vec::new()
        )
      }
    };
    timer_commit.stop();

    // --
    // CHALLENGES AND WITNESSES FOR PERMUTATION
    // --

    // Non-memory
    let timer_gen = Timer::new("witness_gen");
    let (
      comb_tau,
      comb_r,
      perm_w0_prover,
      perm_exec_w2_prover,
      perm_exec_comm_w2_list,
      perm_block_w2_prover,
      perm_block_comm_w2_list,
      perm_w3_prover,
      perm_comm_w3_list,
    ) = {
      let comb_tau = transcript.challenge_scalar(b"challenge_tau");
      let comb_r = transcript.challenge_scalar(b"challenge_r");
      
      // w0 is (tau, r, r^2, ...) for the first 2 * num_inputs_unpadded entries
      // set the first entry to 1 for multiplication and later revert it to tau
      let mut perm_w0 = vec![comb_tau];
      let mut r_tmp = comb_r;
      for _ in 1..2 * num_inputs_unpadded {
        perm_w0.push(r_tmp);
        r_tmp *= comb_r;
      }
      perm_w0.extend(vec![zero; num_ios - 2 * num_inputs_unpadded]);
      
      // FOR PERM
      // w2 is I, O, ZO, r * i1, r^2 * i2, r^3 * i3, ...
      // where I = v * (v + i0 + r * i1 + r^2 * i2 + ...),
      //       ZO * r^n = r^n * o0 + r^(n + 1) * o1, ...,
      //       O = v * (v + ZO)
      // are used by the consistency check
      let mut perm_exec_w2: Vec<Vec<Scalar>> = exec_inputs_list.iter().map(|input|
        [
          vec![zero; 3],
          (1..2 * num_inputs_unpadded - 2).map(|j| perm_w0[j] * input[j + 2]).collect(),
          vec![zero; num_ios - 2 * num_inputs_unpadded]
        ].concat()
      ).collect();
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

      let mut perm_block_w2: Vec<Vec<Vec<Scalar>>> = block_inputs_mat.iter().map(
        |i| i.iter().map(|input|
          [
            vec![zero; 3],
            (1..2 * num_inputs_unpadded - 2).map(|j| perm_w0[j] * input[j + 2]).collect(),
            vec![zero; num_ios - 2 * num_inputs_unpadded]
          ].concat()
        ).collect()
      ).collect();
      for p in 0..block_num_instances {
        for q in 0..block_num_proofs[p] {
          perm_block_w2[p][q][0] = block_inputs_mat[p][q][0];
          perm_block_w2[p][q][1] = block_inputs_mat[p][q][0];
          for i in 0..num_inputs_unpadded - 1 {
            let perm = if i == 0 { ONE } else { perm_w0[i] };
            perm_block_w2[p][q][0] += perm * block_inputs_mat[p][q][2 + i];
            perm_block_w2[p][q][2] += perm * block_inputs_mat[p][q][2 + (num_inputs_unpadded - 1) + i];
          }
          perm_block_w2[p][q][0] *= block_inputs_mat[p][q][0];
          let ZO = perm_block_w2[p][q][2];
          perm_block_w2[p][q][1] += ZO;
          perm_block_w2[p][q][1] *= block_inputs_mat[p][q][0];
        }
      }
      
      // Proofs of w3 are of format (exec, blocks0, block1, ...)
      // w3 is [v, x, pi, D]
      let mut perm_w3: Vec<Vec<Vec<Scalar>>> = Vec::new();
      for p in 0..block_num_instances + 1 {
        perm_w3.push(vec![Vec::new(); perm_num_proofs[p]]);
        for q in (0..perm_num_proofs[p]).rev() {
          perm_w3[p][q] = vec![ZERO; 4];
          if p == 0 {
            // For exec
            perm_w3[p][q][0] = exec_inputs_list[q][0];
            perm_w3[p][q][1] = perm_w3[p][q][0] * (comb_tau - perm_exec_w2[q][3..].iter().fold(ZERO, |a, b| a + b) - exec_inputs_list[q][2]);
          } else {
            // For blocks
            perm_w3[p][q][0] = block_inputs_mat[p - 1][q][0];
            perm_w3[p][q][1] = perm_w3[p][q][0] * (comb_tau - perm_block_w2[p - 1][q][3..].iter().fold(ZERO, |a, b| a + b) - block_inputs_mat[p - 1][q][2]);
          }
          if q != perm_num_proofs[p] - 1 {
            perm_w3[p][q][3] = perm_w3[p][q][1] * (perm_w3[p][q + 1][2] + ONE - perm_w3[p][q + 1][0]);
          } else {
            perm_w3[p][q][3] = perm_w3[p][q][1];
          }
          perm_w3[p][q][2] = perm_w3[p][q][0] * perm_w3[p][q][3];
        }
      }

      // create a multilinear polynomial using the supplied assignment for variables
      let perm_poly_w0 = DensePolynomial::new(perm_w0.clone());
      // produce a commitment to the satisfying assignment
      let (perm_comm_w0, _blinds_vars) = perm_poly_w0.commit(&vars_gens.gens_pc, None);
      // add the commitment to the prover's transcript
      perm_comm_w0.append_to_transcript(b"poly_commitment", transcript);

      // commit the witnesses and inputs separately instance-by-instance
      let (
        perm_exec_poly_w2,
        perm_exec_comm_w2,
      ) = {
        let (perm_exec_poly_w2, perm_exec_comm_w2) = {
          // Flatten the witnesses into a Q_i * X list
          let w2_list_p = perm_exec_w2.iter().fold(Vec::new(), |a, b| [a, b.to_vec()].concat());
          // create a multilinear polynomial using the supplied assignment for variables
          let perm_exec_poly_w2 = DensePolynomial::new(w2_list_p);

          // produce a commitment to the satisfying assignment
          let (perm_exec_comm_w2, _blinds_vars) = perm_exec_poly_w2.commit(&vars_gens.gens_pc, None);

          // add the commitment to the prover's transcript
          perm_exec_comm_w2.append_to_transcript(b"poly_commitment", transcript);
          (perm_exec_poly_w2, perm_exec_comm_w2)
        };

        (
          perm_exec_poly_w2,
          perm_exec_comm_w2,
        )
      };

      let mut perm_block_poly_w2_list = Vec::new();
      let mut perm_block_comm_w2_list = Vec::new();
      let mut perm_poly_w3_list = Vec::new();
      let mut perm_comm_w3_list = Vec::new();

      for p in 0..block_num_instances {
        let (perm_block_poly_w2, perm_block_comm_w2) = {
          // Flatten the witnesses into a Q_i * X list
          let w2_list_p = perm_block_w2[p].iter().fold(Vec::new(), |a, b| [a, b.to_vec()].concat());
          // create a multilinear polynomial using the supplied assignment for variables
          let perm_block_poly_w2 = DensePolynomial::new(w2_list_p);
          // produce a commitment to the satisfying assignment
          let (perm_block_comm_w2, _blinds_vars) = perm_block_poly_w2.commit(&vars_gens.gens_pc, None);

          // add the commitment to the prover's transcript
          perm_block_comm_w2.append_to_transcript(b"poly_commitment", transcript);
          (perm_block_poly_w2, perm_block_comm_w2)
        };
        perm_block_poly_w2_list.push(perm_block_poly_w2);
        perm_block_comm_w2_list.push(perm_block_comm_w2);
      }

      for p in 0..block_num_instances + 1 {  
        let (perm_poly_w3, perm_comm_w3) = {
          // Flatten the witnesses into a Q_i * X list
          let w3_list_p = perm_w3[p].iter().fold(Vec::new(), |a, b| [a, b.to_vec()].concat());
          // create a multilinear polynomial using the supplied assignment for variables
          let perm_poly_w3 = DensePolynomial::new(w3_list_p);

          // produce a commitment to the satisfying assignment
          let (perm_comm_w3, _blinds_vars) = perm_poly_w3.commit(&vars_gens.gens_pc, None);

          // add the commitment to the prover's transcript
          perm_comm_w3.append_to_transcript(b"poly_commitment", transcript);
          (perm_poly_w3, perm_comm_w3)
        };
        perm_poly_w3_list.push(perm_poly_w3);
        perm_comm_w3_list.push(perm_comm_w3);
      }

      let perm_w0_prover = ProverWitnessSecInfo::new(vec![vec![perm_w0]], vec![perm_poly_w0]);
      let perm_exec_w2_prover = ProverWitnessSecInfo::new(vec![perm_exec_w2], vec![perm_exec_poly_w2]);
      let perm_block_w2_prover = ProverWitnessSecInfo::new(perm_block_w2, perm_block_poly_w2_list);
      let perm_w3_prover = ProverWitnessSecInfo::new(perm_w3, perm_poly_w3_list);

      (
        comb_tau,
        comb_r,

        perm_w0_prover,
        perm_exec_w2_prover,
        vec![perm_exec_comm_w2],
        perm_block_w2_prover,
        perm_block_comm_w2_list,
        perm_w3_prover,
        perm_comm_w3_list,
      )
    };

    // Memory-per-block
    let (
      mem_block_w3_prover,
      mem_block_comm_w3_list
    ) = {
      if total_num_mem_accesses_bound > 0 {
        // mask is unary representation of block_num_mem_accesses[p]
        let zero = ZERO;
        let one = ONE;

        // w3 is (v, x, pi, D, MR, MD, MC, MR, MR, MC, ...)
        let mut mem_block_w3 = Vec::new();
        let V_addr = |i: usize| 1 + 2 * i;
        let V_val = |i: usize| 2 + 2 * i;
        let V_MR = |i: usize| 4 + 3 * i;
        let V_MD = |i: usize| 5 + 3 * i;
        let V_MC = |i: usize| 6 + 3 * i;
        for p in 0..block_num_instances {
          mem_block_w3.push(vec![Vec::new(); block_num_proofs[p]]);
          for q in (0..block_num_proofs[p]).rev() {
            mem_block_w3[p][q] = vec![zero; addr_block_w3_size];
            mem_block_w3[p][q][0] = block_vars_mat[p][q][0];
            // Compute MR, MD, MC
            for i in 0..max_block_num_mem_accesses {
              // MR = r * val
              let val = if block_vars_mat[p][q].len() > V_val(i) { block_vars_mat[p][q][V_val(i)] } else { ZERO };
              mem_block_w3[p][q][V_MR(i)] = comb_r * val;
              // MD = mask * (tau - addr - MR)
              let addr = if block_vars_mat[p][q].len() > V_addr(i) { block_vars_mat[p][q][V_addr(i)] } else { ZERO };
              let t = comb_tau - addr - mem_block_w3[p][q][V_MR(i)];
              mem_block_w3[p][q][V_MD(i)] = mem_block_mask[p][0][i] * t;
              // MC = (1 or MC[i-1]) * (MD + 1 - mask)
              let t = mem_block_w3[p][q][V_MD(i)] + one - mem_block_mask[p][0][i];
              mem_block_w3[p][q][V_MC(i)] = 
                if i == 0 { block_vars_mat[p][q][0] * t }
                else { mem_block_w3[p][q][V_MC(i - 1)] * t };
            }
            // Compute x
            mem_block_w3[p][q][1] = mem_block_w3[p][q][V_MC(max_block_num_mem_accesses - 1)];
            // Compute D and pi
            if q != block_num_proofs[p] - 1 {
              mem_block_w3[p][q][3] = mem_block_w3[p][q][1] * (mem_block_w3[p][q + 1][2] + one - mem_block_w3[p][q + 1][0]);
            } else {
              mem_block_w3[p][q][3] = mem_block_w3[p][q][1];
            }
            mem_block_w3[p][q][2] = mem_block_w3[p][q][0] * mem_block_w3[p][q][3];
          }
        }

        // commit the witnesses and inputs separately instance-by-instance
        let mut mem_block_poly_w3_list = Vec::new();
        let mut mem_block_comm_w3_list = Vec::new();

        for p in 0..block_num_instances {
          let (mem_block_poly_w3, mem_block_comm_w3) = {
            // Flatten the witnesses into a Q_i * X list
            let w1_list_p = mem_block_w3[p].iter().fold(Vec::new(), |a, b| [a, b.to_vec()].concat());
            // create a multilinear polynomial using the supplied assignment for variables
            let mem_block_poly_w3 = DensePolynomial::new(w1_list_p);
            // produce a commitment to the satisfying assignment
            let (mem_block_comm_w3, _blinds_vars) = mem_block_poly_w3.commit(&vars_gens.gens_pc, None);

            // add the commitment to the prover's transcript
            mem_block_comm_w3.append_to_transcript(b"poly_commitment", transcript);
            (mem_block_poly_w3, mem_block_comm_w3)
          };
          mem_block_poly_w3_list.push(mem_block_poly_w3);
          mem_block_comm_w3_list.push(mem_block_comm_w3);
        }

        let mem_block_w3_prover = ProverWitnessSecInfo::new(mem_block_w3, mem_block_poly_w3_list);

        (
          mem_block_w3_prover,
          mem_block_comm_w3_list
        )
      } else {
        (
          ProverWitnessSecInfo::dummy(),
          Vec::new()
        )
      }
    };

    // Memory-as-a-whole
    let (
      mem_addr_w2_prover,
      mem_addr_comm_w2,
      mem_addr_w3_prover,
      mem_addr_comm_w3
    ) = {
      if total_num_mem_accesses > 0 {
        // mem_addr_w2 is (I, O, ZO, r * val)
        // where I = v * (v + addr + r * val),
        //       ZO = 0,
        //       O = v * v = v
        // are used by (dummy) consistency check
        let mut mem_addr_w2 = Vec::new();
        for q in 0..total_num_mem_accesses {
          mem_addr_w2.push(vec![ZERO; 4]);
          mem_addr_w2[q][3] = comb_r * addr_mems_list[q][3];
          mem_addr_w2[q][0] = addr_mems_list[q][0] * (addr_mems_list[q][0] + addr_mems_list[q][2] + mem_addr_w2[q][3]);
          mem_addr_w2[q][1] = addr_mems_list[q][0];
        }
        // mem_addr_w3 is (v, x, pi, D) 
        let mut mem_addr_w3 = vec![vec![ZERO; 4]; total_num_mem_accesses];
        for q in (0..total_num_mem_accesses).rev() {
          // v
          mem_addr_w3[q][0] = addr_mems_list[q][0];
          // x = v * (tau - addr - r * val)
          mem_addr_w3[q][1] = addr_mems_list[q][0] * (comb_tau - addr_mems_list[q][2] - comb_r * addr_mems_list[q][3]);
          // pi and D
          if q != total_num_mem_accesses - 1 {
            mem_addr_w3[q][3] = mem_addr_w3[q][1] * (mem_addr_w3[q + 1][2] + ONE - mem_addr_w3[q + 1][0]);
          } else {
            mem_addr_w3[q][3] = mem_addr_w3[q][1];
          }
          mem_addr_w3[q][2] = mem_addr_w3[q][0] * mem_addr_w3[q][3];
        }

        let (
          mem_addr_poly_w2,
          mem_addr_comm_w2,
          mem_addr_poly_w3,
          mem_addr_comm_w3,
        ) = {
          let (mem_addr_poly_w2, mem_addr_comm_w2) = {
            // Flatten the witnesses into a Q_i * X list
            let w2_list_p = mem_addr_w2.iter().fold(Vec::new(), |a, b| [a, b.to_vec()].concat());
            // create a multilinear polynomial using the supplied assignment for variables
            let mem_addr_poly_w2 = DensePolynomial::new(w2_list_p);

            // produce a commitment to the satisfying assignment
            let (mem_addr_comm_w2, _blinds_vars) = mem_addr_poly_w2.commit(&vars_gens.gens_pc, None);

            // add the commitment to the prover's transcript
            mem_addr_comm_w2.append_to_transcript(b"poly_commitment", transcript);
            (mem_addr_poly_w2, mem_addr_comm_w2)
          };
          
          let (mem_addr_poly_w3, mem_addr_comm_w3) = {
            // Flatten the witnesses into a Q_i * X list
            let w3_list_p = mem_addr_w3.iter().fold(Vec::new(), |a, b| [a, b.to_vec()].concat());
            // create a multilinear polynomial using the supplied assignment for variables
            let mem_addr_poly_w3 = DensePolynomial::new(w3_list_p);

            // produce a commitment to the satisfying assignment
            let (mem_addr_comm_w3, _blinds_vars) = mem_addr_poly_w3.commit(&vars_gens.gens_pc, None);

            // add the commitment to the prover's transcript
            mem_addr_comm_w3.append_to_transcript(b"poly_commitment", transcript);
            (mem_addr_poly_w3, mem_addr_comm_w3)
          };

          (
            mem_addr_poly_w2,
            mem_addr_comm_w2,
            mem_addr_poly_w3,
            mem_addr_comm_w3,
          )
        };

        let mem_addr_w2_prover = ProverWitnessSecInfo::new(vec![mem_addr_w2], vec![mem_addr_poly_w2]);
        let mem_addr_w3_prover = ProverWitnessSecInfo::new(vec![mem_addr_w3], vec![mem_addr_poly_w3]);

        (
          mem_addr_w2_prover,
          vec![mem_addr_comm_w2],
          mem_addr_w3_prover,
          vec![mem_addr_comm_w3]
        )
      } else {
        (
          ProverWitnessSecInfo::dummy(),
          Vec::new(),
          ProverWitnessSecInfo::dummy(),
          Vec::new()
        )
      }
    };
    timer_gen.stop();

    // Construct vars_info for inputs
    let block_vars_prover = ProverWitnessSecInfo::new(block_vars_mat, block_poly_vars_list);
    let block_inputs_prover = ProverWitnessSecInfo::new(block_inputs_mat, block_poly_inputs_list);
    let exec_inputs_prover = ProverWitnessSecInfo::new(vec![exec_inputs_list], exec_poly_inputs);
    let addr_mems_prover = if total_num_mem_accesses_bound > 0 {
      ProverWitnessSecInfo::new(vec![addr_mems_list], addr_poly_mems)
    } else {
      ProverWitnessSecInfo::dummy()
    };
    let mem_block_mask_prover = ProverWitnessSecInfo::new(mem_block_mask, mem_block_poly_mask_list);

    // --
    // BLOCK CORRECTNESS
    // --

    let timer_proof = Timer::new("Block Correctness");
    let (block_r1cs_sat_proof, block_challenges) = {
      let (proof, block_challenges) = {
        R1CSProof::prove(
          block_num_instances,
          block_max_num_proofs,
          block_num_proofs,
          num_vars,
          vec![&block_inputs_prover, &block_vars_prover],
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
    let (block_inst_evals_bound_rp, block_inst_evals_list, block_r1cs_eval_proof) = {
      let [rp, _, rx, ry] = block_challenges;
      let inst = block_inst;
      let timer_eval = Timer::new("eval_sparse_polys");

      let mut r1cs_eval_proof_list = Vec::new();
      let (inst_evals_list, inst_evals_bound_rp) = inst.inst.multi_evaluate(&rp, &rx, &ry);
      timer_eval.stop();
      for i in 0..block_num_instances {
        let inst_evals = inst_evals_list[i];
        let (Ar, Br, Cr) = &inst_evals;
        Ar.append_to_transcript(b"Ar_claim", transcript);
        Br.append_to_transcript(b"Br_claim", transcript);
        Cr.append_to_transcript(b"Cr_claim", transcript);

        let r1cs_eval_proof = {
          let proof = R1CSEvalProof::prove(
            &block_decomm[i].decomm,
            &rx,
            &ry,
            &inst_evals,
            &block_gens.gens_r1cs_eval,
            transcript,
            &mut random_tape,
          );

          let proof_encoded: Vec<u8> = bincode::serialize(&proof).unwrap();
          Timer::print(&format!("len_r1cs_eval_proof {:?}", proof_encoded.len()));
          proof
        };
        r1cs_eval_proof_list.push(r1cs_eval_proof);
      }


      (inst_evals_bound_rp, inst_evals_list, r1cs_eval_proof_list)
    };
    timer_proof.stop();

    // --
    // CONSIS_CHECK
    // --

    let timer_proof = Timer::new("Consis Check");
    let (consis_check_r1cs_sat_proof, consis_check_challenges) = {
      let (proof, consis_check_challenges) = {
        R1CSProof::prove_single(
          1,
          consis_check_num_cons_base,
          2,
          total_num_proofs_bound,
          consis_num_proofs,
          &vec![consis_num_proofs],
          &consis_check_inst.inst,
          &vars_gens,
          &vec![num_ios],
          &perm_exec_w2_prover.w_mat,
          &perm_exec_w2_prover.poly_w,
          transcript,
          &mut random_tape,
        )
      };

      let proof_encoded: Vec<u8> = bincode::serialize(&proof).unwrap();
      Timer::print(&format!("len_r1cs_sat_proof {:?}", proof_encoded.len()));

      (proof, consis_check_challenges)
    };

    // Final evaluation on CONSIS_CHECK
    let (consis_check_inst_evals, consis_check_r1cs_eval_proof) = {
      let [_, rx, ry] = &consis_check_challenges;
      let inst = consis_check_inst;
      let timer_eval = Timer::new("eval_sparse_polys");
      let inst_evals = {
        let (Ar, Br, Cr) = inst.inst.evaluate(rx, ry);
        Ar.append_to_transcript(b"Ar_claim", transcript);
        Br.append_to_transcript(b"Br_claim", transcript);
        Cr.append_to_transcript(b"Cr_claim", transcript);
        (Ar, Br, Cr)
      };
      timer_eval.stop();

      let r1cs_eval_proof = {
        let proof = R1CSEvalProof::prove(
          &consis_check_decomm.decomm,
          &rx,
          &ry,
          &inst_evals,
          &consis_check_gens.gens_r1cs_eval,
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
    // MEM_BLOCK
    // --

    let mem_block_proofs = {
      if total_num_mem_accesses_bound > 0 {
        // --
        // MEM_EXTRACT
        // --
        let timer_proof = Timer::new("Mem Extract");
        let (mem_extract_r1cs_sat_proof, mem_extract_challenges) = {
          let (proof, mem_extract_challenges) = {
            R1CSProof::prove(
              block_num_instances,
              block_max_num_proofs,
              block_num_proofs,
              addr_block_w3_size,
              vec![&perm_w0_prover, &mem_block_mask_prover, &block_vars_prover, &mem_block_w3_prover],
              &mem_extract_inst.inst,
              &vars_gens,
              transcript,
              &mut random_tape,
            )
          };
    
          let proof_encoded: Vec<u8> = bincode::serialize(&proof).unwrap();
          Timer::print(&format!("len_r1cs_sat_proof {:?}", proof_encoded.len()));
    
          (proof, mem_extract_challenges)
        };
    
        // Final evaluation on MEM_EXTRACT
        let (mem_extract_inst_evals, mem_extract_r1cs_eval_proof) = {
          let [_, _, rx, ry] = mem_extract_challenges;
          let inst = mem_extract_inst;
          let timer_eval = Timer::new("eval_sparse_polys");
          let inst_evals = {
            let (Ar, Br, Cr) = inst.inst.evaluate(&rx, &ry);
            Ar.append_to_transcript(b"Ar_claim", transcript);
            Br.append_to_transcript(b"Br_claim", transcript);
            Cr.append_to_transcript(b"Cr_claim", transcript);
            (Ar, Br, Cr)
          };
          timer_eval.stop();
    
          let r1cs_eval_proof = {
            let proof = R1CSEvalProof::prove(
              &mem_extract_decomm.decomm,
              &rx,
              &ry,
              &inst_evals,
              &mem_extract_gens.gens_r1cs_eval,
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

        Some(MemBlockProofs {
          mem_extract_r1cs_sat_proof,
          mem_extract_inst_evals,
          mem_extract_r1cs_eval_proof,
        })
      } else {
        None
      }
    };

    // --
    // MEM_ADDR
    // --

    let mem_addr_proofs = {
      if total_num_mem_accesses > 0 {
        // --
        // MEM_COHERE
        // --
        let timer_proof = Timer::new("Mem Cohere");
        let (mem_cohere_r1cs_sat_proof, mem_cohere_challenges) = {
          let (proof, mem_cohere_challenges) = {
            R1CSProof::prove_single(
              1,
              mem_cohere_num_cons_base,
              4,
              total_num_mem_accesses_bound,
              total_num_mem_accesses,
              &vec![total_num_mem_accesses],
              &mem_cohere_inst.inst,
              &vars_gens,
              &vec![4],
              &addr_mems_prover.w_mat,
              &addr_mems_prover.poly_w,
              transcript,
              &mut random_tape,
            )
          };
    
          let proof_encoded: Vec<u8> = bincode::serialize(&proof).unwrap();
          Timer::print(&format!("len_r1cs_sat_proof {:?}", proof_encoded.len()));
    
          (proof, mem_cohere_challenges)
        };
    
        // Final evaluation on MEM_COHERE
        let (mem_cohere_inst_evals, mem_cohere_r1cs_eval_proof) = {
          let [_, rx, ry] = &mem_cohere_challenges;
          let inst = mem_cohere_inst;
          let timer_eval = Timer::new("eval_sparse_polys");
          let inst_evals = {
            let (Ar, Br, Cr) = inst.inst.evaluate(rx, ry);
            Ar.append_to_transcript(b"Ar_claim", transcript);
            Br.append_to_transcript(b"Br_claim", transcript);
            Cr.append_to_transcript(b"Cr_claim", transcript);
            (Ar, Br, Cr)
          };
          timer_eval.stop();
    
          let r1cs_eval_proof = {
            let proof = R1CSEvalProof::prove(
              &mem_cohere_decomm.decomm,
              &rx,
              &ry,
              &inst_evals,
              &mem_cohere_gens.gens_r1cs_eval,
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

        Some(MemAddrProofs {
          mem_cohere_r1cs_sat_proof,
          mem_cohere_inst_evals,
          mem_cohere_r1cs_eval_proof,
        })
      } else {
        None
      }
    };

    // --
    // PERM_BLOCK_ROOT, PERM_EXEC_ROOT, MEM_ADDR_ROOT
    // --
    let perm_size = max(consis_num_proofs, total_num_mem_accesses);

    let timer_proof = Timer::new("Perm Root");
    let (perm_root_w1_prover, _) = ProverWitnessSecInfo::merge(vec![&exec_inputs_prover, &block_inputs_prover, &addr_mems_prover]);
    let (perm_root_w2_prover, _) = ProverWitnessSecInfo::merge(vec![&perm_exec_w2_prover, &perm_block_w2_prover, &mem_addr_w2_prover]);
    let (perm_root_w3_prover, _) = ProverWitnessSecInfo::merge(vec![&perm_w3_prover, &mem_addr_w3_prover]);
    let perm_root_num_instances = perm_root_w1_prover.w_mat.len();
    let mut perm_root_num_proofs: Vec<usize> = perm_root_w1_prover.w_mat.iter().map(|i| i.len()).collect();
    perm_root_num_proofs.extend(vec![1; perm_root_num_instances.next_power_of_two() - perm_root_num_instances]);
    let (perm_root_r1cs_sat_proof, perm_root_challenges) = {
      let (proof, perm_root_challenges) = {
        R1CSProof::prove(
          perm_root_num_instances,
          perm_size,
          &perm_root_num_proofs,
          num_ios,
          vec![&perm_w0_prover, &perm_root_w1_prover, &perm_root_w2_prover, &perm_root_w3_prover],
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
        (Ar, Br, Cr)
      };
      timer_eval.stop();

      let r1cs_eval_proof = {
        let proof = R1CSEvalProof::prove(
          &perm_root_decomm.decomm,
          &rx,
          &ry,
          &inst_evals,
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
    // PERM_BLOCK_POLY, PERM_EXEC_POLY, MEM_BLOCK_POLY, MEM_ADDR_POLY
    // --

    let timer_proof = Timer::new("Perm Mem Poly");
    let (perm_mem_w3_prover, inst_map) = ProverWitnessSecInfo::merge(vec![&perm_w3_prover, &mem_block_w3_prover, &mem_addr_w3_prover]);
    let perm_mem_num_instances = perm_mem_w3_prover.w_mat.len();
    let mut perm_mem_num_proofs: Vec<usize> = perm_mem_w3_prover.w_mat.iter().map(|i| i.len()).collect();
    perm_mem_num_proofs.extend(vec![1; perm_mem_num_instances.next_power_of_two() - perm_mem_num_instances]);
    // mem_block has size addr_block_w3_size, everything else takes size 4
    let perm_mem_num_inputs = inst_map.iter().map(|i| if *i == 1 { addr_block_w3_size } else { 4 }).collect();
    let (perm_mem_poly_r1cs_sat_proof, perm_mem_poly_challenges) = {
      let (proof, perm_mem_poly_challenges) = {
        R1CSProof::prove_single(
          perm_mem_num_instances,
          perm_poly_num_cons_base,
          4,
          // We need to feed the compile-time bound because that is the size of the constraints
          // Unlike other instances, where the runtime bound is sufficient because that's the number of copies
          perm_size_bound,
          perm_size,
          &perm_mem_num_proofs,
          &perm_poly_inst.inst,
          &vars_gens,
          &perm_mem_num_inputs,
          &perm_mem_w3_prover.w_mat,
          &perm_mem_w3_prover.poly_w,
          transcript,
          &mut random_tape,
        )
      };

      let proof_encoded: Vec<u8> = bincode::serialize(&proof).unwrap();
      Timer::print(&format!("len_r1cs_sat_proof {:?}", proof_encoded.len()));

      (proof, perm_mem_poly_challenges)
    };

    // Final evaluation on PERM_POLY
    let (perm_mem_poly_inst_evals, perm_mem_poly_r1cs_eval_proof) = {
      let [_, rx, ry] = &perm_mem_poly_challenges;
      let inst = perm_poly_inst;
      let timer_eval = Timer::new("eval_sparse_polys");
      let inst_evals = {
        let (Ar, Br, Cr) = inst.inst.evaluate(rx, ry);
        Ar.append_to_transcript(b"Ar_claim", transcript);
        Br.append_to_transcript(b"Br_claim", transcript);
        Cr.append_to_transcript(b"Cr_claim", transcript);
        (Ar, Br, Cr)
      };
      timer_eval.stop();

      let r1cs_eval_proof = {
        let proof = R1CSEvalProof::prove(
          &perm_poly_decomm.decomm,
          rx,
          ry,
          &inst_evals,
          &perm_poly_gens.gens_r1cs_eval,
          transcript,
          &mut random_tape,
        );

        let proof_encoded: Vec<u8> = bincode::serialize(&proof).unwrap();
        Timer::print(&format!("len_r1cs_eval_proof {:?}", proof_encoded.len()));
        proof
      };

      
      (inst_evals, r1cs_eval_proof)
    };

    // Record the prod of exec, blocks, mem_block, & mem_addr
    let (perm_mem_poly_list, proof_eval_perm_mem_prod_list) = {
      let mut perm_mem_poly_list = Vec::new();
      let mut proof_eval_perm_mem_prod_list = Vec::new();
      for p in 0..perm_mem_num_instances {
        let r_len = (perm_mem_num_proofs[p] * perm_mem_num_inputs[p]).log_2();
        // Prod is the 2nd entry
        let perm_mem_poly = perm_mem_w3_prover.poly_w[p][2];
        let (proof_eval_perm_mem_prod, _comm_perm_prod) = PolyEvalProof::prove(
          &perm_mem_w3_prover.poly_w[p],
          None,
          &[vec![ZERO; r_len - 2], vec![ONE], vec![ZERO]].concat(),
          &perm_mem_poly,
          None,
          &vars_gens.gens_pc,
          transcript,
          &mut random_tape,
        );
        perm_mem_poly_list.push(perm_mem_poly);
        proof_eval_perm_mem_prod_list.push(proof_eval_perm_mem_prod);
      }
      (perm_mem_poly_list, proof_eval_perm_mem_prod_list)
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
      func_input_width,
      input_offset,
      output_offset,
      input,
      output,
      output_exec_num,
      vars_gens,
      transcript,
      &mut random_tape
    );
    timer_proof.stop();

    timer_prove.stop();
    SNARK {
      block_comm_vars_list,
      block_comm_inputs_list,
      exec_comm_inputs,
      addr_comm_mems,

      perm_exec_comm_w2_list,
      perm_block_comm_w2_list,
      perm_comm_w3_list,

      mem_block_comm_w3_list,
      mem_addr_comm_w2,
      mem_addr_comm_w3,

      block_r1cs_sat_proof,
      block_inst_evals_bound_rp,
      block_inst_evals_list,
      block_r1cs_eval_proof,

      consis_check_r1cs_sat_proof,
      consis_check_inst_evals,
      consis_check_r1cs_eval_proof,

      perm_root_r1cs_sat_proof,
      perm_root_inst_evals,
      perm_root_r1cs_eval_proof,

      mem_block_proofs,
      mem_addr_proofs,

      perm_mem_poly_r1cs_sat_proof,
      perm_mem_poly_inst_evals,
      perm_mem_poly_r1cs_eval_proof,
      perm_mem_poly_list,
      proof_eval_perm_mem_prod_list,

      io_proof
    }
  }

  /// A method to verify the SNARK proof of the satisfiability of an R1CS instance
  pub fn verify(
    &self,
    input_block_num: usize,
    output_block_num: usize,
    func_input_width: usize,
    input_offset: usize,
    output_offset: usize,
    input: &Vec<[u8; 32]>,
    output: &[u8; 32],
    output_exec_num: usize,

    num_vars: usize,
    num_ios: usize,
    addr_block_w3_size: usize,
    num_inputs_unpadded: usize,
    // How many variables (witnesses) are used by each block? Round to the next power of 2
    num_vars_per_block: &Vec<usize>,
    total_num_proofs_bound: usize,
    block_num_instances_bound: usize,

    block_max_num_proofs: usize,
    block_num_proofs: &Vec<usize>,
    block_num_cons: usize,
    block_comm: &Vec<ComputationCommitment>,
    block_gens: &SNARKGens,

    consis_num_proofs: usize,
    consis_check_num_cons_base: usize,
    consis_check_comm: &ComputationCommitment,
    consis_check_gens: &SNARKGens,

    perm_root_num_cons: usize,
    perm_root_comm: &ComputationCommitment,
    perm_root_gens: &SNARKGens,

    perm_poly_num_cons_base: usize,
    perm_poly_comm: &ComputationCommitment,
    perm_poly_gens: &SNARKGens,

    max_block_num_mem_accesses: usize,
    mem_extract_num_cons: usize,
    mem_extract_comm: &ComputationCommitment,
    mem_extract_gens: &SNARKGens,

    total_num_mem_accesses_bound: usize,
    total_num_mem_accesses: usize,
    mem_cohere_num_cons_base: usize,
    mem_cohere_comm: &ComputationCommitment,
    mem_cohere_gens: &SNARKGens,

    mem_block_comm_mask_list: &Vec<PolyCommitment>,

    vars_gens: &R1CSGens,
    transcript: &mut Transcript,
  ) -> Result<(), ProofVerifyError> {
    let timer_verify = Timer::new("SNARK::verify");
    transcript.append_protocol_name(SNARK::protocol_name());

    // --
    // ASSERTIONS
    // --
    assert!(0 < consis_num_proofs);
    for p in 0..block_num_instances_bound {
      assert!(block_num_proofs[p] <= block_max_num_proofs);
    }
    assert!(consis_num_proofs <= total_num_proofs_bound);
    assert!(total_num_mem_accesses <= total_num_mem_accesses_bound);

    // --
    // COMMITMENTS
    // --

    let input_block_num = Scalar::from(input_block_num as u64);
    let output_block_num = Scalar::from(output_block_num as u64);
    let input: Vec<Scalar> = input.iter().map(|i| Scalar::from_bytes(i).unwrap()).collect();
    let output: Scalar = Scalar::from_bytes(output).unwrap();
    {
      let timer_commit = Timer::new("inst_commit");
      // Commit public parameters
      Scalar::from(func_input_width as u64).append_to_transcript(b"func_input_width", transcript);
      Scalar::from(input_offset as u64).append_to_transcript(b"input_offset", transcript);
      Scalar::from(output_offset as u64).append_to_transcript(b"output_offset", transcript);
      Scalar::from(output_exec_num as u64).append_to_transcript(b"output_exec_num", transcript);
      Scalar::from(num_ios as u64).append_to_transcript(b"num_ios", transcript);
      for n in num_vars_per_block {
        Scalar::from(*n as u64).append_to_transcript(b"num_vars_per_block", transcript);
      }
      Scalar::from(addr_block_w3_size as u64).append_to_transcript(b"addr_block_w3_size", transcript);
      Scalar::from(num_inputs_unpadded as u64).append_to_transcript(b"num_inputs_unpadded", transcript);
      Scalar::from(total_num_proofs_bound as u64).append_to_transcript(b"total_num_proofs_bound", transcript);
      Scalar::from(block_num_instances_bound as u64).append_to_transcript(b"block_num_instances_bound", transcript);
      Scalar::from(block_max_num_proofs as u64).append_to_transcript(b"block_max_num_proofs", transcript);
      Scalar::from(max_block_num_mem_accesses as u64).append_to_transcript(b"max_block_num_mem_accesses", transcript);
      Scalar::from(total_num_mem_accesses_bound as u64).append_to_transcript(b"total_num_mem_accesses_bound", transcript);
      Scalar::from(total_num_mem_accesses as u64).append_to_transcript(b"total_num_mem_accesses", transcript);
      
      // commit mem_block_mask
      for c in mem_block_comm_mask_list {
        c.append_to_transcript(b"mem_block_masks", transcript);
      }
      // commit num_proofs
      Scalar::from(block_max_num_proofs as u64).append_to_transcript(b"block_max_num_proofs", transcript);
      for n in block_num_proofs {
        Scalar::from(*n as u64).append_to_transcript(b"block_num_proofs", transcript);
      }

      // append a commitment to the computation to the transcript
      for c in block_comm {
        c.comm.append_to_transcript(b"block_comm", transcript);
      }
      consis_check_comm.comm.append_to_transcript(b"consis_comm", transcript);
      perm_root_comm.comm.append_to_transcript(b"block_comm", transcript);
      perm_poly_comm.comm.append_to_transcript(b"block_comm", transcript);
      mem_extract_comm.comm.append_to_transcript(b"block_comm", transcript);
      mem_cohere_comm.comm.append_to_transcript(b"consis_comm", transcript);

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
    let block_num_instances = block_num_proofs.iter().fold(0, |i, j| if *j > 0 { i + 1 } else { i });
    // Sort the following based on block_num_proofs:
    // - block_num_proofs
    // - block_inst, block_comm, block_decomm
    // - block_num_mem_accesses
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
    let index: Vec<usize> = inst_sorter.iter().map(|i| i.index).collect();
    let num_vars_per_block: Vec<usize> = (0..block_num_instances).map(|i| num_vars_per_block[index[i]]).collect();
    let block_comm: &Vec<&ComputationCommitment> = &(0..block_num_instances).map(|i| &block_comm[index[i]]).collect();
    let mem_block_comm_mask_list: Vec<PolyCommitment> = (0..block_num_instances).map(|i| mem_block_comm_mask_list[index[i]].clone()).collect();

    // --
    // PADDING
    // --
    // Pad entries of block_num_proofs to a power of 2
    let block_max_num_proofs = block_max_num_proofs.next_power_of_two();
    for i in 0..block_num_instances {
      block_num_proofs[i] = block_num_proofs[i].next_power_of_two();
    }
    // Pad exec_inputs with dummys so the length is a power of 2
    let consis_num_proofs = consis_num_proofs.next_power_of_two();
    // Pad addr_mems with dummys so the length is a power of 2
    let total_num_mem_accesses = if total_num_mem_accesses == 0 { 0 } else { total_num_mem_accesses.next_power_of_two() };
    
    // Compute perm_size_bound & perm_num_proofs
    let perm_size_bound = max(total_num_proofs_bound, total_num_mem_accesses_bound) * 4;
    let mut perm_num_proofs = [vec![consis_num_proofs], block_num_proofs.to_vec()].concat();
    // Pad num_proofs with 1 until the next power of 2
    block_num_proofs.extend(vec![1; block_num_instances.next_power_of_two() - block_num_instances]);
    perm_num_proofs.extend(vec![1; (block_num_instances + 1).next_power_of_two() - (block_num_instances - 1)]);
    let block_num_proofs = &block_num_proofs;
    timer_sort.stop();

    // --
    // SAMPLE CHALLENGES, COMMIT WITNESSES, & CONSTRUCT WITNESS_SEC_INFO
    // --
    let timer_commit = Timer::new("witness_commit");
    let (
      block_vars_verifier,
      block_inputs_verifier,
      exec_inputs_verifier,
    ) = {
      // add the commitment to the verifier's transcript
      for p in 0..block_num_instances {
        self.block_comm_vars_list[p].append_to_transcript(b"poly_commitment", transcript);
        self.block_comm_inputs_list[p].append_to_transcript(b"poly_commitment", transcript);
      }
      self.exec_comm_inputs[0].append_to_transcript(b"poly_commitment", transcript);
      (
        VerifierWitnessSecInfo::new(false, num_vars_per_block, &block_num_proofs, &self.block_comm_vars_list),
        VerifierWitnessSecInfo::new(false, vec![num_ios; block_num_instances], &block_num_proofs, &self.block_comm_inputs_list),
        VerifierWitnessSecInfo::new(false, vec![num_ios], &vec![consis_num_proofs], &self.exec_comm_inputs),
      )
    };

    let addr_mems_verifier = {
      if total_num_mem_accesses > 0 {
        self.addr_comm_mems[0].append_to_transcript(b"poly_commitment", transcript);
        VerifierWitnessSecInfo::new(false, vec![4], &vec![total_num_mem_accesses], &self.addr_comm_mems)
      } else {
        VerifierWitnessSecInfo::dummy()
      }
    };

    let mem_block_mask_verifier = VerifierWitnessSecInfo::new(
      true,
      vec![max_block_num_mem_accesses.next_power_of_two(); block_num_instances],
      &vec![1; block_num_instances],
      &mem_block_comm_mask_list
    );

    let comb_tau = transcript.challenge_scalar(b"challenge_tau");
    let comb_r = transcript.challenge_scalar(b"challenge_r");

    let (
      perm_w0_verifier,
      perm_exec_w2_verifier,
      perm_block_w2_verifier,
      perm_w3_verifier,
    ) = {
      // Let the verifier generate perm_w0 itself
      let mut perm_w0 = vec![comb_tau];
      let mut r_tmp = comb_r;
      for _ in 1..2 * num_inputs_unpadded {
        perm_w0.push(r_tmp);
        r_tmp *= comb_r;
      }
      perm_w0.extend(vec![Scalar::zero(); num_ios - 2 * num_inputs_unpadded]);
      // create a multilinear polynomial using the supplied assignment for variables
      let perm_poly_w0 = DensePolynomial::new(perm_w0.clone());
      // produce a commitment to the satisfying assignment
      let (perm_comm_w0, _blinds_vars) = perm_poly_w0.commit(&vars_gens.gens_pc, None);
      // add the commitment to the prover's transcript
      perm_comm_w0.append_to_transcript(b"poly_commitment", transcript);

      self.perm_exec_comm_w2_list[0].append_to_transcript(b"poly_commitment", transcript);
      for p in 0..block_num_instances {
        self.perm_block_comm_w2_list[p].append_to_transcript(b"poly_commitment", transcript);
      }
      for p in 0..block_num_instances + 1 {
        self.perm_comm_w3_list[p].append_to_transcript(b"poly_commitment", transcript);
      }
      (
        VerifierWitnessSecInfo::new(true, vec![num_ios], &vec![1], &vec![perm_comm_w0]),
        VerifierWitnessSecInfo::new(false, vec![num_ios], &vec![consis_num_proofs], &self.perm_exec_comm_w2_list),
        VerifierWitnessSecInfo::new(false, vec![num_ios; block_num_instances], &block_num_proofs.clone(), &self.perm_block_comm_w2_list),
        VerifierWitnessSecInfo::new(false, vec![4; block_num_instances + 1], &perm_num_proofs.clone(), &self.perm_comm_w3_list),
      )
    };

    let mem_block_w3_verifier = {
      if total_num_mem_accesses_bound > 0 {
        for p in 0..block_num_instances {
          self.mem_block_comm_w3_list[p].append_to_transcript(b"poly_commitment", transcript);
        }
        VerifierWitnessSecInfo::new(false, vec![addr_block_w3_size; block_num_instances], &block_num_proofs, &self.mem_block_comm_w3_list)
      } else {
        VerifierWitnessSecInfo::dummy()
      }
    };

    let (
      mem_addr_w2_verifier,
      mem_addr_w3_verifier
    ) = {
      if total_num_mem_accesses > 0 {
        self.mem_addr_comm_w2[0].append_to_transcript(b"poly_commitment", transcript);
        self.mem_addr_comm_w3[0].append_to_transcript(b"poly_commitment", transcript);
        (
          VerifierWitnessSecInfo::new(false, vec![4], &vec![total_num_mem_accesses], &self.mem_addr_comm_w2),
          VerifierWitnessSecInfo::new(false, vec![4], &vec![total_num_mem_accesses], &self.mem_addr_comm_w3),
        )
      } else {
        (
          VerifierWitnessSecInfo::dummy(),
          VerifierWitnessSecInfo::dummy(),
        )
      }
    };
    timer_commit.stop();

    // --
    // BLOCK CORRECTNESS
    // --
    {
      let timer_sat_proof = Timer::new("Block Correctness Sat");
      let block_challenges = self.block_r1cs_sat_proof.verify(
        block_num_instances,
        block_max_num_proofs,
        block_num_proofs,
        num_vars,
        vec![&block_inputs_verifier, &block_vars_verifier],
        block_num_cons,
        &vars_gens,
        &self.block_inst_evals_bound_rp,
        transcript,
      )?;
      timer_sat_proof.stop();

      let timer_eval_proof = Timer::new("Block Correctness Eval");
      // Verify Evaluation on BLOCK
      let mut A_evals = Vec::new();
      let mut B_evals = Vec::new();
      let mut C_evals = Vec::new();
      let [rp, _, rx, ry] = block_challenges;
      for i in 0..block_num_instances {
        let (Ar, Br, Cr) = &self.block_inst_evals_list[i];
        Ar.append_to_transcript(b"Ar_claim", transcript);
        Br.append_to_transcript(b"Br_claim", transcript);
        Cr.append_to_transcript(b"Cr_claim", transcript);
        self.block_r1cs_eval_proof[i].verify(
          &block_comm[i].comm,
          &rx,
          &ry,
          &self.block_inst_evals_list[i],
          &block_gens.gens_r1cs_eval,
          transcript,
        )?;
        A_evals.push(Ar.clone());
        B_evals.push(Br.clone());
        C_evals.push(Cr.clone());
      }
      // Verify that block_inst_evals_bound_rp is block_inst_evals_list bind rp
      assert_eq!(DensePolynomial::new(A_evals).evaluate(&rp), self.block_inst_evals_bound_rp.0);
      assert_eq!(DensePolynomial::new(B_evals).evaluate(&rp), self.block_inst_evals_bound_rp.1);
      assert_eq!(DensePolynomial::new(C_evals).evaluate(&rp), self.block_inst_evals_bound_rp.2);
      timer_eval_proof.stop();
    }

    // --
    // CONSIS_CHECK
    // --
    {
      let timer_sat_proof = Timer::new("Consis Check Sat");
      let consis_check_challenges = self.consis_check_r1cs_sat_proof.verify_single(
        1,
        consis_check_num_cons_base,
        2,
        total_num_proofs_bound,
        consis_num_proofs,
        &vec![consis_num_proofs],
        &vars_gens,
        &self.consis_check_inst_evals,
        &vec![num_ios],
        &self.perm_exec_comm_w2_list,
        transcript,
      )?;
      timer_sat_proof.stop();

      let timer_eval_proof = Timer::new("Consis Check Eval");
      // Verify Evaluation on CONSIS_CHECK
      let (Ar, Br, Cr) = &self.consis_check_inst_evals;
      Ar.append_to_transcript(b"Ar_claim", transcript);
      Br.append_to_transcript(b"Br_claim", transcript);
      Cr.append_to_transcript(b"Cr_claim", transcript);
      let [_, rx, ry] = &consis_check_challenges;
      self.consis_check_r1cs_eval_proof.verify(
        &consis_check_comm.comm,
        rx,
        ry,
        &self.consis_check_inst_evals,
        &consis_check_gens.gens_r1cs_eval,
        transcript,
      )?;
      timer_eval_proof.stop();
    };

    // --
    // MEM_BLOCK and MEM_ADDR
    // --
    if total_num_mem_accesses_bound > 0 {
      let mem_block_proofs = self.mem_block_proofs.as_ref().unwrap();

      // --
      // MEM_EXTRACT
      // --
      {
        let timer_sat_proof = Timer::new("Mem Extract Sat");
        let mem_extract_challenges = mem_block_proofs.mem_extract_r1cs_sat_proof.verify(
          block_num_instances,
          block_max_num_proofs,
          block_num_proofs,
          addr_block_w3_size,
          vec![&perm_w0_verifier, &mem_block_mask_verifier, &block_vars_verifier, &mem_block_w3_verifier],
          mem_extract_num_cons,
          &vars_gens,
          &mem_block_proofs.mem_extract_inst_evals,
          transcript,
        )?;
        timer_sat_proof.stop();

        let timer_eval_proof = Timer::new("Mem Extract Eval");
        // Verify Evaluation on PERM_BLOCK_ROOT
        let (Ar, Br, Cr) = &mem_block_proofs.mem_extract_inst_evals;
        Ar.append_to_transcript(b"Ar_claim", transcript);
        Br.append_to_transcript(b"Br_claim", transcript);
        Cr.append_to_transcript(b"Cr_claim", transcript);
        let [_, _, rx, ry] = mem_extract_challenges;
        mem_block_proofs.mem_extract_r1cs_eval_proof.verify(
          &mem_extract_comm.comm,
          &rx,
          &ry,
          &mem_block_proofs.mem_extract_inst_evals,
          &mem_extract_gens.gens_r1cs_eval,
          transcript,
        )?;
        timer_eval_proof.stop();
      }

      // --
      // MEM_ADDR
      // --
      if total_num_mem_accesses > 0 {
        let mem_addr_proofs = self.mem_addr_proofs.as_ref().unwrap();

        // --
        // MEM_COHERE
        // --
        {
          let timer_sat_proof = Timer::new("Mem Cohere Sat");
          let mem_cohere_challenges = mem_addr_proofs.mem_cohere_r1cs_sat_proof.verify_single(
            1,
            mem_cohere_num_cons_base,
            4,
            total_num_mem_accesses_bound,
            total_num_mem_accesses,
            &vec![total_num_mem_accesses],
            &vars_gens,
            &mem_addr_proofs.mem_cohere_inst_evals,
            &vec![4],
            &self.addr_comm_mems,
            transcript,
          )?;
          timer_sat_proof.stop();

          let timer_eval_proof = Timer::new("Mem Cohere Eval");
          // Verify Evaluation on MEM_COHERE
          let (Ar, Br, Cr) = &mem_addr_proofs.mem_cohere_inst_evals;
          Ar.append_to_transcript(b"Ar_claim", transcript);
          Br.append_to_transcript(b"Br_claim", transcript);
          Cr.append_to_transcript(b"Cr_claim", transcript);
          let [_, rx, ry] = &mem_cohere_challenges;
          mem_addr_proofs.mem_cohere_r1cs_eval_proof.verify(
            &mem_cohere_comm.comm,
            rx,
            ry,
            &mem_addr_proofs.mem_cohere_inst_evals,
            &mem_cohere_gens.gens_r1cs_eval,
            transcript,
          )?;
          timer_eval_proof.stop();
        };
      }
    }

    // --
    // PERM_BLOCK_ROOT, PERM_EXEC_ROOT, MEM_ADDR_ROOT
    // --
    let perm_size = max(consis_num_proofs, total_num_mem_accesses);
    {
      let timer_sat_proof = Timer::new("Perm Root Sat");
      let (perm_root_w1_verifier, _) = VerifierWitnessSecInfo::merge(vec![&exec_inputs_verifier, &block_inputs_verifier, &addr_mems_verifier]);
      let (perm_root_w2_verifier, _) = VerifierWitnessSecInfo::merge(vec![&perm_exec_w2_verifier, &perm_block_w2_verifier, &mem_addr_w2_verifier]);
      let (perm_root_w3_verifier, _) = VerifierWitnessSecInfo::merge(vec![&perm_w3_verifier, &mem_addr_w3_verifier]);
      let perm_root_num_instances = perm_root_w1_verifier.num_proofs.len();
      let mut perm_root_num_proofs: Vec<usize> = perm_root_w1_verifier.num_proofs.clone();
      perm_root_num_proofs.extend(vec![1; perm_root_num_instances.next_power_of_two() - perm_root_num_instances]);
      let perm_block_root_challenges = self.perm_root_r1cs_sat_proof.verify(
        perm_root_num_instances,
        perm_size,
        &perm_root_num_proofs,
        num_ios,
        vec![&perm_w0_verifier, &perm_root_w1_verifier, &perm_root_w2_verifier, &perm_root_w3_verifier],
        perm_root_num_cons,
        &vars_gens,
        &self.perm_root_inst_evals,
        transcript,
      )?;
      timer_sat_proof.stop();

      let timer_eval_proof = Timer::new("Perm Root Eval");
      // Verify Evaluation on PERM_BLOCK_ROOT
      let (Ar, Br, Cr) = &self.perm_root_inst_evals;
      Ar.append_to_transcript(b"Ar_claim", transcript);
      Br.append_to_transcript(b"Br_claim", transcript);
      Cr.append_to_transcript(b"Cr_claim", transcript);
      let [_, _, rx, ry] = perm_block_root_challenges;
      self.perm_root_r1cs_eval_proof.verify(
        &perm_root_comm.comm,
        &rx,
        &ry,
        &self.perm_root_inst_evals,
        &perm_root_gens.gens_r1cs_eval,
        transcript,
      )?;
      timer_eval_proof.stop();
    }


    // --
    // PERM_BLOCK_POLY, PERM_EXEC_POLY, MEM_BLOCK_POLY, MEM_ADDR_POLY
    // --
    {
      let timer_sat_proof = Timer::new("Perm Mem Poly Sat");

      let (perm_mem_w3_verifier, inst_map) = VerifierWitnessSecInfo::merge(
        vec![&perm_w3_verifier, &mem_block_w3_verifier, &mem_addr_w3_verifier]
      );
      let perm_mem_num_instances = perm_mem_w3_verifier.num_proofs.len();
      let mut perm_mem_num_proofs: Vec<usize> = perm_mem_w3_verifier.num_proofs;
      perm_mem_num_proofs.extend(vec![1; perm_mem_num_instances.next_power_of_two() - perm_mem_num_instances]);
      // mem_block has size addr_block_w3_size, everything else takes size 4
      let perm_mem_num_inputs = inst_map.iter().map(|i| if *i == 1 { addr_block_w3_size } else { 4 }).collect();

      let perm_mem_poly_challenges = self.perm_mem_poly_r1cs_sat_proof.verify_single(
        perm_mem_num_instances,
        perm_poly_num_cons_base,
        4,
        perm_size_bound,
        perm_size,
        &perm_mem_num_proofs,
        &vars_gens,
        &self.perm_mem_poly_inst_evals,
        &perm_mem_num_inputs,
        &perm_mem_w3_verifier.comm_w,
        transcript,
      )?;
      timer_sat_proof.stop();

      let timer_eval_proof = Timer::new("Perm Mem Poly Eval");
      // Verify Evaluation on PERM_BLOCK_POLY
      let (Ar, Br, Cr) = &self.perm_mem_poly_inst_evals;
      Ar.append_to_transcript(b"Ar_claim", transcript);
      Br.append_to_transcript(b"Br_claim", transcript);
      Cr.append_to_transcript(b"Cr_claim", transcript);
      let [_, rx, ry] = &perm_mem_poly_challenges;

      self.perm_mem_poly_r1cs_eval_proof.verify(
        &perm_poly_comm.comm,
        rx,
        ry,
        &self.perm_mem_poly_inst_evals,
        &perm_poly_gens.gens_r1cs_eval,
        transcript,
      )?;
      timer_eval_proof.stop();

      // Compute poly for PERM_EXEC, PERM_BLOCK, MEM_BLOCK, MEM_ADDR base on INST_MAP
      let mut perm_block_poly_bound_tau = ONE;
      let mut perm_exec_poly_bound_tau = ONE;
      let mut mem_block_poly_bound_tau = ONE;
      let mut mem_addr_poly_bound_tau = ONE;
      // INST_MAP: 0 -> perm_exec + perm_block, 1 -> mem_block, 2 -> mem_addr
      let mut next_zero_is_perm_exec = true;

      for p in 0..perm_mem_num_instances {
        let r_len = (perm_mem_num_proofs[p] * perm_mem_num_inputs[p]).log_2();
        self.proof_eval_perm_mem_prod_list[p].verify_plain(
          &vars_gens.gens_pc,
          transcript,
          &[vec![ZERO; r_len - 2], vec![ONE], vec![ZERO]].concat(),
          &self.perm_mem_poly_list[p],
          &perm_mem_w3_verifier.comm_w[p],
        )?;
        match inst_map[p] {
          0 => {
            if next_zero_is_perm_exec {
              next_zero_is_perm_exec = false;
              perm_exec_poly_bound_tau *= self.perm_mem_poly_list[p]; 
            } else {
              perm_block_poly_bound_tau *= self.perm_mem_poly_list[p]; 
            }
          }
          1 => {
            mem_block_poly_bound_tau *= self.perm_mem_poly_list[p];
          }
          2 => {
            mem_addr_poly_bound_tau *= self.perm_mem_poly_list[p];
          }
          _ => {}
        }
      }

      // Correctness of Permutation
      assert_eq!(perm_block_poly_bound_tau, perm_exec_poly_bound_tau);
      // Correctness of Memory
      assert_eq!(mem_block_poly_bound_tau, mem_addr_poly_bound_tau);
    };

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
      func_input_width,
      input_offset,
      output_offset,
      input,
      output,
      output_exec_num,
      vars_gens,
      transcript
    )?;
    timer_proof.stop();
    
    timer_verify.stop();
    Ok(())
  }

  /*
  // --
  // PARALLEL VERSION
  // --

  /// A method to produce a SNARK proof of the satisfiability of an R1CS instance
  pub fn prove_parallel(
    input_block_num: usize,
    output_block_num: usize,
    func_input_width: usize,
    input_offset: usize,
    output_offset: usize,
    input: &Vec<[u8; 32]>,
    output: &[u8; 32],
    output_exec_num: usize,

    num_vars: usize,
    num_ios: usize,
    addr_block_w3_size: usize,
    num_inputs_unpadded: usize,
    num_vars_per_block: &Vec<usize>,
    total_num_proofs_bound: usize,

    block_num_instances_bound: usize,
    block_max_num_proofs: usize,
    block_num_proofs: &Vec<usize>,
    block_inst: &mut Instance,
    block_comm: &Vec<ComputationCommitment>,
    block_decomm: &Vec<ComputationDecommitment>,
    block_gens: &SNARKGens,

    consis_num_proofs: usize,
    consis_comb_inst: &Instance,
    consis_comb_comm: &ComputationCommitment,
    consis_comb_decomm: &ComputationDecommitment,
    consis_comb_gens: &SNARKGens,

    consis_check_num_cons_base: usize,
    consis_check_inst: &Instance,
    consis_check_comm: &ComputationCommitment,
    consis_check_decomm: &ComputationDecommitment,
    consis_check_gens: &SNARKGens,

    perm_prelim_inst: &Instance,
    perm_prelim_comm: &ComputationCommitment,
    perm_prelim_decomm: &ComputationDecommitment,
    perm_prelim_gens: &SNARKGens,

    perm_root_inst: &Instance,
    perm_root_comm: &ComputationCommitment,
    perm_root_decomm: &ComputationDecommitment,
    perm_root_gens: &SNARKGens,

    perm_poly_num_cons_base: usize,
    perm_poly_inst: &Instance,
    perm_poly_comm: &ComputationCommitment,
    perm_poly_decomm: &ComputationDecommitment,
    perm_poly_gens: &SNARKGens,

    max_block_num_mem_accesses: usize,
    mem_extract_inst: &Instance,
    mem_extract_comm: &ComputationCommitment,
    mem_extract_decomm: &ComputationDecommitment,
    mem_extract_gens: &SNARKGens,

    total_num_mem_accesses_bound: usize,
    total_num_mem_accesses: usize,
    mem_cohere_num_cons_base: usize,
    mem_cohere_inst: &Instance,
    mem_cohere_comm: &ComputationCommitment,
    mem_cohere_decomm: &ComputationDecommitment,
    mem_cohere_gens: &SNARKGens,

    mem_addr_comb_inst: &Instance,
    mem_addr_comb_comm: &ComputationCommitment,
    mem_addr_comb_decomm: &ComputationDecommitment,
    mem_addr_comb_gens: &SNARKGens,

    block_vars_mat: Vec<Vec<VarsAssignment>>,
    block_inputs_mat: Vec<Vec<InputsAssignment>>,
    exec_inputs_list: Vec<InputsAssignment>,
    addr_mems_list: Vec<MemsAssignment>,

    mem_block_mask: &Vec<Vec<Vec<Scalar>>>,
    mem_block_poly_mask_list: &Vec<DensePolynomial>,
    mem_block_comm_mask_list: &Vec<PolyCommitment>,

    vars_gens: &R1CSGens,

    transcript: &mut Transcript,
  ) -> Self {
    let timer_prove = Timer::new("SNARK::prove");

    transcript.append_protocol_name(SNARK::protocol_name());

    // --
    // ASSERTIONS
    // --
    assert!(0 < consis_num_proofs);
    for p in 0..block_num_instances_bound {
      assert!(block_num_proofs[p] <= block_max_num_proofs);
    }
    assert!(consis_num_proofs <= total_num_proofs_bound);
    assert!(total_num_mem_accesses <= total_num_mem_accesses_bound);
    assert_eq!(block_num_instances_bound, mem_block_mask.len());
    assert_eq!(block_num_instances_bound, mem_block_poly_mask_list.len());
    assert_eq!(block_num_instances_bound, mem_block_comm_mask_list.len());

    // --
    // PREPROCESSING
    // --
    // unwrap the assignments
    let mut block_vars_mat = block_vars_mat.into_iter().map(|a| a.into_iter().map(|v| v.assignment).collect_vec()).collect_vec();
    let mut block_inputs_mat = block_inputs_mat.into_iter().map(|a| a.into_iter().map(|v| v.assignment).collect_vec()).collect_vec();
    let mut exec_inputs_list = exec_inputs_list.into_iter().map(|v| v.assignment).collect_vec();
    let mut addr_mems_list = addr_mems_list.into_iter().map(|v| v.assignment).collect_vec();

    // --
    // INSTANCE COMMITMENTS
    // --
    let input_block_num = Scalar::from(input_block_num as u64);
    let output_block_num = Scalar::from(output_block_num as u64);
    let input: Vec<Scalar> = input.iter().map(|i| Scalar::from_bytes(i).unwrap()).collect();
    let output: Scalar = Scalar::from_bytes(output).unwrap();
    let timer_commit = Timer::new("inst_commit");
    // Commit public parameters
    Scalar::from(func_input_width as u64).append_to_transcript(b"func_input_width", transcript);
    Scalar::from(input_offset as u64).append_to_transcript(b"input_offset", transcript);
    Scalar::from(output_offset as u64).append_to_transcript(b"output_offset", transcript);
    Scalar::from(output_exec_num as u64).append_to_transcript(b"output_exec_num", transcript);
    Scalar::from(num_ios as u64).append_to_transcript(b"num_ios", transcript);
    for n in num_vars_per_block {
      Scalar::from(*n as u64).append_to_transcript(b"num_vars_per_block", transcript);
    }
    Scalar::from(addr_block_w3_size as u64).append_to_transcript(b"addr_block_w3_size", transcript);
    Scalar::from(num_inputs_unpadded as u64).append_to_transcript(b"num_inputs_unpadded", transcript);
    Scalar::from(total_num_proofs_bound as u64).append_to_transcript(b"total_num_proofs_bound", transcript);
    Scalar::from(block_num_instances_bound as u64).append_to_transcript(b"block_num_instances_bound", transcript);
    Scalar::from(block_max_num_proofs as u64).append_to_transcript(b"block_max_num_proofs", transcript);
    Scalar::from(max_block_num_mem_accesses as u64).append_to_transcript(b"max_block_num_mem_accesses", transcript);
    Scalar::from(total_num_mem_accesses_bound as u64).append_to_transcript(b"total_num_mem_accesses_bound", transcript);
    Scalar::from(total_num_mem_accesses as u64).append_to_transcript(b"total_num_mem_accesses", transcript);
    
    // commit mem_block_mask
    for c in mem_block_comm_mask_list {
      c.append_to_transcript(b"mem_block_masks", transcript);
    }
    // commit num_proofs
    Scalar::from(block_max_num_proofs as u64).append_to_transcript(b"block_max_num_proofs", transcript);
    for n in block_num_proofs {
      Scalar::from(*n as u64).append_to_transcript(b"block_num_proofs", transcript);
    }

    // append a commitment to the computation to the transcript
    for c in block_comm {
      c.comm.append_to_transcript(b"block_comm", transcript);
    }
    consis_comb_comm.comm.append_to_transcript(b"consis_comm", transcript);
    consis_check_comm.comm.append_to_transcript(b"consis_comm", transcript);
    perm_prelim_comm.comm.append_to_transcript(b"block_comm", transcript);
    perm_root_comm.comm.append_to_transcript(b"block_comm", transcript);
    perm_poly_comm.comm.append_to_transcript(b"block_comm", transcript);
    mem_extract_comm.comm.append_to_transcript(b"block_comm", transcript);
    mem_cohere_comm.comm.append_to_transcript(b"consis_comm", transcript);
    mem_addr_comb_comm.comm.append_to_transcript(b"block_comm", transcript);

    // Commit io
    input_block_num.append_to_transcript(b"input_block_num", transcript);
    output_block_num.append_to_transcript(b"output_block_num", transcript);
    input.append_to_transcript(b"input_list", transcript);
    output.append_to_transcript(b"output_list", transcript);

    timer_commit.stop();

    // --
    // BLOCK SORT
    // --
    let timer_sort = Timer::new("block_sort");
    // Block_num_instance is the number of non-zero entries in block_num_proofs
    let block_num_instances = block_num_proofs.iter().fold(0, |i, j| if *j > 0 { i + 1 } else { i });
    // Sort the following based on block_num_proofs:
    // - block_num_proofs
    // - block_inst, block_comm, block_decomm
    // - block_num_mem_accesses
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
    block_inst.sort(block_num_instances, &index);
    let block_decomm: &Vec<&ComputationDecommitment> = &(0..block_num_instances).map(|i| &block_decomm[index[i]]).collect();
    let mem_block_mask: Vec<Vec<Vec<Scalar>>> = (0..block_num_instances).map(|i| mem_block_mask[index[i]].clone()).collect();
    let mem_block_poly_mask_list: Vec<DensePolynomial> = (0..block_num_instances).map(|i| mem_block_poly_mask_list[index[i]].clone()).collect();

    // --
    // PADDING
    // --
    let zero = ZERO;
    let dummy_inputs = vec![zero; num_ios];
    // For every block that num_proofs is not a power of 2, pad vars_mat and inputs_mat until the length is a power of 2
    let block_max_num_proofs = block_max_num_proofs.next_power_of_two();
    for i in 0..block_num_instances {
      let dummy_vars = vec![zero; block_vars_mat[i][0].len()];
      let gap = block_num_proofs[i].next_power_of_two() - block_num_proofs[i];
      block_vars_mat[i].extend(vec![dummy_vars.clone(); gap]);
      block_inputs_mat[i].extend(vec![dummy_inputs.clone(); gap]);
      block_num_proofs[i] = block_num_proofs[i].next_power_of_two();
    }
    // Pad num_proofs with 1 until the next power of 2
    block_num_proofs.extend(vec![1; block_num_instances.next_power_of_two() - block_num_instances]);
    let block_num_proofs = &block_num_proofs;

    // Pad exec_inputs with dummys so the length is a power of 2
    exec_inputs_list.extend(vec![dummy_inputs; consis_num_proofs.next_power_of_two() - consis_num_proofs]);
    let consis_num_proofs = consis_num_proofs.next_power_of_two();

    // Pad addr_mems with dummys so the length is a power of 2
    if total_num_mem_accesses > 0 {
      let dummy_addr = vec![zero; 4];
      addr_mems_list.extend(vec![dummy_addr; total_num_mem_accesses.next_power_of_two() - total_num_mem_accesses]);
    }
    let total_num_mem_accesses = if total_num_mem_accesses == 0 { 0 } else { total_num_mem_accesses.next_power_of_two() };
    timer_sort.stop();

    // --
    // WITNESS COMMITMENTS
    // --
    let timer_commit = Timer::new("input_commit");
    let (
      block_poly_vars_list,
      block_comm_vars_list,
      block_poly_inputs_list,
      block_comm_inputs_list,
      exec_poly_inputs,
      exec_comm_inputs
    ) = {

      // commit the witnesses and inputs separately instance-by-instance
      let mut block_poly_vars_list = Vec::new();
      let mut block_comm_vars_list = Vec::new();
      let mut block_poly_inputs_list = Vec::new();
      let mut block_comm_inputs_list = Vec::new();

      for p in 0..block_num_instances {
        let (block_poly_vars, block_comm_vars) = {
          // Flatten the witnesses into a Q_i * X list
          let vars_list_p = block_vars_mat[p].iter().fold(Vec::new(), |a, b| [a, b.to_vec()].concat());
          // create a multilinear polynomial using the supplied assignment for variables
          let block_poly_vars = DensePolynomial::new(vars_list_p);

          // produce a commitment to the satisfying assignment
          let (block_comm_vars, _blinds_vars) = block_poly_vars.commit(&vars_gens.gens_pc, None);

          // add the commitment to the prover's transcript
          block_comm_vars.append_to_transcript(b"poly_commitment", transcript);
          (block_poly_vars, block_comm_vars)
        };
        
        let (block_poly_inputs, block_comm_inputs) = {
          // Flatten the inputs into a Q_i * X list
          let inputs_list_p = block_inputs_mat[p].iter().fold(Vec::new(), |a, b| [a, b.to_vec()].concat());
          // create a multilinear polynomial using the supplied assignment for variables
          let block_poly_inputs = DensePolynomial::new(inputs_list_p);

          // produce a commitment to the satisfying assignment
          let (block_comm_inputs, _blinds_inputs) = block_poly_inputs.commit(&vars_gens.gens_pc, None);

          // add the commitment to the prover's transcript
          block_comm_inputs.append_to_transcript(b"poly_commitment", transcript);
          (block_poly_inputs, block_comm_inputs)
        };
        block_poly_vars_list.push(block_poly_vars);
        block_comm_vars_list.push(block_comm_vars);
        block_poly_inputs_list.push(block_poly_inputs);
        block_comm_inputs_list.push(block_comm_inputs);
      }

      let (exec_poly_inputs, exec_comm_inputs) = {
        let exec_inputs = exec_inputs_list.iter().fold(Vec::new(), |a, b| [a, b.to_vec()].concat());
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
        block_poly_inputs_list,
        block_comm_inputs_list,
        vec![exec_poly_inputs],
        vec![exec_comm_inputs]
      )
    };
    let (
      addr_poly_mems,
      addr_comm_mems
    ) = {
      if total_num_mem_accesses > 0 {
        let (addr_poly_mems, addr_comm_mems) = {
          let addr_mems = addr_mems_list.iter().fold(Vec::new(), |a, b| [a, b.to_vec()].concat());
          // create a multilinear polynomial using the supplied assignment for variables
          let addr_poly_mems = DensePolynomial::new(addr_mems);

          // produce a commitment to the satisfying assignment
          let (addr_comm_mems, _blinds_inputs) = addr_poly_mems.commit(&vars_gens.gens_pc, None);

          // add the commitment to the prover's transcript
          addr_comm_mems.append_to_transcript(b"poly_commitment", transcript);
          (addr_poly_mems, addr_comm_mems)
        };
        (
          vec![addr_poly_mems], 
          vec![addr_comm_mems],
        )
      } else {
        (
          Vec::new(),
          Vec::new()
        )
      }
    };
    timer_commit.stop();

    // --
    // CHALLENGES AND WITNESSES FOR PERMUTATION
    // --

    // Non-memory
    let timer_gen = Timer::new("witness_gen");
    let (
      comb_tau,
      comb_r,
      perm_w0_prover,
      perm_comm_w0,
      perm_block_w2_prover,
      perm_block_comm_w2_list,
      perm_block_w3_prover,
      perm_block_comm_w3_list,
      perm_exec_w2_prover,
      perm_exec_comm_w2,
      perm_exec_w3_prover,
      perm_exec_comm_w3,
      consis_w2_prover,
      consis_comm_w2,
      consis_w3_prover,
      consis_comm_w3,
    ) = {
      let comb_tau = transcript.challenge_scalar(b"challenge_tau");
      let comb_r = transcript.challenge_scalar(b"challenge_r");
      
      // w0 is (tau, r, r^2, ...) for the first 2 * num_inputs_unpadded entries
      // set the first entry to 1 for multiplication and later revert it to tau
      let mut perm_w0 = Vec::new();
      perm_w0.push(ONE);
      let mut r_tmp = comb_r;
      for _ in 1..2 * num_inputs_unpadded {
        perm_w0.push(r_tmp);
        r_tmp *= comb_r;
      }
      perm_w0.extend(vec![zero; num_ios - 2 * num_inputs_unpadded]);
      
      // FOR PERM
      // w2 is block_inputs * <r>
      let perm_block_w2: Vec<Vec<Vec<Scalar>>> = block_inputs_mat.iter().map(
        |i| i.iter().map(|input|
          [
            (0..2 * num_inputs_unpadded).map(|j| perm_w0[j] * input[j]).collect(),
            vec![zero; num_ios - 2 * num_inputs_unpadded]
          ].concat()
        ).collect()
      ).collect();
      let perm_exec_w2: Vec<Vec<Scalar>> = exec_inputs_list.iter().map(|input|
        [
          (0..2 * num_inputs_unpadded).map(|j| perm_w0[j] * input[j]).collect(),
          vec![zero; num_ios - 2 * num_inputs_unpadded]
        ].concat()
      ).collect();
      perm_w0[0] = comb_tau;
      
      // w3 is [v, x, pi, D]
      let mut perm_block_w3: Vec<Vec<Vec<Scalar>>> = Vec::new();
      for p in 0..block_num_instances {
        perm_block_w3.push(vec![Vec::new(); block_num_proofs[p]]);
        for q in (0..block_num_proofs[p]).rev() {
          perm_block_w3[p][q] = vec![ZERO; 4];
          perm_block_w3[p][q][0] = block_inputs_mat[p][q][0];
          perm_block_w3[p][q][1] = perm_block_w3[p][q][0] * (comb_tau - perm_block_w2[p][q].iter().fold(ZERO, |a, b| a + b));
          if q != block_num_proofs[p] - 1 {
            perm_block_w3[p][q][3] = perm_block_w3[p][q][1] * (perm_block_w3[p][q + 1][2] + ONE - perm_block_w3[p][q + 1][0]);
          } else {
            perm_block_w3[p][q][3] = perm_block_w3[p][q][1];
          }
          perm_block_w3[p][q][2] = perm_block_w3[p][q][0] * perm_block_w3[p][q][3];
        }
      }
      let mut perm_exec_w3 = vec![Vec::new(); consis_num_proofs];
      for q in (0..consis_num_proofs).rev() {
        perm_exec_w3[q] = vec![ZERO; 4];
        perm_exec_w3[q][0] = exec_inputs_list[q][0];
        perm_exec_w3[q][1] = (comb_tau - perm_exec_w2[q].iter().fold(ZERO, |a, b| a + b)) * exec_inputs_list[q][0];
        if q != consis_num_proofs - 1 {
          perm_exec_w3[q][3] = perm_exec_w3[q][1] * (perm_exec_w3[q + 1][2] + ONE - perm_exec_w3[q + 1][0]);
        } else {
          perm_exec_w3[q][3] = perm_exec_w3[q][1];
        }
        perm_exec_w3[q][2] = perm_exec_w3[q][0] * perm_exec_w3[q][3];
      }

      // create a multilinear polynomial using the supplied assignment for variables
      let perm_poly_w0 = DensePolynomial::new(perm_w0.clone());
      // produce a commitment to the satisfying assignment
      let (perm_comm_w0, _blinds_vars) = perm_poly_w0.commit(&vars_gens.gens_pc, None);
      // add the commitment to the prover's transcript
      perm_comm_w0.append_to_transcript(b"poly_commitment", transcript);

      // commit the witnesses and inputs separately instance-by-instance
      let mut perm_block_poly_w2_list = Vec::new();
      let mut perm_block_comm_w2_list = Vec::new();
      let mut perm_block_poly_w3_list = Vec::new();
      let mut perm_block_comm_w3_list = Vec::new();

      for p in 0..block_num_instances {
        let (perm_block_poly_w2, perm_block_comm_w2) = {
          // Flatten the witnesses into a Q_i * X list
          let w2_list_p = perm_block_w2[p].iter().fold(Vec::new(), |a, b| [a, b.to_vec()].concat());
          // create a multilinear polynomial using the supplied assignment for variables
          let perm_block_poly_w2 = DensePolynomial::new(w2_list_p);
          // produce a commitment to the satisfying assignment
          let (perm_block_comm_w2, _blinds_vars) = perm_block_poly_w2.commit(&vars_gens.gens_pc, None);

          // add the commitment to the prover's transcript
          perm_block_comm_w2.append_to_transcript(b"poly_commitment", transcript);
          (perm_block_poly_w2, perm_block_comm_w2)
        };
        perm_block_poly_w2_list.push(perm_block_poly_w2);
        perm_block_comm_w2_list.push(perm_block_comm_w2);
        
        let (perm_block_poly_w3, perm_block_comm_w3) = {
          // Flatten the witnesses into a Q_i * X list
          let w3_list_p = perm_block_w3[p].iter().fold(Vec::new(), |a, b| [a, b.to_vec()].concat());
          // create a multilinear polynomial using the supplied assignment for variables
          let perm_block_poly_w3 = DensePolynomial::new(w3_list_p);

          // produce a commitment to the satisfying assignment
          let (perm_block_comm_w3, _blinds_vars) = perm_block_poly_w3.commit(&vars_gens.gens_pc, None);

          // add the commitment to the prover's transcript
          perm_block_comm_w3.append_to_transcript(b"poly_commitment", transcript);
          (perm_block_poly_w3, perm_block_comm_w3)
        };
        perm_block_poly_w3_list.push(perm_block_poly_w3);
        perm_block_comm_w3_list.push(perm_block_comm_w3);
      }

      let (
        perm_exec_poly_w2,
        perm_exec_comm_w2,
        perm_exec_poly_w3,
        perm_exec_comm_w3,
      ) = {
        let (perm_exec_poly_w2, perm_exec_comm_w2) = {
          // Flatten the witnesses into a Q_i * X list
          let w2_list_p = perm_exec_w2.iter().fold(Vec::new(), |a, b| [a, b.to_vec()].concat());
          // create a multilinear polynomial using the supplied assignment for variables
          let perm_exec_poly_w2 = DensePolynomial::new(w2_list_p);

          // produce a commitment to the satisfying assignment
          let (perm_exec_comm_w2, _blinds_vars) = perm_exec_poly_w2.commit(&vars_gens.gens_pc, None);

          // add the commitment to the prover's transcript
          perm_exec_comm_w2.append_to_transcript(b"poly_commitment", transcript);
          (perm_exec_poly_w2, perm_exec_comm_w2)
        };
        
        let (perm_exec_poly_w3, perm_exec_comm_w3) = {
          // Flatten the witnesses into a Q_i * X list
          let w3_list_p = perm_exec_w3.iter().fold(Vec::new(), |a, b| [a, b.to_vec()].concat());
          // create a multilinear polynomial using the supplied assignment for variables
          let perm_exec_poly_w3 = DensePolynomial::new(w3_list_p);

          // produce a commitment to the satisfying assignment
          let (perm_exec_comm_w3, _blinds_vars) = perm_exec_poly_w3.commit(&vars_gens.gens_pc, None);

          // add the commitment to the prover's transcript
          perm_exec_comm_w3.append_to_transcript(b"poly_commitment", transcript);
          (perm_exec_poly_w3, perm_exec_comm_w3)
        };

        (
          perm_exec_poly_w2,
          perm_exec_comm_w2,
          perm_exec_poly_w3,
          perm_exec_comm_w3,
        )
      };

      // FOR CONSIS
      // w2 is <0, i0 * r, i1 * r^2, ..., 0, o0 * r, o1 * r^2, ...>
      // w3 is <v, v * (cnst + i0 * r + i1 * r^2 + i2 * r^3 + ...), v * (cnst + o0 * r + o1 * r^2 + o2 * r^3 + ...), 0>
      let mut consis_w2 = Vec::new();
      let mut consis_w3 = Vec::new();
      for q in 0..consis_num_proofs {
        consis_w2.push(vec![ZERO; num_ios]);
        consis_w3.push(vec![ZERO; 4]);
        
        consis_w3[q][1] = exec_inputs_list[q][0];
        consis_w3[q][2] = exec_inputs_list[q][0];
        for i in 1..num_inputs_unpadded {
          consis_w2[q][i] = perm_w0[i] * exec_inputs_list[q][i];
          consis_w2[q][num_inputs_unpadded + i] = perm_w0[i] * exec_inputs_list[q][num_inputs_unpadded + i];
          consis_w3[q][1] += consis_w2[q][i];
          consis_w3[q][2] += consis_w2[q][num_inputs_unpadded + i];
        }
        consis_w3[q][0] = exec_inputs_list[q][0];
        consis_w3[q][1] *= exec_inputs_list[q][0];
        consis_w3[q][2] *= exec_inputs_list[q][0];
      }

      let (consis_poly_w2, consis_comm_w2) = {
        // Flatten the witnesses into a Q_i * X list
        let w2_list_p = consis_w2.iter().fold(Vec::new(), |a, b| [a, b.to_vec()].concat());
        // create a multilinear polynomial using the supplied assignment for variables
        let consis_poly_w2 = DensePolynomial::new(w2_list_p);

        // produce a commitment to the satisfying assignment
        let (consis_comm_w2, _blinds_vars) = consis_poly_w2.commit(&vars_gens.gens_pc, None);

        // add the commitment to the prover's transcript
        consis_comm_w2.append_to_transcript(b"poly_commitment", transcript);
        (consis_poly_w2, consis_comm_w2)
      };
      
      let (consis_poly_w3, consis_comm_w3) = {
        // Flatten the witnesses into a Q_i * X list
        let w3_list_p = consis_w3.iter().fold(Vec::new(), |a, b| [a, b.to_vec()].concat());
        // create a multilinear polynomial using the supplied assignment for variables
        let consis_poly_w3 = DensePolynomial::new(w3_list_p);

        // produce a commitment to the satisfying assignment
        let (consis_comm_w3, _blinds_vars) = consis_poly_w3.commit(&vars_gens.gens_pc, None);

        // add the commitment to the prover's transcript
        consis_comm_w3.append_to_transcript(b"poly_commitment", transcript);
        (consis_poly_w3, consis_comm_w3)
      };

      let perm_w0_prover = ProverWitnessSecInfo::new(vec![vec![perm_w0]], vec![perm_poly_w0]);
      let perm_block_w2_prover = ProverWitnessSecInfo::new(perm_block_w2, perm_block_poly_w2_list);
      let perm_block_w3_prover = ProverWitnessSecInfo::new(perm_block_w3, perm_block_poly_w3_list);
      let perm_exec_w2_prover = ProverWitnessSecInfo::new(vec![perm_exec_w2], vec![perm_exec_poly_w2]);
      let perm_exec_w3_prover = ProverWitnessSecInfo::new(vec![perm_exec_w3], vec![perm_exec_poly_w3]);
      let consis_w2_prover = ProverWitnessSecInfo::new(vec![consis_w2], vec![consis_poly_w2]);
      let consis_w3_prover = ProverWitnessSecInfo::new(vec![consis_w3], vec![consis_poly_w3]);

      (
        comb_tau,
        comb_r,

        perm_w0_prover,
        vec![perm_comm_w0],
        perm_block_w2_prover,
        perm_block_comm_w2_list,
        perm_block_w3_prover,
        perm_block_comm_w3_list,
        perm_exec_w2_prover,
        vec![perm_exec_comm_w2],
        perm_exec_w3_prover,
        vec![perm_exec_comm_w3],
        consis_w2_prover,
        vec![consis_comm_w2],
        consis_w3_prover,
        vec![consis_comm_w3],
      )
    };

    // Memory-per-block
    let (
      mem_w0_prover,
      mem_comm_w0,
      mem_block_w3_prover,
      mem_block_comm_w3_list
    ) = {
      if total_num_mem_accesses_bound > 0 {
        // mask is unary representation of block_num_mem_accesses[p]
        let zero = ZERO;
        let one = ONE;

        // mem_w0 is (tau, r, 0, 0)
        // We don't use perm_w0 because we want mem_w0 to have width 4
        let mem_w0 = vec![comb_tau, comb_r, ZERO, ZERO];
        // create a multilinear polynomial using the supplied assignment for variables
        let mem_poly_w0 = DensePolynomial::new(mem_w0.clone());
        // produce a commitment to the satisfying assignment
        let (mem_comm_w0, _blinds_vars) = mem_poly_w0.commit(&vars_gens.gens_pc, None);
        // add the commitment to the prover's transcript
        mem_comm_w0.append_to_transcript(b"poly_commitment", transcript);

        // w3 is (v, x, pi, D, MR, MD, MC, MR, MR, MC, ...)
        let mut mem_block_w3 = Vec::new();
        let V_addr = |i: usize| 1 + 2 * i;
        let V_val = |i: usize| 2 + 2 * i;
        let V_MR = |i: usize| 4 + 3 * i;
        let V_MD = |i: usize| 5 + 3 * i;
        let V_MC = |i: usize| 6 + 3 * i;
        for p in 0..block_num_instances {
          mem_block_w3.push(vec![Vec::new(); block_num_proofs[p]]);
          for q in (0..block_num_proofs[p]).rev() {
            mem_block_w3[p][q] = vec![zero; addr_block_w3_size];
            mem_block_w3[p][q][0] = block_vars_mat[p][q][0];
            // Compute MR, MD, MC
            for i in 0..max_block_num_mem_accesses {
              // MR = r * val
              let val = if block_vars_mat[p][q].len() > V_val(i) { block_vars_mat[p][q][V_val(i)] } else { ZERO };
              mem_block_w3[p][q][V_MR(i)] = comb_r * val;
              // MD = mask * (tau - addr - MR)
              let addr = if block_vars_mat[p][q].len() > V_addr(i) { block_vars_mat[p][q][V_addr(i)] } else { ZERO };
              let t = comb_tau - addr - mem_block_w3[p][q][V_MR(i)];
              mem_block_w3[p][q][V_MD(i)] = mem_block_mask[p][0][i] * t;
              // MC = (1 or MC[i-1]) * (MD + 1 - mask)
              let t = mem_block_w3[p][q][V_MD(i)] + one - mem_block_mask[p][0][i];
              mem_block_w3[p][q][V_MC(i)] = 
                if i == 0 { block_vars_mat[p][q][0] * t }
                else { mem_block_w3[p][q][V_MC(i - 1)] * t };
            }
            // Compute x
            mem_block_w3[p][q][1] = mem_block_w3[p][q][V_MC(max_block_num_mem_accesses - 1)];
            // Compute D and pi
            if q != block_num_proofs[p] - 1 {
              mem_block_w3[p][q][3] = mem_block_w3[p][q][1] * (mem_block_w3[p][q + 1][2] + one - mem_block_w3[p][q + 1][0]);
            } else {
              mem_block_w3[p][q][3] = mem_block_w3[p][q][1];
            }
            mem_block_w3[p][q][2] = mem_block_w3[p][q][0] * mem_block_w3[p][q][3];
          }
        }

        // commit the witnesses and inputs separately instance-by-instance
        let mut mem_block_poly_w3_list = Vec::new();
        let mut mem_block_comm_w3_list = Vec::new();

        for p in 0..block_num_instances {
          let (mem_block_poly_w3, mem_block_comm_w3) = {
            // Flatten the witnesses into a Q_i * X list
            let w1_list_p = mem_block_w3[p].iter().fold(Vec::new(), |a, b| [a, b.to_vec()].concat());
            // create a multilinear polynomial using the supplied assignment for variables
            let mem_block_poly_w3 = DensePolynomial::new(w1_list_p);
            // produce a commitment to the satisfying assignment
            let (mem_block_comm_w3, _blinds_vars) = mem_block_poly_w3.commit(&vars_gens.gens_pc, None);

            // add the commitment to the prover's transcript
            mem_block_comm_w3.append_to_transcript(b"poly_commitment", transcript);
            (mem_block_poly_w3, mem_block_comm_w3)
          };
          mem_block_poly_w3_list.push(mem_block_poly_w3);
          mem_block_comm_w3_list.push(mem_block_comm_w3);
        }

        let mem_w0_prover = ProverWitnessSecInfo::new(vec![vec![mem_w0]], vec![mem_poly_w0]);
        let mem_block_w3_prover = ProverWitnessSecInfo::new(mem_block_w3, mem_block_poly_w3_list);

        (
          mem_w0_prover,
          vec![mem_comm_w0],
          mem_block_w3_prover,
          mem_block_comm_w3_list
        )
      } else {
        (
          ProverWitnessSecInfo::dummy(),
          Vec::new(),
          ProverWitnessSecInfo::dummy(),
          Vec::new()
        )
      }
    };

    // Memory-as-a-whole
    let (
      mem_addr_w1_prover,
      mem_addr_comm_w1,
      mem_addr_w3_prover,
      mem_addr_comm_w3
    ) = {
      if total_num_mem_accesses > 0 {
        // mem_addr_w1 is (v, x, pi, D) 
        let mut mem_addr_w1 = vec![vec![ZERO; 4]; total_num_mem_accesses];
        for q in (0..total_num_mem_accesses).rev() {
          // v
          mem_addr_w1[q][0] = addr_mems_list[q][0];
          // x = v * (tau - addr - r * val)
          mem_addr_w1[q][1] = addr_mems_list[q][0] * (comb_tau - addr_mems_list[q][1] - comb_r * addr_mems_list[q][2]);
          // pi and D
          if q != total_num_mem_accesses - 1 {
            mem_addr_w1[q][3] = mem_addr_w1[q][1] * (mem_addr_w1[q + 1][2] + ONE - mem_addr_w1[q + 1][0]);
          } else {
            mem_addr_w1[q][3] = mem_addr_w1[q][1];
          }
          mem_addr_w1[q][2] = mem_addr_w1[q][0] * mem_addr_w1[q][3];
        }

        // mem_addr_w3 is (MR, _, _, _)
        let mut mem_addr_w3 = Vec::new();
        for q in 0..total_num_mem_accesses {
          mem_addr_w3.push(vec![ZERO; 4]);
          // MR
          mem_addr_w3[q][0] = comb_r * addr_mems_list[q][2];
        }

        let (
          mem_addr_poly_w1,
          mem_addr_comm_w1,
          mem_addr_poly_w3,
          mem_addr_comm_w3,
        ) = {
          let (mem_addr_poly_w1, mem_addr_comm_w1) = {
            // Flatten the witnesses into a Q_i * X list
            let w1_list_p = mem_addr_w1.iter().fold(Vec::new(), |a, b| [a, b.to_vec()].concat());
            // create a multilinear polynomial using the supplied assignment for variables
            let mem_addr_poly_w1 = DensePolynomial::new(w1_list_p);

            // produce a commitment to the satisfying assignment
            let (mem_addr_comm_w1, _blinds_vars) = mem_addr_poly_w1.commit(&vars_gens.gens_pc, None);

            // add the commitment to the prover's transcript
            mem_addr_comm_w1.append_to_transcript(b"poly_commitment", transcript);
            (mem_addr_poly_w1, mem_addr_comm_w1)
          };
          
          let (mem_addr_poly_w3, mem_addr_comm_w3) = {
            // Flatten the witnesses into a Q_i * X list
            let w3_list_p = mem_addr_w3.iter().fold(Vec::new(), |a, b| [a, b.to_vec()].concat());
            // create a multilinear polynomial using the supplied assignment for variables
            let mem_addr_poly_w3 = DensePolynomial::new(w3_list_p);

            // produce a commitment to the satisfying assignment
            let (mem_addr_comm_w3, _blinds_vars) = mem_addr_poly_w3.commit(&vars_gens.gens_pc, None);

            // add the commitment to the prover's transcript
            mem_addr_comm_w3.append_to_transcript(b"poly_commitment", transcript);
            (mem_addr_poly_w3, mem_addr_comm_w3)
          };

          (
            mem_addr_poly_w1,
            mem_addr_comm_w1,
            mem_addr_poly_w3,
            mem_addr_comm_w3,
          )
        };

        let mem_addr_w1_prover = ProverWitnessSecInfo::new(vec![mem_addr_w1], vec![mem_addr_poly_w1]);
        let mem_addr_w3_prover = ProverWitnessSecInfo::new(vec![mem_addr_w3], vec![mem_addr_poly_w3]);

        (
          mem_addr_w1_prover,
          vec![mem_addr_comm_w1],
          mem_addr_w3_prover,
          vec![mem_addr_comm_w3]
        )
      } else {
        (
          ProverWitnessSecInfo::dummy(),
          Vec::new(),
          ProverWitnessSecInfo::dummy(),
          Vec::new()
        )
      }
    };
    timer_gen.stop();

    // Compute perm_size_bound
    let perm_size_bound = max(total_num_proofs_bound, total_num_mem_accesses_bound);
    // Construct vars_info for inputs
    let block_vars_prover = &ProverWitnessSecInfo::new(block_vars_mat, block_poly_vars_list);
    let block_inputs_prover = &ProverWitnessSecInfo::new(block_inputs_mat, block_poly_inputs_list);
    let exec_inputs_prover = &ProverWitnessSecInfo::new(vec![exec_inputs_list], exec_poly_inputs);
    let addr_mems_prover = &ProverWitnessSecInfo::new(vec![addr_mems_list], addr_poly_mems);
    let mem_block_mask_prover = &ProverWitnessSecInfo::new(mem_block_mask, mem_block_poly_mask_list);

    // Convert shared elements into references
    let mut transcript0 = transcript.clone();
    let mut transcript1 = transcript.clone();
    let mut transcript2 = transcript.clone();
    let mut transcript3 = transcript.clone();
    let mut transcript4 = transcript.clone();
    let mut transcript5 = transcript.clone();
    let mut transcript6 = transcript.clone();
    let mut transcript7 = transcript.clone();
    let mut transcript8 = transcript.clone();
    let mut transcript9 = transcript.clone();
    let mut transcript10 = transcript.clone();
    let mut transcript11 = transcript.clone();
    let mut transcript12 = transcript.clone();
    // we create a Transcript object seeded with a random Scalar
    // to aid the prover produce its randomness
    let mut random_tape = RandomTape::new(b"proof");
    let mut random_tape0 = random_tape.clone();
    let mut random_tape1 = random_tape.clone();
    let mut random_tape2 = random_tape.clone();
    let mut random_tape3 = random_tape.clone();
    let mut random_tape4 = random_tape.clone();
    let mut random_tape5 = random_tape.clone();
    let mut random_tape6 = random_tape.clone();
    let mut random_tape7 = random_tape.clone();
    let mut random_tape8 = random_tape.clone();
    let mut random_tape9 = random_tape.clone();
    let mut random_tape10 = random_tape.clone();
    let mut random_tape11 = random_tape.clone();
    let mut random_tape12 = random_tape.clone();
    // Initialize all 
    let (
      block_r1cs_sat_proof,
      block_inst_evals_bound_rp,
      block_inst_evals_list,
      block_r1cs_eval_proof,

      consis_comb_r1cs_sat_proof,
      consis_comb_inst_evals,
      consis_comb_r1cs_eval_proof,

      consis_check_r1cs_sat_proof,
      consis_check_inst_evals,
      consis_check_r1cs_eval_proof,

      perm_prelim_r1cs_sat_proof,
      perm_prelim_inst_evals,
      perm_prelim_r1cs_eval_proof,
      proof_eval_perm_w0_at_zero,
      proof_eval_perm_w0_at_one,

      perm_block_root_r1cs_sat_proof,
      perm_block_root_inst_evals,
      perm_block_root_r1cs_eval_proof,

      perm_block_poly_r1cs_sat_proof,
      perm_block_poly_inst_evals,
      perm_block_poly_r1cs_eval_proof,
      perm_block_poly_list,
      proof_eval_perm_block_prod_list,

      perm_exec_root_r1cs_sat_proof,
      perm_exec_root_inst_evals,
      perm_exec_root_r1cs_eval_proof,

      perm_exec_poly_r1cs_sat_proof,
      perm_exec_poly_inst_evals,
      perm_exec_poly_r1cs_eval_proof,
      perm_exec_poly,
      proof_eval_perm_exec_prod,

      mem_block_proofs,
      mem_addr_proofs
    ) = thread::scope(|s| {
      // --
      // BLOCK CORRECTNESS
      // --

      let block_correctness_proof = s.spawn(move || {
        let timer_proof = Timer::new("Block Correctness");
        let (block_r1cs_sat_proof, block_challenges) = {
          let (proof, block_challenges) = {
            R1CSProof::prove(
              block_num_instances,
              block_max_num_proofs,
              block_num_proofs,
              num_vars,
              2,
              vec![&block_inputs_prover, &block_vars_prover],
              &block_inst.inst,
              &vars_gens,
              &mut transcript0,
              &mut random_tape0,
            )
          };

          let proof_encoded: Vec<u8> = bincode::serialize(&proof).unwrap();
          Timer::print(&format!("len_r1cs_sat_proof {:?}", proof_encoded.len()));

          (proof, block_challenges)
        };

        // Final evaluation on BLOCK
        let (block_inst_evals_bound_rp, block_inst_evals_list, block_r1cs_eval_proof) = {
          let [rp, _, rx, ry] = block_challenges;
          let inst = block_inst;
          let timer_eval = Timer::new("eval_sparse_polys");

          let mut r1cs_eval_proof_list = Vec::new();
          let (inst_evals_list, inst_evals_bound_rp) = inst.inst.multi_evaluate(&rp, &rx, &ry);
          timer_eval.stop();
          for i in 0..block_num_instances {
            let inst_evals = inst_evals_list[i];
            let (Ar, Br, Cr) = &inst_evals;
            Ar.append_to_transcript(b"Ar_claim", &mut transcript0);
            Br.append_to_transcript(b"Br_claim", &mut transcript0);
            Cr.append_to_transcript(b"Cr_claim", &mut transcript0);

            let r1cs_eval_proof = {
              let proof = R1CSEvalProof::prove(
                &block_decomm[i].decomm,
                &rx,
                &ry,
                &inst_evals,
                &block_gens.gens_r1cs_eval,
                &mut transcript0,
                &mut random_tape0,
              );

              let proof_encoded: Vec<u8> = bincode::serialize(&proof).unwrap();
              Timer::print(&format!("len_r1cs_eval_proof {:?}", proof_encoded.len()));
              proof
            };
            r1cs_eval_proof_list.push(r1cs_eval_proof);
          }


          (inst_evals_bound_rp, inst_evals_list, r1cs_eval_proof_list)
        };
        timer_proof.stop();

        (block_r1cs_sat_proof, block_inst_evals_bound_rp, block_inst_evals_list, block_r1cs_eval_proof)
      });

      // --
      // CONSIS_COMB
      // --

      let timer_proof = Timer::new("Consis Comb");
      let (consis_comb_r1cs_sat_proof, consis_comb_challenges) = {
        let (proof, consis_comb_challenges) = {
          R1CSProof::prove(
            1,
            consis_num_proofs,
            &vec![consis_num_proofs],
            num_ios,
            4,
            vec![&perm_w0_prover, &exec_inputs_prover, &consis_w2_prover, &consis_w3_prover],
            &consis_comb_inst.inst,
            &vars_gens,
            &mut transcript1,
            &mut random_tape1,
          )
        };

        let proof_encoded: Vec<u8> = bincode::serialize(&proof).unwrap();
        Timer::print(&format!("len_r1cs_sat_proof {:?}", proof_encoded.len()));

        (proof, consis_comb_challenges)
      };

      // Final evaluation on CONSIS_COMB
      let (consis_comb_inst_evals, consis_comb_r1cs_eval_proof) = {
        let [_, _, rx, ry] = consis_comb_challenges;
        let inst = consis_comb_inst;
        let timer_eval = Timer::new("eval_sparse_polys");
        let inst_evals = {
          let (Ar, Br, Cr) = inst.inst.evaluate(&rx, &ry);
          Ar.append_to_transcript(b"Ar_claim", &mut transcript1);
          Br.append_to_transcript(b"Br_claim", &mut transcript1);
          Cr.append_to_transcript(b"Cr_claim", &mut transcript1);
          (Ar, Br, Cr)
        };
        timer_eval.stop();

        let r1cs_eval_proof = {
          let proof = R1CSEvalProof::prove(
            &consis_comb_decomm.decomm,
            &rx,
            &ry,
            &inst_evals,
            &consis_comb_gens.gens_r1cs_eval,
            &mut transcript1,
            &mut random_tape1,
          );

          let proof_encoded: Vec<u8> = bincode::serialize(&proof).unwrap();
          Timer::print(&format!("len_r1cs_eval_proof {:?}", proof_encoded.len()));
          proof
        };

        (inst_evals, r1cs_eval_proof)
      };
      timer_proof.stop();

      // --
      // CONSIS_CHECK
      // --

      let timer_proof = Timer::new("Consis Check");
      let (consis_check_r1cs_sat_proof, consis_check_challenges) = {
        let (proof, consis_check_challenges) = {
          R1CSProof::prove_single(
            1,
            consis_check_num_cons_base,
            4,
            total_num_proofs_bound,
            consis_num_proofs,
            &vec![consis_num_proofs],
            &consis_check_inst.inst,
            &vars_gens,
            4,
            &consis_w3_prover.w_mat,
            &consis_w3_prover.poly_w,
            &mut transcript2,
            &mut random_tape2,
          )
        };

        let proof_encoded: Vec<u8> = bincode::serialize(&proof).unwrap();
        Timer::print(&format!("len_r1cs_sat_proof {:?}", proof_encoded.len()));

        (proof, consis_check_challenges)
      };

      // Final evaluation on CONSIS_CHECK
      let (consis_check_inst_evals, consis_check_r1cs_eval_proof) = {
        let [_, rx, ry] = &consis_check_challenges;
        let inst = consis_check_inst;
        let timer_eval = Timer::new("eval_sparse_polys");
        let inst_evals = {
          let (Ar, Br, Cr) = inst.inst.evaluate(rx, ry);
          Ar.append_to_transcript(b"Ar_claim", &mut transcript2);
          Br.append_to_transcript(b"Br_claim", &mut transcript2);
          Cr.append_to_transcript(b"Cr_claim", &mut transcript2);
          (Ar, Br, Cr)
        };
        timer_eval.stop();

        let r1cs_eval_proof = {
          let proof = R1CSEvalProof::prove(
            &consis_check_decomm.decomm,
            &rx,
            &ry,
            &inst_evals,
            &consis_check_gens.gens_r1cs_eval,
            &mut transcript2,
            &mut random_tape2,
          );

          let proof_encoded: Vec<u8> = bincode::serialize(&proof).unwrap();
          Timer::print(&format!("len_r1cs_eval_proof {:?}", proof_encoded.len()));
          proof
        };

        
        (inst_evals, r1cs_eval_proof)
      };
      timer_proof.stop();

      // --
      // PERM_PRELIM
      // --

      let timer_proof = Timer::new("Perm Prelim");
      let (
        perm_prelim_r1cs_sat_proof, 
        perm_prelim_challenges,
        proof_eval_perm_w0_at_zero,
        proof_eval_perm_w0_at_one
      ) = {
        let (proof, perm_prelim_challenges) = {
          R1CSProof::prove(
            1,
            1,
            &vec![1],
            num_ios,
            1,
            vec![&perm_w0_prover],
            &perm_prelim_inst.inst,
            &vars_gens,
            &mut transcript3,
            &mut random_tape3,
          )
        };

        // Proof that first two entries of perm_w0 are tau and r
        let ry_len = perm_prelim_challenges[3].len();
        let (proof_eval_perm_w0_at_zero, _comm_perm_w0_at_zero) = PolyEvalProof::prove(
          &perm_w0_prover.poly_w[0],
          None,
          &vec![ZERO; ry_len],
          &comb_tau,
          None,
          &vars_gens.gens_pc,
          &mut transcript3,
          &mut random_tape3,
        );
        let (proof_eval_perm_w0_at_one, _comm_perm_w0_at_one) = PolyEvalProof::prove(
          &perm_w0_prover.poly_w[0],
          None,
          &[vec![ZERO; ry_len - 1], vec![ONE]].concat(),
          &comb_r,
          None,
          &vars_gens.gens_pc,
          &mut transcript3,
          &mut random_tape3,
        );
        
        let proof_encoded: Vec<u8> = bincode::serialize(&proof).unwrap();
        Timer::print(&format!("len_r1cs_sat_proof {:?}", proof_encoded.len()));

        (
          proof, 
          perm_prelim_challenges,
          proof_eval_perm_w0_at_zero,
          proof_eval_perm_w0_at_one
        )
      };

      // Final evaluation on PERM_PRELIM
      let (perm_prelim_inst_evals, perm_prelim_r1cs_eval_proof) = {
        let [rp, _, rx, ry] = perm_prelim_challenges;
        let rx = [rp, rx].concat();
        let inst = perm_prelim_inst;
        let timer_eval = Timer::new("eval_sparse_polys");
        let inst_evals = {
          let (Ar, Br, Cr) = inst.inst.evaluate(&rx, &ry);
          Ar.append_to_transcript(b"Ar_claim", &mut transcript3);
          Br.append_to_transcript(b"Br_claim", &mut transcript3);
          Cr.append_to_transcript(b"Cr_claim", &mut transcript3);
          (Ar, Br, Cr)
        };
        timer_eval.stop();

        let r1cs_eval_proof = {
          let proof = R1CSEvalProof::prove(
            &perm_prelim_decomm.decomm,
            &rx,
            &ry,
            &inst_evals,
            &perm_prelim_gens.gens_r1cs_eval,
            &mut transcript3,
            &mut random_tape3,
          );

          let proof_encoded: Vec<u8> = bincode::serialize(&proof).unwrap();
          Timer::print(&format!("len_r1cs_eval_proof {:?}", proof_encoded.len()));
          proof
        };

        
        (inst_evals, r1cs_eval_proof)
      };
      timer_proof.stop();

      // --
      // PERM_BLOCK_ROOT
      // --

      let timer_proof = Timer::new("Perm Block Root");
      let (perm_block_root_r1cs_sat_proof, perm_block_root_challenges) = {
        let (proof, perm_block_root_challenges) = {
          R1CSProof::prove(
            block_num_instances,
            block_max_num_proofs,
            block_num_proofs,
            num_ios,
            4,
            vec![&perm_w0_prover, &block_inputs_prover, &perm_block_w2_prover, &perm_block_w3_prover],
            &perm_root_inst.inst,
            &vars_gens,
            &mut transcript4,
            &mut random_tape4,
          )
        };

        let proof_encoded: Vec<u8> = bincode::serialize(&proof).unwrap();
        Timer::print(&format!("len_r1cs_sat_proof {:?}", proof_encoded.len()));

        (proof, perm_block_root_challenges)
      };

      // Final evaluation on PERM_BLOCK_ROOT
      let (perm_block_root_inst_evals, perm_block_root_r1cs_eval_proof) = {
        let [_, _, rx, ry] = perm_block_root_challenges;
        let inst = perm_root_inst;
        let timer_eval = Timer::new("eval_sparse_polys");
        let inst_evals = {
          let (Ar, Br, Cr) = inst.inst.evaluate(&rx, &ry);
          Ar.append_to_transcript(b"Ar_claim", &mut transcript4);
          Br.append_to_transcript(b"Br_claim", &mut transcript4);
          Cr.append_to_transcript(b"Cr_claim", &mut transcript4);
          (Ar, Br, Cr)
        };
        timer_eval.stop();

        let r1cs_eval_proof = {
          let proof = R1CSEvalProof::prove(
            &perm_root_decomm.decomm,
            &rx,
            &ry,
            &inst_evals,
            &perm_root_gens.gens_r1cs_eval,
            &mut transcript4,
            &mut random_tape4,
          );

          let proof_encoded: Vec<u8> = bincode::serialize(&proof).unwrap();
          Timer::print(&format!("len_r1cs_eval_proof {:?}", proof_encoded.len()));
          proof
        };

        
        (inst_evals, r1cs_eval_proof)
      };
      timer_proof.stop();

      // --
      // PERM_BLOCK_POLY
      // --

      let timer_proof = Timer::new("Perm Block Poly");
      let (perm_block_poly_r1cs_sat_proof, perm_block_poly_challenges) = {
        let (proof, perm_block_poly_challenges) = {
          R1CSProof::prove_single(
            block_num_instances,
            perm_poly_num_cons_base,
            4,
            // We need to feed the compile-time bound because that is the size of the constraints
            // Unlike other instances, where the runtime bound is sufficient because that's the number of copies
            perm_size_bound,
            block_max_num_proofs,
            &block_num_proofs,
            &perm_poly_inst.inst,
            &vars_gens,
            4,
            &perm_block_w3_prover.w_mat,
            &perm_block_w3_prover.poly_w,
            &mut transcript5,
            &mut random_tape5,
          )
        };

        let proof_encoded: Vec<u8> = bincode::serialize(&proof).unwrap();
        Timer::print(&format!("len_r1cs_sat_proof {:?}", proof_encoded.len()));

        (proof, perm_block_poly_challenges)
      };

      // Final evaluation on PERM_BLOCK_POLY
      let (perm_block_poly_inst_evals, perm_block_poly_r1cs_eval_proof) = {
        let [_, rx, ry] = &perm_block_poly_challenges;
        let inst = perm_poly_inst;
        let timer_eval = Timer::new("eval_sparse_polys");
        let inst_evals = {
          let (Ar, Br, Cr) = inst.inst.evaluate(rx, ry);
          Ar.append_to_transcript(b"Ar_claim", &mut transcript5);
          Br.append_to_transcript(b"Br_claim", &mut transcript5);
          Cr.append_to_transcript(b"Cr_claim", &mut transcript5);
          (Ar, Br, Cr)
        };
        timer_eval.stop();

        let r1cs_eval_proof = {
          let proof = R1CSEvalProof::prove(
            &perm_poly_decomm.decomm,
            rx,
            ry,
            &inst_evals,
            &perm_poly_gens.gens_r1cs_eval,
            &mut transcript5,
            &mut random_tape5,
          );

          let proof_encoded: Vec<u8> = bincode::serialize(&proof).unwrap();
          Timer::print(&format!("len_r1cs_eval_proof {:?}", proof_encoded.len()));
          proof
        };

        
        (inst_evals, r1cs_eval_proof)
      };

      // Record the prod of each instance
      let (perm_block_poly_list, proof_eval_perm_block_prod_list) = {
        let mut perm_block_poly_list = Vec::new();
        let mut proof_eval_perm_block_prod_list = Vec::new();
        for p in 0..block_num_instances {
          let r_len = (block_num_proofs[p] * 4).log_2();
          // Prod is the 3rd entry
          let perm_block_poly = perm_block_w3_prover.poly_w[p][3];
          let (proof_eval_perm_block_prod, _comm_perm_block_prod) = PolyEvalProof::prove(
            &perm_block_w3_prover.poly_w[p],
            None,
            &[vec![ZERO; r_len - 2], vec![ONE; 2]].concat(),
            &perm_block_poly,
            None,
            &vars_gens.gens_pc,
            &mut transcript5,
            &mut random_tape5,
          );
          perm_block_poly_list.push(perm_block_poly);
          proof_eval_perm_block_prod_list.push(proof_eval_perm_block_prod);
        }
        (perm_block_poly_list, proof_eval_perm_block_prod_list)
      };
      timer_proof.stop();

      // --
      // PERM_EXEC_ROOT
      // --

      let timer_proof = Timer::new("Perm Exec Root");
      let (perm_exec_root_r1cs_sat_proof, perm_exec_root_challenges) = {
        let (proof, perm_exec_root_challenges) = {
          R1CSProof::prove(
            1,
            consis_num_proofs,
            &vec![consis_num_proofs],
            num_ios,
            4,
            vec![&perm_w0_prover, &exec_inputs_prover, &perm_exec_w2_prover, &perm_exec_w3_prover],
            &perm_root_inst.inst,
            &vars_gens,
            &mut transcript6,
            &mut random_tape6,
          )
        };

        let proof_encoded: Vec<u8> = bincode::serialize(&proof).unwrap();
        Timer::print(&format!("len_r1cs_sat_proof {:?}", proof_encoded.len()));

        (proof, perm_exec_root_challenges)
      };

      // Final evaluation on PERM_EXEC_ROOT
      let (perm_exec_root_inst_evals, perm_exec_root_r1cs_eval_proof) = {
        let [_, _, rx, ry] = perm_exec_root_challenges;
        let inst = perm_root_inst;
        let timer_eval = Timer::new("eval_sparse_polys");
        let inst_evals = {
          let (Ar, Br, Cr) = inst.inst.evaluate(&rx, &ry);
          Ar.append_to_transcript(b"Ar_claim", &mut transcript6);
          Br.append_to_transcript(b"Br_claim", &mut transcript6);
          Cr.append_to_transcript(b"Cr_claim", &mut transcript6);
          (Ar, Br, Cr)
        };
        timer_eval.stop();

        let r1cs_eval_proof = {
          let proof = R1CSEvalProof::prove(
            &perm_root_decomm.decomm,
            &rx,
            &ry,
            &inst_evals,
            &perm_root_gens.gens_r1cs_eval,
            &mut transcript6,
            &mut random_tape6,
          );

          let proof_encoded: Vec<u8> = bincode::serialize(&proof).unwrap();
          Timer::print(&format!("len_r1cs_eval_proof {:?}", proof_encoded.len()));
          proof
        };

        
        (inst_evals, r1cs_eval_proof)
      };
      timer_proof.stop();

      // --
      // PERM_EXEC_POLY
      // --

      let timer_proof = Timer::new("Perm Exec Poly");
      let (perm_exec_poly_r1cs_sat_proof, perm_exec_poly_challenges) = {
        let (proof, perm_exec_poly_challenges) = {
          R1CSProof::prove_single(
            1,
            perm_poly_num_cons_base,
            4,
            perm_size_bound,
            consis_num_proofs,
            &vec![consis_num_proofs],
            &perm_poly_inst.inst,
            &vars_gens,
            4,
            &perm_exec_w3_prover.w_mat,
            &perm_exec_w3_prover.poly_w,
            &mut transcript7,
            &mut random_tape7,
          )
        };

        let proof_encoded: Vec<u8> = bincode::serialize(&proof).unwrap();
        Timer::print(&format!("len_r1cs_sat_proof {:?}", proof_encoded.len()));

        (proof, perm_exec_poly_challenges)
      };

      // Final evaluation on PERM_EXEC_POLY
      let (perm_exec_poly_inst_evals, perm_exec_poly_r1cs_eval_proof) = {
        let [_, rx, ry] = &perm_exec_poly_challenges;
        let inst = perm_poly_inst;
        let timer_eval = Timer::new("eval_sparse_polys");
        let inst_evals = {
          let (Ar, Br, Cr) = inst.inst.evaluate(rx, ry);
          Ar.append_to_transcript(b"Ar_claim", &mut transcript7);
          Br.append_to_transcript(b"Br_claim", &mut transcript7);
          Cr.append_to_transcript(b"Cr_claim", &mut transcript7);
          (Ar, Br, Cr)
        };
        timer_eval.stop();

        let r1cs_eval_proof = {
          let proof = R1CSEvalProof::prove(
            &perm_poly_decomm.decomm,
            &rx,
            &ry,
            &inst_evals,
            &perm_poly_gens.gens_r1cs_eval,
            &mut transcript7,
            &mut random_tape7,
          );

          let proof_encoded: Vec<u8> = bincode::serialize(&proof).unwrap();
          Timer::print(&format!("len_r1cs_eval_proof {:?}", proof_encoded.len()));
          proof
        };

        
        (inst_evals, r1cs_eval_proof)
      };

      // Record the prod of instance
      let (perm_exec_poly, proof_eval_perm_exec_prod) = {
        let r_len = (consis_num_proofs * 4).log_2();
        // Prod is the 3rd entry
        let perm_exec_poly = perm_exec_w3_prover.poly_w[0][3];
        let (proof_eval_perm_exec_prod, _comm_perm_exec_prod) = PolyEvalProof::prove(
          &perm_exec_w3_prover.poly_w[0],
          None,
          &[vec![ZERO; r_len - 2], vec![ONE; 2]].concat(),
          &perm_exec_poly,
          None,
          &vars_gens.gens_pc,
          &mut transcript7,
          &mut random_tape7,
        );
        (perm_exec_poly, proof_eval_perm_exec_prod)
      };
      timer_proof.stop();

      // --
      // MEM_BLOCK
      // --

      let mem_block_proofs = {
        if total_num_mem_accesses_bound > 0 {
          // --
          // MEM_EXTRACT
          // --
          let timer_proof = Timer::new("Mem Extract");
          let (mem_extract_r1cs_sat_proof, mem_extract_challenges) = {
            let (proof, mem_extract_challenges) = {
              R1CSProof::prove(
                block_num_instances,
                block_max_num_proofs,
                block_num_proofs,
                addr_block_w3_size,
                4,
                vec![&mem_w0_prover, &mem_block_mask_prover, &block_vars_prover, &mem_block_w3_prover],
                &mem_extract_inst.inst,
                &vars_gens,
                &mut transcript8,
                &mut random_tape8,
              )
            };
      
            let proof_encoded: Vec<u8> = bincode::serialize(&proof).unwrap();
            Timer::print(&format!("len_r1cs_sat_proof {:?}", proof_encoded.len()));
      
            (proof, mem_extract_challenges)
          };
      
          // Final evaluation on MEM_EXTRACT
          let (mem_extract_inst_evals, mem_extract_r1cs_eval_proof) = {
            let [_, _, rx, ry] = mem_extract_challenges;
            let inst = mem_extract_inst;
            let timer_eval = Timer::new("eval_sparse_polys");
            let inst_evals = {
              let (Ar, Br, Cr) = inst.inst.evaluate(&rx, &ry);
              Ar.append_to_transcript(b"Ar_claim", &mut transcript8);
              Br.append_to_transcript(b"Br_claim", &mut transcript8);
              Cr.append_to_transcript(b"Cr_claim", &mut transcript8);
              (Ar, Br, Cr)
            };
            timer_eval.stop();
      
            let r1cs_eval_proof = {
              let proof = R1CSEvalProof::prove(
                &mem_extract_decomm.decomm,
                &rx,
                &ry,
                &inst_evals,
                &mem_extract_gens.gens_r1cs_eval,
                &mut transcript8,
                &mut random_tape8,
              );
      
              let proof_encoded: Vec<u8> = bincode::serialize(&proof).unwrap();
              Timer::print(&format!("len_r1cs_eval_proof {:?}", proof_encoded.len()));
              proof
            };
      
            
            (inst_evals, r1cs_eval_proof)
          };
          timer_proof.stop();

          // --
          // MEM_BLOCK_POLY
          // --
          let timer_proof = Timer::new("Mem Block Poly");
          let (mem_block_poly_r1cs_sat_proof, mem_block_poly_challenges) = {
            let (proof, mem_block_poly_challenges) = {
              R1CSProof::prove_single(
                block_num_instances,
                perm_poly_num_cons_base,
                4,
                // We need to feed the compile-time bound because that is the size of the constraints
                // Unlike other instances, where the runtime bound is sufficient because that's the number of copies
                perm_size_bound,
                block_max_num_proofs,
                &block_num_proofs,
                &perm_poly_inst.inst,
                &vars_gens,
                addr_block_w3_size,
                &mem_block_w3_prover.w_mat,
                &mem_block_w3_prover.poly_w,
                &mut transcript9,
                &mut random_tape9,
              )
            };
      
            let proof_encoded: Vec<u8> = bincode::serialize(&proof).unwrap();
            Timer::print(&format!("len_r1cs_sat_proof {:?}", proof_encoded.len()));
      
            (proof, mem_block_poly_challenges)
          };
      
          // Final evaluation on MEM_BLOCK_POLY
          let (mem_block_poly_inst_evals, mem_block_poly_r1cs_eval_proof) = {
            let [_, rx, ry] = &mem_block_poly_challenges;
            let inst = perm_poly_inst;
            let timer_eval = Timer::new("eval_sparse_polys");
            let inst_evals = {
              let (Ar, Br, Cr) = inst.inst.evaluate(rx, ry);
              Ar.append_to_transcript(b"Ar_claim", &mut transcript9);
              Br.append_to_transcript(b"Br_claim", &mut transcript9);
              Cr.append_to_transcript(b"Cr_claim", &mut transcript9);
              (Ar, Br, Cr)
            };
            timer_eval.stop();
      
            let r1cs_eval_proof = {
              let proof = R1CSEvalProof::prove(
                &perm_poly_decomm.decomm,
                &rx,
                &ry,
                &inst_evals,
                &perm_poly_gens.gens_r1cs_eval,
                &mut transcript9,
                &mut random_tape9,
              );
      
              let proof_encoded: Vec<u8> = bincode::serialize(&proof).unwrap();
              Timer::print(&format!("len_r1cs_eval_proof {:?}", proof_encoded.len()));
              proof
            };
      
            
            (inst_evals, r1cs_eval_proof)
          };
      
          // Record the prod of each instance
          let (mem_block_poly_list, proof_eval_mem_block_prod_list) = {
            let mut mem_block_poly_list = Vec::new();
            let mut proof_eval_mem_block_prod_list = Vec::new();
            for p in 0..block_num_instances {
              let r_len = (block_num_proofs[p] * addr_block_w3_size).log_2();
              // Prod is the 3rd entry
              let mem_block_poly = mem_block_w3_prover.poly_w[p][3];
              let (proof_eval_mem_block_prod, _comm_mem_block_prod) = PolyEvalProof::prove(
                &mem_block_w3_prover.poly_w[p],
                None,
                &[vec![ZERO; r_len - 2], vec![ONE; 2]].concat(),
                &mem_block_poly,
                None,
                &vars_gens.gens_pc,
                &mut transcript9,
                &mut random_tape9,
              );
              mem_block_poly_list.push(mem_block_poly);
              proof_eval_mem_block_prod_list.push(proof_eval_mem_block_prod);
            }
            (mem_block_poly_list, proof_eval_mem_block_prod_list)
          };
          timer_proof.stop();

          Some(MemBlockProofs {
            mem_extract_r1cs_sat_proof,
            mem_extract_inst_evals,
            mem_extract_r1cs_eval_proof,
      
            mem_block_poly_r1cs_sat_proof,
            mem_block_poly_inst_evals,
            mem_block_poly_r1cs_eval_proof,
            mem_block_poly_list,
            proof_eval_mem_block_prod_list,
          })
        } else {
          None
        }
      };

      // --
      // MEM_ADDR
      // --

      let mem_addr_proofs = {
        if total_num_mem_accesses > 0 {
          // --
          // MEM_COHERE
          // --
          let timer_proof = Timer::new("Mem Cohere");
          let (mem_cohere_r1cs_sat_proof, mem_cohere_challenges) = {
            let (proof, mem_cohere_challenges) = {
              R1CSProof::prove_single(
                1,
                mem_cohere_num_cons_base,
                4,
                total_num_mem_accesses_bound,
                total_num_mem_accesses,
                &vec![total_num_mem_accesses],
                &mem_cohere_inst.inst,
                &vars_gens,
                4,
                &addr_mems_prover.w_mat,
                &addr_mems_prover.poly_w,
                &mut transcript10,
                &mut random_tape10,
              )
            };
      
            let proof_encoded: Vec<u8> = bincode::serialize(&proof).unwrap();
            Timer::print(&format!("len_r1cs_sat_proof {:?}", proof_encoded.len()));
      
            (proof, mem_cohere_challenges)
          };
      
          // Final evaluation on MEM_COHERE
          let (mem_cohere_inst_evals, mem_cohere_r1cs_eval_proof) = {
            let [_, rx, ry] = &mem_cohere_challenges;
            let inst = mem_cohere_inst;
            let timer_eval = Timer::new("eval_sparse_polys");
            let inst_evals = {
              let (Ar, Br, Cr) = inst.inst.evaluate(rx, ry);
              Ar.append_to_transcript(b"Ar_claim", &mut transcript10);
              Br.append_to_transcript(b"Br_claim", &mut transcript10);
              Cr.append_to_transcript(b"Cr_claim", &mut transcript10);
              (Ar, Br, Cr)
            };
            timer_eval.stop();
      
            let r1cs_eval_proof = {
              let proof = R1CSEvalProof::prove(
                &mem_cohere_decomm.decomm,
                &rx,
                &ry,
                &inst_evals,
                &mem_cohere_gens.gens_r1cs_eval,
                &mut transcript10,
                &mut random_tape10,
              );
      
              let proof_encoded: Vec<u8> = bincode::serialize(&proof).unwrap();
              Timer::print(&format!("len_r1cs_eval_proof {:?}", proof_encoded.len()));
              proof
            };
      
            
            (inst_evals, r1cs_eval_proof)
          };
          timer_proof.stop();

          // --
          // MEM_ADDR_COMB
          // --
          let timer_proof = Timer::new("Mem Addr Comb");
          let (
            mem_addr_comb_r1cs_sat_proof, 
            mem_addr_comb_challenges,
            proof_eval_mem_w0_at_zero,
            proof_eval_mem_w0_at_one
          ) = {
            let (proof, mem_addr_comb_challenges) = {
              R1CSProof::prove(
                1,
                total_num_mem_accesses,
                &vec![total_num_mem_accesses],
                4,
                4,
                vec![&mem_w0_prover, &mem_addr_w1_prover, &addr_mems_prover, &mem_addr_w3_prover],
                &mem_addr_comb_inst.inst,
                &vars_gens,
                &mut transcript11,
                &mut random_tape11,
              )
            };

            // Proof that first two entries of mem_w0 are tau and r
            let ry_len = 2;
            let (proof_eval_mem_w0_at_zero, _comm_mem_w0_at_zero) = PolyEvalProof::prove(
              &mem_w0_prover.poly_w[0],
              None,
              &vec![ZERO; ry_len],
              &comb_tau,
              None,
              &vars_gens.gens_pc,
              &mut transcript11,
              &mut random_tape11,
            );
            let (proof_eval_mem_w0_at_one, _comm_mem_w0_at_one) = PolyEvalProof::prove(
              &mem_w0_prover.poly_w[0],
              None,
              &[vec![ZERO; ry_len - 1], vec![ONE]].concat(),
              &comb_r,
              None,
              &vars_gens.gens_pc,
              &mut transcript11,
              &mut random_tape11,
            );

            let proof_encoded: Vec<u8> = bincode::serialize(&proof).unwrap();
            Timer::print(&format!("len_r1cs_sat_proof {:?}", proof_encoded.len()));

            (proof, mem_addr_comb_challenges, proof_eval_mem_w0_at_zero, proof_eval_mem_w0_at_one)
          };

          // Final evaluation on MEM_ADDR_COMB
          let (mem_addr_comb_inst_evals, mem_addr_comb_r1cs_eval_proof) = {
            let [_, _, rx, ry] = mem_addr_comb_challenges;
            let inst = mem_addr_comb_inst;
            let timer_eval = Timer::new("eval_sparse_polys");
            let inst_evals = {
              let (Ar, Br, Cr) = inst.inst.evaluate(&rx, &ry);
              Ar.append_to_transcript(b"Ar_claim", &mut transcript11);
              Br.append_to_transcript(b"Br_claim", &mut transcript11);
              Cr.append_to_transcript(b"Cr_claim", &mut transcript11);
              (Ar, Br, Cr)
            };
            timer_eval.stop();

            let r1cs_eval_proof = {
              let proof = R1CSEvalProof::prove(
                &mem_addr_comb_decomm.decomm,
                &rx,
                &ry,
                &inst_evals,
                &mem_addr_comb_gens.gens_r1cs_eval,
                &mut transcript11,
                &mut random_tape11,
              );

              let proof_encoded: Vec<u8> = bincode::serialize(&proof).unwrap();
              Timer::print(&format!("len_r1cs_eval_proof {:?}", proof_encoded.len()));
              proof
            };

            
            (inst_evals, r1cs_eval_proof)
          };
          timer_proof.stop();

          // --
          // MEM_ADDR_POLY
          // --
          let timer_proof = Timer::new("Mem Addr Poly");
          let (mem_addr_poly_r1cs_sat_proof, mem_addr_poly_challenges) = {
            let (proof, mem_addr_poly_challenges) = {
              R1CSProof::prove_single(
                1,
                perm_poly_num_cons_base,
                4,
                perm_size_bound,
                total_num_mem_accesses,
                &vec![total_num_mem_accesses],
                &perm_poly_inst.inst,
                &vars_gens,
                4,
                &mem_addr_w1_prover.w_mat,
                &mem_addr_w1_prover.poly_w,
                &mut transcript12,
                &mut random_tape12,
              )
            };

            let proof_encoded: Vec<u8> = bincode::serialize(&proof).unwrap();
            Timer::print(&format!("len_r1cs_sat_proof {:?}", proof_encoded.len()));

            (proof, mem_addr_poly_challenges)
          };

          // Final evaluation on MEM_ADDR_POLY
          let (mem_addr_poly_inst_evals, mem_addr_poly_r1cs_eval_proof) = {
            let [_, rx, ry] = &mem_addr_poly_challenges;
            let inst = perm_poly_inst;
            let timer_eval = Timer::new("eval_sparse_polys");
            let inst_evals = {
              let (Ar, Br, Cr) = inst.inst.evaluate(rx, ry);
              Ar.append_to_transcript(b"Ar_claim", &mut transcript12);
              Br.append_to_transcript(b"Br_claim", &mut transcript12);
              Cr.append_to_transcript(b"Cr_claim", &mut transcript12);
              (Ar, Br, Cr)
            };
            timer_eval.stop();

            let r1cs_eval_proof = {
              let proof = R1CSEvalProof::prove(
                &perm_poly_decomm.decomm,
                &rx,
                &ry,
                &inst_evals,
                &perm_poly_gens.gens_r1cs_eval,
                &mut transcript12,
                &mut random_tape12,
              );

              let proof_encoded: Vec<u8> = bincode::serialize(&proof).unwrap();
              Timer::print(&format!("len_r1cs_eval_proof {:?}", proof_encoded.len()));
              proof
            };

            
            (inst_evals, r1cs_eval_proof)
          };
          timer_proof.stop();

          // Record the prod of instance
          let (mem_addr_poly, proof_eval_mem_addr_prod) = {
            let r_len = (total_num_mem_accesses * 4).log_2();
            // Prod is the 3rd entry
            let mem_addr_poly = mem_addr_w1_prover.poly_w[0][3];
            let (proof_eval_mem_addr_prod, _comm_mem_addr_prod) = PolyEvalProof::prove(
              &mem_addr_w1_prover.poly_w[0],
              None,
              &[vec![ZERO; r_len - 2], vec![ONE; 2]].concat(),
              &mem_addr_poly,
              None,
              &vars_gens.gens_pc,
              &mut transcript12,
              &mut random_tape12,
            );
            (mem_addr_poly, proof_eval_mem_addr_prod)
          };
          Some(MemAddrProofs {
            mem_cohere_r1cs_sat_proof,
            mem_cohere_inst_evals,
            mem_cohere_r1cs_eval_proof,
            
            mem_addr_comb_r1cs_sat_proof,
            mem_addr_comb_inst_evals,
            mem_addr_comb_r1cs_eval_proof,
            proof_eval_mem_w0_at_zero,
            proof_eval_mem_w0_at_one,
      
            mem_addr_poly_r1cs_sat_proof,
            mem_addr_poly_inst_evals,
            mem_addr_poly_r1cs_eval_proof,
            mem_addr_poly,
            proof_eval_mem_addr_prod,
          })
        } else {
          None
        }
      };

      let (block_r1cs_sat_proof, 
        block_inst_evals_bound_rp, 
        block_inst_evals_list, 
        block_r1cs_eval_proof
      ) = block_correctness_proof.join().unwrap();

      (
        block_r1cs_sat_proof,
        block_inst_evals_bound_rp,
        block_inst_evals_list,
        block_r1cs_eval_proof,

        consis_comb_r1cs_sat_proof,
        consis_comb_inst_evals,
        consis_comb_r1cs_eval_proof,

        consis_check_r1cs_sat_proof,
        consis_check_inst_evals,
        consis_check_r1cs_eval_proof,

        perm_prelim_r1cs_sat_proof,
        perm_prelim_inst_evals,
        perm_prelim_r1cs_eval_proof,
        proof_eval_perm_w0_at_zero,
        proof_eval_perm_w0_at_one,

        perm_block_root_r1cs_sat_proof,
        perm_block_root_inst_evals,
        perm_block_root_r1cs_eval_proof,

        perm_block_poly_r1cs_sat_proof,
        perm_block_poly_inst_evals,
        perm_block_poly_r1cs_eval_proof,
        perm_block_poly_list,
        proof_eval_perm_block_prod_list,

        perm_exec_root_r1cs_sat_proof,
        perm_exec_root_inst_evals,
        perm_exec_root_r1cs_eval_proof,

        perm_exec_poly_r1cs_sat_proof,
        perm_exec_poly_inst_evals,
        perm_exec_poly_r1cs_eval_proof,
        perm_exec_poly,
        proof_eval_perm_exec_prod,

        mem_block_proofs,
        mem_addr_proofs
      )
    });

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
      func_input_width,
      input_offset,
      output_offset,
      input,
      output,
      output_exec_num,
      vars_gens,
      transcript,
      &mut random_tape
    );
    timer_proof.stop();

    timer_prove.stop();
    SNARK {
      block_comm_vars_list,
      block_comm_inputs_list,
      exec_comm_inputs,
      addr_comm_mems,

      perm_comm_w0,
      perm_block_comm_w2_list,
      perm_block_comm_w3_list,
      perm_exec_comm_w2,
      perm_exec_comm_w3,

      consis_comm_w2,
      consis_comm_w3,

      mem_block_comm_w3_list,
      mem_comm_w0,
      mem_addr_comm_w1,
      mem_addr_comm_w3,

      block_r1cs_sat_proof,
      block_inst_evals_bound_rp,
      block_inst_evals_list,
      block_r1cs_eval_proof,

      consis_comb_r1cs_sat_proof,
      consis_comb_inst_evals,
      consis_comb_r1cs_eval_proof,

      consis_check_r1cs_sat_proof,
      consis_check_inst_evals,
      consis_check_r1cs_eval_proof,

      perm_prelim_r1cs_sat_proof,
      perm_prelim_inst_evals,
      perm_prelim_r1cs_eval_proof,
      proof_eval_perm_w0_at_zero,
      proof_eval_perm_w0_at_one,

      perm_block_root_r1cs_sat_proof,
      perm_block_root_inst_evals,
      perm_block_root_r1cs_eval_proof,

      perm_block_poly_r1cs_sat_proof,
      perm_block_poly_inst_evals,
      perm_block_poly_r1cs_eval_proof,
      perm_block_poly_list,
      proof_eval_perm_block_prod_list,

      perm_exec_root_r1cs_sat_proof,
      perm_exec_root_inst_evals,
      perm_exec_root_r1cs_eval_proof,

      perm_exec_poly_r1cs_sat_proof,
      perm_exec_poly_inst_evals,
      perm_exec_poly_r1cs_eval_proof,
      perm_exec_poly,
      proof_eval_perm_exec_prod,

      mem_block_proofs,
      mem_addr_proofs,

      io_proof
    }
  }

  /// A method to verify the SNARK proof of the satisfiability of an R1CS instance
  pub fn verify_parallel(
    &self,
    input_block_num: usize,
    output_block_num: usize,
    func_input_width: usize,
    input_offset: usize,
    output_offset: usize,
    input: &Vec<[u8; 32]>,
    output: &[u8; 32],
    output_exec_num: usize,

    num_vars: usize,
    num_ios: usize,
    addr_block_w3_size: usize,
    num_inputs_unpadded: usize,
    // How many variables (witnesses) are used by each block? Round to the next power of 2
    num_vars_per_block: &Vec<usize>,
    total_num_proofs_bound: usize,
    block_num_instances_bound: usize,

    block_max_num_proofs: usize,
    block_num_proofs: &Vec<usize>,
    block_num_cons: usize,
    block_comm: Vec<ComputationCommitment>,
    block_gens: SNARKGens,

    consis_num_proofs: usize,
    consis_comb_num_cons: usize,
    consis_comb_comm: &ComputationCommitment,
    consis_comb_gens: &SNARKGens,

    consis_check_num_cons_base: usize,
    consis_check_comm: &ComputationCommitment,
    consis_check_gens: &SNARKGens,

    perm_prelim_num_cons: usize,
    perm_prelim_comm: &ComputationCommitment,
    perm_prelim_gens: &SNARKGens,

    perm_root_num_cons: usize,
    perm_root_comm: &ComputationCommitment,
    perm_root_gens: &SNARKGens,

    perm_poly_num_cons_base: usize,
    perm_poly_comm: &ComputationCommitment,
    perm_poly_gens: &SNARKGens,

    max_block_num_mem_accesses: usize,
    mem_extract_num_cons: usize,
    mem_extract_comm: &ComputationCommitment,
    mem_extract_gens: &SNARKGens,

    total_num_mem_accesses_bound: usize,
    total_num_mem_accesses: usize,
    mem_cohere_num_cons_base: usize,
    mem_cohere_comm: &ComputationCommitment,
    mem_cohere_gens: &SNARKGens,

    mem_addr_comb_num_cons: usize,
    mem_addr_comb_comm: &ComputationCommitment,
    mem_addr_comb_gens: &SNARKGens,

    mem_block_comm_mask_list: &Vec<PolyCommitment>,

    vars_gens: &R1CSGens,
    transcript: &mut Transcript,
  ) -> Result<(), ProofVerifyError> {
    let timer_verify = Timer::new("SNARK::verify");
    transcript.append_protocol_name(SNARK::protocol_name());

    // --
    // ASSERTIONS
    // --
    assert!(0 < consis_num_proofs);
    for p in 0..block_num_instances_bound {
      assert!(block_num_proofs[p] <= block_max_num_proofs);
    }
    assert!(consis_num_proofs <= total_num_proofs_bound);
    assert!(total_num_mem_accesses <= total_num_mem_accesses_bound);

    // --
    // COMMITMENTS
    // --

    let input_block_num = Scalar::from(input_block_num as u64);
    let output_block_num = Scalar::from(output_block_num as u64);
    let input: Vec<Scalar> = input.iter().map(|i| Scalar::from_bytes(i).unwrap()).collect();
    let output: Scalar = Scalar::from_bytes(output).unwrap();
    {
      let timer_commit = Timer::new("inst_commit");
      // Commit public parameters
      Scalar::from(func_input_width as u64).append_to_transcript(b"func_input_width", transcript);
      Scalar::from(input_offset as u64).append_to_transcript(b"input_offset", transcript);
      Scalar::from(output_offset as u64).append_to_transcript(b"output_offset", transcript);
      Scalar::from(output_exec_num as u64).append_to_transcript(b"output_exec_num", transcript);
      Scalar::from(num_ios as u64).append_to_transcript(b"num_ios", transcript);
      for n in num_vars_per_block {
        Scalar::from(*n as u64).append_to_transcript(b"num_vars_per_block", transcript);
      }
      Scalar::from(addr_block_w3_size as u64).append_to_transcript(b"addr_block_w3_size", transcript);
      Scalar::from(num_inputs_unpadded as u64).append_to_transcript(b"num_inputs_unpadded", transcript);
      Scalar::from(total_num_proofs_bound as u64).append_to_transcript(b"total_num_proofs_bound", transcript);
      Scalar::from(block_num_instances_bound as u64).append_to_transcript(b"block_num_instances_bound", transcript);
      Scalar::from(block_max_num_proofs as u64).append_to_transcript(b"block_max_num_proofs", transcript);
      Scalar::from(max_block_num_mem_accesses as u64).append_to_transcript(b"max_block_num_mem_accesses", transcript);
      Scalar::from(total_num_mem_accesses_bound as u64).append_to_transcript(b"total_num_mem_accesses_bound", transcript);
      Scalar::from(total_num_mem_accesses as u64).append_to_transcript(b"total_num_mem_accesses", transcript);
      
      // commit mem_block_mask
      for c in mem_block_comm_mask_list {
        c.append_to_transcript(b"mem_block_masks", transcript);
      }
      // commit num_proofs
      Scalar::from(block_max_num_proofs as u64).append_to_transcript(b"block_max_num_proofs", transcript);
      for n in block_num_proofs {
        Scalar::from(*n as u64).append_to_transcript(b"block_num_proofs", transcript);
      }

      // append a commitment to the computation to the transcript
      for c in &block_comm {
        c.comm.append_to_transcript(b"block_comm", transcript);
      }
      consis_comb_comm.comm.append_to_transcript(b"consis_comm", transcript);
      consis_check_comm.comm.append_to_transcript(b"consis_comm", transcript);
      perm_prelim_comm.comm.append_to_transcript(b"block_comm", transcript);
      perm_root_comm.comm.append_to_transcript(b"block_comm", transcript);
      perm_poly_comm.comm.append_to_transcript(b"block_comm", transcript);
      mem_extract_comm.comm.append_to_transcript(b"block_comm", transcript);
      mem_cohere_comm.comm.append_to_transcript(b"consis_comm", transcript);
      mem_addr_comb_comm.comm.append_to_transcript(b"block_comm", transcript);

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
    let block_num_instances = block_num_proofs.iter().fold(0, |i, j| if *j > 0 { i + 1 } else { i });
    // Sort the following based on block_num_proofs:
    // - block_num_proofs
    // - block_inst, block_comm, block_decomm
    // - block_num_mem_accesses
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
    let index: Vec<usize> = inst_sorter.iter().map(|i| i.index).collect();
    let num_vars_per_block: Vec<usize> = (0..block_num_instances).map(|i| num_vars_per_block[index[i]]).collect();
    let block_comm: Vec<ComputationCommitment> = (0..block_num_instances).map(|i| block_comm[index[i]].clone()).collect();
    let mem_block_comm_mask_list: Vec<PolyCommitment> = (0..block_num_instances).map(|i| mem_block_comm_mask_list[index[i]].clone()).collect();

    // --
    // PADDING
    // --
    // Pad entries of block_num_proofs to a power of 2
    let block_max_num_proofs = block_max_num_proofs.next_power_of_two();
    for i in 0..block_num_instances {
      block_num_proofs[i] = block_num_proofs[i].next_power_of_two();
    }
    // Pad num_proofs with 1 until the next power of 2
    block_num_proofs.extend(vec![1; block_num_instances.next_power_of_two() - block_num_instances]);
    let block_num_proofs = &block_num_proofs;
    // Pad exec_inputs with dummys so the length is a power of 2
    let consis_num_proofs = consis_num_proofs.next_power_of_two();
    // Pad addr_mems with dummys so the length is a power of 2
    let total_num_mem_accesses = if total_num_mem_accesses == 0 { 0 } else { total_num_mem_accesses.next_power_of_two() };
    timer_sort.stop();

    // --
    // SAMPLE CHALLENGES, COMMIT WITNESSES, & CONSTRUCT WITNESS_SEC_INFO
    // --
    let timer_commit = Timer::new("witness_commit");
    let (
      block_vars_verifier,
      block_inputs_verifier,
      exec_inputs_verifier,
      addr_mems_verifier
    ) = {
      // add the commitment to the verifier's transcript
      for p in 0..block_num_instances {
        self.block_comm_vars_list[p].append_to_transcript(b"poly_commitment", transcript);
        self.block_comm_inputs_list[p].append_to_transcript(b"poly_commitment", transcript);
      }
      self.exec_comm_inputs[0].append_to_transcript(b"poly_commitment", transcript);
      if total_num_mem_accesses > 0 {
        self.addr_comm_mems[0].append_to_transcript(b"poly_commitment", transcript);
      }
      (
        &VerifierWitnessSecInfo::new(false, num_vars_per_block, &self.block_comm_vars_list),
        &VerifierWitnessSecInfo::new(false, vec![num_ios; block_num_instances], &self.block_comm_inputs_list),
        &VerifierWitnessSecInfo::new(false, vec![num_ios], &self.exec_comm_inputs),
        &VerifierWitnessSecInfo::new(false, vec![4], &self.addr_comm_mems),
      )
    };
    let mem_block_mask_verifier = VerifierWitnessSecInfo::new(
      true,
      vec![max_block_num_mem_accesses.next_power_of_two(); block_num_instances],
      &mem_block_comm_mask_list
    );

    let comb_tau = transcript.challenge_scalar(b"challenge_tau");
    let comb_r = transcript.challenge_scalar(b"challenge_r");
    
    let (
      perm_w0_verifier,
      perm_block_w2_verifier,
      perm_block_w3_verifier,
      perm_exec_w2_verifier,
      perm_exec_w3_verifier,
      consis_w2_verifier,
      consis_w3_verifier,
    ) = {
      self.perm_comm_w0[0].append_to_transcript(b"poly_commitment", transcript);
      for p in 0..block_num_instances {
        self.perm_block_comm_w2_list[p].append_to_transcript(b"poly_commitment", transcript);
        self.perm_block_comm_w3_list[p].append_to_transcript(b"poly_commitment", transcript);
      }
      self.perm_exec_comm_w2[0].append_to_transcript(b"poly_commitment", transcript);
      self.perm_exec_comm_w3[0].append_to_transcript(b"poly_commitment", transcript);
      self.consis_comm_w2[0].append_to_transcript(b"poly_commitment", transcript);
      self.consis_comm_w3[0].append_to_transcript(b"poly_commitment", transcript);
      (
        &VerifierWitnessSecInfo::new(true, vec![num_ios], &self.perm_comm_w0),
        &VerifierWitnessSecInfo::new(false, vec![num_ios; block_num_instances], &self.perm_block_comm_w2_list),
        &VerifierWitnessSecInfo::new(false, vec![4; block_num_instances], &self.perm_block_comm_w3_list),
        &VerifierWitnessSecInfo::new(false, vec![num_ios], &self.perm_exec_comm_w2),
        &VerifierWitnessSecInfo::new(false, vec![4], &self.perm_exec_comm_w3),
        &VerifierWitnessSecInfo::new(false, vec![num_ios], &self.consis_comm_w2),
        &VerifierWitnessSecInfo::new(false, vec![4], &self.consis_comm_w3),
      )
    };

    let (
      mem_w0_verifier,
      mem_block_w3_verifier
    ) = {
      if total_num_mem_accesses_bound > 0 {
        self.mem_comm_w0[0].append_to_transcript(b"poly_commitment", transcript);
        for p in 0..block_num_instances {
          self.mem_block_comm_w3_list[p].append_to_transcript(b"poly_commitment", transcript);
        }
      }
      (
        &VerifierWitnessSecInfo::new(true, vec![4], &self.mem_comm_w0),
        &VerifierWitnessSecInfo::new(false, vec![addr_block_w3_size; block_num_instances], &self.mem_block_comm_w3_list),
      )
    };

    let (
      mem_addr_w1_verifier,
      mem_addr_w3_verifier
    ) = {
      if total_num_mem_accesses > 0 {
        self.mem_addr_comm_w1[0].append_to_transcript(b"poly_commitment", transcript);
        self.mem_addr_comm_w3[0].append_to_transcript(b"poly_commitment", transcript);
      }
      (
        &VerifierWitnessSecInfo::new(false, vec![4], &self.mem_addr_comm_w1),
        &VerifierWitnessSecInfo::new(false, vec![4], &self.mem_addr_comm_w3),
      )
    };

    // Compute perm_size_bound
    let perm_size_bound = max(total_num_proofs_bound, total_num_mem_accesses_bound);
    timer_commit.stop();

    // Convert shared elements into references
    let mut transcript0 = transcript.clone();
    let mut transcript1 = transcript.clone();
    let mut transcript2 = transcript.clone();
    let mut transcript3 = transcript.clone();
    let mut transcript4 = transcript.clone();
    let mut transcript5 = transcript.clone();
    let mut transcript6 = transcript.clone();
    let mut transcript7 = transcript.clone();
    let mut transcript8 = transcript.clone();
    let mut transcript9 = transcript.clone();
    let mut transcript10 = transcript.clone();
    let mut transcript11 = transcript.clone();
    let mut transcript12 = transcript.clone();
    thread::scope(|s| {
      // --
      // BLOCK CORRECTNESS
      // --
      s.spawn(move || {
        let timer_sat_proof = Timer::new("Block Correctness Sat");
        let block_challenges = self.block_r1cs_sat_proof.verify(
          block_num_instances,
          block_max_num_proofs,
          block_num_proofs,
          num_vars,
          2,
          vec![block_inputs_verifier, block_vars_verifier],
          block_num_cons,
          vars_gens,
          &self.block_inst_evals_bound_rp,
          &mut transcript0,
        ).unwrap();
        timer_sat_proof.stop();

        let timer_eval_proof = Timer::new("Block Correctness Eval");
        // Verify Evaluation on BLOCK
        let mut A_evals = Vec::new();
        let mut B_evals = Vec::new();
        let mut C_evals = Vec::new();
        let [rp, _, rx, ry] = block_challenges;
        for i in 0..block_num_instances {
          let (Ar, Br, Cr) = self.block_inst_evals_list[i];
          Ar.append_to_transcript(b"Ar_claim", &mut transcript0);
          Br.append_to_transcript(b"Br_claim", &mut transcript0);
          Cr.append_to_transcript(b"Cr_claim", &mut transcript0);
          self.block_r1cs_eval_proof[i].verify(
            &block_comm[i].comm,
            &rx,
            &ry,
            &self.block_inst_evals_list[i],
            &block_gens.gens_r1cs_eval,
            &mut transcript0,
          ).unwrap();
          A_evals.push(Ar.clone());
          B_evals.push(Br.clone());
          C_evals.push(Cr.clone());
        }
        // Verify that block_inst_evals_bound_rp is block_inst_evals_list bind rp
        assert_eq!(DensePolynomial::new(A_evals).evaluate(&rp), self.block_inst_evals_bound_rp.0);
        assert_eq!(DensePolynomial::new(B_evals).evaluate(&rp), self.block_inst_evals_bound_rp.1);
        assert_eq!(DensePolynomial::new(C_evals).evaluate(&rp), self.block_inst_evals_bound_rp.2);
        timer_eval_proof.stop();
      });

      // --
      // CONSIS_COMB
      // --
      s.spawn(move || {
        let timer_sat_proof = Timer::new("Consis Comb Sat");
        let consis_comb_challenges = self.consis_comb_r1cs_sat_proof.verify(
          1,
          consis_num_proofs,
          &vec![consis_num_proofs],
          num_ios,
          4,
          vec![perm_w0_verifier, exec_inputs_verifier, consis_w2_verifier, consis_w3_verifier],
          consis_comb_num_cons,
          &vars_gens,
          &self.consis_comb_inst_evals,
          &mut transcript1,
        ).unwrap();
        timer_sat_proof.stop();
  
        let timer_eval_proof = Timer::new("Consis Comb Eval");
        // Verify Evaluation on CONSIS_COMB
        let (Ar, Br, Cr) = &self.consis_comb_inst_evals;
        Ar.append_to_transcript(b"Ar_claim", &mut transcript1);
        Br.append_to_transcript(b"Br_claim", &mut transcript1);
        Cr.append_to_transcript(b"Cr_claim", &mut transcript1);
        let [_, _, rx, ry] = consis_comb_challenges;
        self.consis_comb_r1cs_eval_proof.verify(
          &consis_comb_comm.comm,
          &rx,
          &ry,
          &self.consis_comb_inst_evals,
          &consis_comb_gens.gens_r1cs_eval,
          &mut transcript1,
        ).unwrap();
        timer_eval_proof.stop();
      });

      // --
      // CONSIS_CHECK
      // --
      s.spawn(move || {
        let timer_sat_proof = Timer::new("Consis Check Sat");
        let consis_check_challenges = self.consis_check_r1cs_sat_proof.verify_single(
          1,
          consis_check_num_cons_base,
          4,
          total_num_proofs_bound,
          consis_num_proofs,
          &vec![consis_num_proofs],
          &vars_gens,
          &self.consis_check_inst_evals,
          4,
          &self.consis_comm_w3,
          &mut transcript2,
        ).unwrap();
        timer_sat_proof.stop();

        let timer_eval_proof = Timer::new("Consis Check Eval");
        // Verify Evaluation on CONSIS_CHECK
        let (Ar, Br, Cr) = &self.consis_check_inst_evals;
        Ar.append_to_transcript(b"Ar_claim", &mut transcript2);
        Br.append_to_transcript(b"Br_claim", &mut transcript2);
        Cr.append_to_transcript(b"Cr_claim", &mut transcript2);
        let [_, rx, ry] = &consis_check_challenges;
        self.consis_check_r1cs_eval_proof.verify(
          &consis_check_comm.comm,
          rx,
          ry,
          &self.consis_check_inst_evals,
          &consis_check_gens.gens_r1cs_eval,
          &mut transcript2,
        ).unwrap();
        timer_eval_proof.stop();
      });

      // --
      // PERM_PRELIM
      // --
      s.spawn(move || {
        let timer_sat_proof = Timer::new("Perm Prelim Sat");
        let perm_prelim_challenges = self.perm_prelim_r1cs_sat_proof.verify(
          1,
          1,
          &vec![1],
          num_ios,
          1,
          vec![&perm_w0_verifier],
          perm_prelim_num_cons,
          &vars_gens,
          &self.perm_prelim_inst_evals,
          &mut transcript3,
        ).unwrap();
        // Proof that first two entries of perm_w0 are tau and r
        let ry_len = perm_prelim_challenges[3].len();
        self.proof_eval_perm_w0_at_zero.verify_plain(
          &vars_gens.gens_pc,
          &mut transcript3,
          &vec![ZERO; ry_len],
          &comb_tau,
          &self.perm_comm_w0[0],
        ).unwrap();
        self.proof_eval_perm_w0_at_one.verify_plain(
          &vars_gens.gens_pc,
          &mut transcript3,
          &[vec![ZERO; ry_len - 1], vec![ONE]].concat(),
          &comb_r,
          &self.perm_comm_w0[0],
        ).unwrap();
        timer_sat_proof.stop();

        let timer_eval_proof = Timer::new("Perm Prelim Eval");
        // Verify Evaluation on PERM_PRELIM
        let (Ar, Br, Cr) = &self.perm_prelim_inst_evals;
        Ar.append_to_transcript(b"Ar_claim", &mut transcript3);
        Br.append_to_transcript(b"Br_claim", &mut transcript3);
        Cr.append_to_transcript(b"Cr_claim", &mut transcript3);
        let [rp, _, rx, ry] = perm_prelim_challenges;
        self.perm_prelim_r1cs_eval_proof.verify(
          &perm_prelim_comm.comm,
          &[rp, rx].concat(),
          &ry,
          &self.perm_prelim_inst_evals,
          &perm_prelim_gens.gens_r1cs_eval,
          &mut transcript3,
        ).unwrap();
        timer_eval_proof.stop();
      });

      // --
      // PERM_BLOCK_ROOT
      // --
      s.spawn(move || {
        let timer_sat_proof = Timer::new("Perm Block Root Sat");
        let perm_block_root_challenges = self.perm_block_root_r1cs_sat_proof.verify(
          block_num_instances,
          block_max_num_proofs,
          &block_num_proofs,
          num_ios,
          4,
          vec![&perm_w0_verifier, &block_inputs_verifier, &perm_block_w2_verifier, &perm_block_w3_verifier],
          perm_root_num_cons,
          &vars_gens,
          &self.perm_block_root_inst_evals,
          &mut transcript4,
        ).unwrap();
        timer_sat_proof.stop();

        let timer_eval_proof = Timer::new("Perm Block Root Eval");
        // Verify Evaluation on PERM_BLOCK_ROOT
        let (Ar, Br, Cr) = &self.perm_block_root_inst_evals;
        Ar.append_to_transcript(b"Ar_claim", &mut transcript4);
        Br.append_to_transcript(b"Br_claim", &mut transcript4);
        Cr.append_to_transcript(b"Cr_claim", &mut transcript4);
        let [_, _, rx, ry] = perm_block_root_challenges;
        self.perm_block_root_r1cs_eval_proof.verify(
          &perm_root_comm.comm,
          &rx,
          &ry,
          &self.perm_block_root_inst_evals,
          &perm_root_gens.gens_r1cs_eval,
          &mut transcript4,
        ).unwrap();
        timer_eval_proof.stop();
      });

      // --
      // PERM_BLOCK_POLY
      // --
      let perm_block_poly_bound_tau = s.spawn(move || {
        let timer_sat_proof = Timer::new("Perm Block Poly Sat");
        let perm_block_poly_challenges = self.perm_block_poly_r1cs_sat_proof.verify_single(
          block_num_instances,
          perm_poly_num_cons_base,
          4,
          perm_size_bound,
          block_max_num_proofs,
          &block_num_proofs,
          &vars_gens,
          &self.perm_block_poly_inst_evals,
          4,
          &self.perm_block_comm_w3_list,
          &mut transcript5,
        ).unwrap();
        timer_sat_proof.stop();

        let timer_eval_proof = Timer::new("Perm Block Poly Eval");
        // Verify Evaluation on PERM_BLOCK_POLY
        let (Ar, Br, Cr) = &self.perm_block_poly_inst_evals;
        Ar.append_to_transcript(b"Ar_claim", &mut transcript5);
        Br.append_to_transcript(b"Br_claim", &mut transcript5);
        Cr.append_to_transcript(b"Cr_claim", &mut transcript5);
        let [_, rx, ry] = &perm_block_poly_challenges;
        self.perm_block_poly_r1cs_eval_proof.verify(
          &perm_poly_comm.comm,
          rx,
          ry,
          &self.perm_block_poly_inst_evals,
          &perm_poly_gens.gens_r1cs_eval,
          &mut transcript5,
        ).unwrap();
        timer_eval_proof.stop();

        // COMPUTE POLY FOR PERM_BLOCK
        let mut perm_block_poly_bound_tau = ONE;
        for p in 0..block_num_instances {
            let r_len = (block_num_proofs[p] * 4).log_2();
            self.proof_eval_perm_block_prod_list[p].verify_plain(
              &vars_gens.gens_pc,
              &mut transcript5,
              &[vec![ZERO; r_len - 2], vec![ONE; 2]].concat(),
              &self.perm_block_poly_list[p],
              &self.perm_block_comm_w3_list[p],
            ).unwrap();
            perm_block_poly_bound_tau *= self.perm_block_poly_list[p];
        }
        perm_block_poly_bound_tau
      });

      // --
      // PERM_EXEC_ROOT
      // --
      s.spawn(move || {
        let timer_sat_proof = Timer::new("Perm Exec Root Sat");
        let perm_exec_root_challenges = self.perm_exec_root_r1cs_sat_proof.verify(
          1,
          consis_num_proofs,
          &vec![consis_num_proofs],
          num_ios,
          4,
          vec![&perm_w0_verifier, &exec_inputs_verifier, &perm_exec_w2_verifier, &perm_exec_w3_verifier],
          perm_root_num_cons,
          &vars_gens,
          &self.perm_exec_root_inst_evals,
          &mut transcript6,
        ).unwrap();
        timer_sat_proof.stop();

        let timer_eval_proof = Timer::new("Perm Exec Root Eval");
        // Verify Evaluation on PERM_EXEC_ROOT
        let (Ar, Br, Cr) = &self.perm_exec_root_inst_evals;
        Ar.append_to_transcript(b"Ar_claim", &mut transcript6);
        Br.append_to_transcript(b"Br_claim", &mut transcript6);
        Cr.append_to_transcript(b"Cr_claim", &mut transcript6);
        let [_, _, rx, ry] = perm_exec_root_challenges;
        self.perm_exec_root_r1cs_eval_proof.verify(
          &perm_root_comm.comm,
          &rx,
          &ry,
          &self.perm_exec_root_inst_evals,
          &perm_root_gens.gens_r1cs_eval,
          &mut transcript6,
        ).unwrap();
        timer_eval_proof.stop();
      });

      // --
      // PERM_EXEC_POLY
      // --
      let perm_exec_poly_bound_tau = s.spawn(move || {
        let timer_sat_proof = Timer::new("Perm Exec Poly Sat");
        let perm_exec_poly_challenges = self.perm_exec_poly_r1cs_sat_proof.verify_single(
          1,
          perm_poly_num_cons_base,
          4,
          perm_size_bound,
          consis_num_proofs,
          &vec![consis_num_proofs],
          &vars_gens,
          &self.perm_exec_poly_inst_evals,
          4,
          &self.perm_exec_comm_w3,
          &mut transcript7,
        ).unwrap();
        timer_sat_proof.stop();

        let timer_eval_proof = Timer::new("Perm Exec Poly Eval");
        // Verify Evaluation on PERM_EXEC_POLY
        let (Ar, Br, Cr) = &self.perm_exec_poly_inst_evals;
        Ar.append_to_transcript(b"Ar_claim", &mut transcript7);
        Br.append_to_transcript(b"Br_claim", &mut transcript7);
        Cr.append_to_transcript(b"Cr_claim", &mut transcript7);
        let [_, rx, ry] = &perm_exec_poly_challenges;
        self.perm_exec_poly_r1cs_eval_proof.verify(
          &perm_poly_comm.comm,
          rx,
          ry,
          &self.perm_exec_poly_inst_evals,
          &perm_poly_gens.gens_r1cs_eval,
          &mut transcript7,
        ).unwrap();
        timer_eval_proof.stop();

        // COMPUTE POLY FOR PERM_EXEC
        let r_len = (consis_num_proofs * 4).log_2();
        self.proof_eval_perm_exec_prod.verify_plain(
          &vars_gens.gens_pc,
          &mut transcript7,
          &[vec![ZERO; r_len - 2], vec![ONE; 2]].concat(),
          &self.perm_exec_poly,
          &self.perm_exec_comm_w3[0],
        ).unwrap();
        self.perm_exec_poly
      });

      // --
      // MEM_BLOCK and MEM_ADDR
      // --
      if total_num_mem_accesses_bound > 0 {
        let mem_block_proofs = self.mem_block_proofs.as_ref().unwrap();

        // --
        // MEM_EXTRACT
        // --
        s.spawn(move || {
          let timer_sat_proof = Timer::new("Mem Extract Sat");
          let mem_extract_challenges = mem_block_proofs.mem_extract_r1cs_sat_proof.verify(
            block_num_instances,
            block_max_num_proofs,
            &block_num_proofs,
            addr_block_w3_size,
            4,
            vec![&mem_w0_verifier, &mem_block_mask_verifier, &block_vars_verifier, &mem_block_w3_verifier],
            mem_extract_num_cons,
            &vars_gens,
            &mem_block_proofs.mem_extract_inst_evals,
            &mut transcript8,
          ).unwrap();
          timer_sat_proof.stop();

          let timer_eval_proof = Timer::new("Mem Extract Eval");
          // Verify Evaluation on PERM_BLOCK_ROOT
          let (Ar, Br, Cr) = &mem_block_proofs.mem_extract_inst_evals;
          Ar.append_to_transcript(b"Ar_claim", &mut transcript8);
          Br.append_to_transcript(b"Br_claim", &mut transcript8);
          Cr.append_to_transcript(b"Cr_claim", &mut transcript8);
          let [_, _, rx, ry] = mem_extract_challenges;
          mem_block_proofs.mem_extract_r1cs_eval_proof.verify(
            &mem_extract_comm.comm,
            &rx,
            &ry,
            &mem_block_proofs.mem_extract_inst_evals,
            &mem_extract_gens.gens_r1cs_eval,
            &mut transcript8,
          ).unwrap();
          timer_eval_proof.stop();
        });

        // --
        // MEM_BLOCK_POLY
        // --
        let mem_block_poly_bound_tau = s.spawn(move || {
          let timer_sat_proof = Timer::new("Mem Block Poly Sat");
          let mem_block_poly_challenges = mem_block_proofs.mem_block_poly_r1cs_sat_proof.verify_single(
            block_num_instances,
            perm_poly_num_cons_base,
            4,
            perm_size_bound,
            block_max_num_proofs,
            &block_num_proofs,
            &vars_gens,
            &mem_block_proofs.mem_block_poly_inst_evals,
            addr_block_w3_size,
            &self.mem_block_comm_w3_list,
            &mut transcript9,
          ).unwrap();
          timer_sat_proof.stop();

          let timer_eval_proof = Timer::new("Mem Block Poly Eval");
          // Verify Evaluation on MEM_BLOCK_POLY
          let (Ar, Br, Cr) = &mem_block_proofs.mem_block_poly_inst_evals;
          Ar.append_to_transcript(b"Ar_claim", &mut transcript9);
          Br.append_to_transcript(b"Br_claim", &mut transcript9);
          Cr.append_to_transcript(b"Cr_claim", &mut transcript9);
          let [_, rx, ry] = &mem_block_poly_challenges;
          mem_block_proofs.mem_block_poly_r1cs_eval_proof.verify(
            &perm_poly_comm.comm,
            rx,
            ry,
            &mem_block_proofs.mem_block_poly_inst_evals,
            &perm_poly_gens.gens_r1cs_eval,
            &mut transcript9,
          ).unwrap();
          timer_eval_proof.stop();

          // COMPUTE POLY FOR MEM_BLOCK
          let mut mem_block_poly_bound_tau = ONE;
          for p in 0..block_num_instances {
            let r_len = (block_num_proofs[p] * addr_block_w3_size).log_2();
            mem_block_proofs.proof_eval_mem_block_prod_list[p].verify_plain(
              &vars_gens.gens_pc,
              &mut transcript9,
              &[vec![ZERO; r_len - 2], vec![ONE; 2]].concat(),
              &mem_block_proofs.mem_block_poly_list[p],
              &self.mem_block_comm_w3_list[p],
            ).unwrap();
            mem_block_poly_bound_tau *= mem_block_proofs.mem_block_poly_list[p];
          }
          mem_block_poly_bound_tau
        });

        // --
        // MEM_ADDR
        // --
        let mem_addr_poly_bound_tau = {
          if total_num_mem_accesses > 0 {
            let mem_addr_proofs = self.mem_addr_proofs.as_ref().unwrap();

            // --
            // MEM_COHERE
            // --
            s.spawn(move || {
              let timer_sat_proof = Timer::new("Mem Cohere Sat");
              let mem_cohere_challenges = mem_addr_proofs.mem_cohere_r1cs_sat_proof.verify_single(
                1,
                mem_cohere_num_cons_base,
                4,
                total_num_mem_accesses_bound,
                total_num_mem_accesses,
                &vec![total_num_mem_accesses],
                &vars_gens,
                &mem_addr_proofs.mem_cohere_inst_evals,
                4,
                &self.addr_comm_mems,
                &mut transcript10,
              ).unwrap();
              timer_sat_proof.stop();

              let timer_eval_proof = Timer::new("Mem Cohere Eval");
              // Verify Evaluation on MEM_COHERE
              let (Ar, Br, Cr) = &mem_addr_proofs.mem_cohere_inst_evals;
              Ar.append_to_transcript(b"Ar_claim", &mut transcript10);
              Br.append_to_transcript(b"Br_claim", &mut transcript10);
              Cr.append_to_transcript(b"Cr_claim", &mut transcript10);
              let [_, rx, ry] = &mem_cohere_challenges;
              mem_addr_proofs.mem_cohere_r1cs_eval_proof.verify(
                &mem_cohere_comm.comm,
                rx,
                ry,
                &mem_addr_proofs.mem_cohere_inst_evals,
                &mem_cohere_gens.gens_r1cs_eval,
                &mut transcript10,
              ).unwrap();
              timer_eval_proof.stop();
            });

            // --
            // MEM_ADDR_COMB
            // --
            s.spawn(move || {
              let timer_sat_proof = Timer::new("Mem Addr Comb Sat");
              let mem_addr_comb_challenges = mem_addr_proofs.mem_addr_comb_r1cs_sat_proof.verify(
                1,
                total_num_mem_accesses,
                &vec![total_num_mem_accesses],
                4,
                4,
                vec![&mem_w0_verifier, &mem_addr_w1_verifier, &addr_mems_verifier, &mem_addr_w3_verifier],
                mem_addr_comb_num_cons,
                &vars_gens,
                &mem_addr_proofs.mem_addr_comb_inst_evals,
                &mut transcript11,
              ).unwrap();
              // Proof that first two entries of mem_w0 are tau and r
              let ry_len = 2;
              mem_addr_proofs.proof_eval_mem_w0_at_zero.verify_plain(
                &vars_gens.gens_pc,
                &mut transcript11,
                &vec![ZERO; ry_len],
                &comb_tau,
                &self.mem_comm_w0[0],
              ).unwrap();
              mem_addr_proofs.proof_eval_mem_w0_at_one.verify_plain(
                &vars_gens.gens_pc,
                &mut transcript11,
                &[vec![ZERO; ry_len - 1], vec![ONE]].concat(),
                &comb_r,
                &self.mem_comm_w0[0],
              ).unwrap();
              timer_sat_proof.stop();

              let timer_eval_proof = Timer::new("Mem Addr Comb Eval");
              // Verify Evaluation on PERM_EXEC_ROOT
              let (Ar, Br, Cr) = &mem_addr_proofs.mem_addr_comb_inst_evals;
              Ar.append_to_transcript(b"Ar_claim", &mut transcript11);
              Br.append_to_transcript(b"Br_claim", &mut transcript11);
              Cr.append_to_transcript(b"Cr_claim", &mut transcript11);
              let [_, _, rx, ry] = mem_addr_comb_challenges;
              mem_addr_proofs.mem_addr_comb_r1cs_eval_proof.verify(
                &mem_addr_comb_comm.comm,
                &rx,
                &ry,
                &mem_addr_proofs.mem_addr_comb_inst_evals,
                &mem_addr_comb_gens.gens_r1cs_eval,
                &mut transcript11,
              ).unwrap();
              timer_eval_proof.stop();
            });

            // --
            // MEM_ADDR_POLY
            // --
            let mem_addr_poly_bound_tau = s.spawn(move || {
              let timer_sat_proof = Timer::new("Mem Addr Poly Sat");
              let mem_addr_poly_challenges = mem_addr_proofs.mem_addr_poly_r1cs_sat_proof.verify_single(
                1,
                perm_poly_num_cons_base,
                4,
                perm_size_bound,
                total_num_mem_accesses,
                &vec![total_num_mem_accesses],
                &vars_gens,
                &mem_addr_proofs.mem_addr_poly_inst_evals,
                4,
                &self.mem_addr_comm_w1,
                &mut transcript12,
              ).unwrap();
              timer_sat_proof.stop();

              let timer_eval_proof = Timer::new("Mem Addr Poly Eval");
              // Verify Evaluation on PERM_EXEC_POLY
              let (Ar, Br, Cr) = &mem_addr_proofs.mem_addr_poly_inst_evals;
              Ar.append_to_transcript(b"Ar_claim", &mut transcript12);
              Br.append_to_transcript(b"Br_claim", &mut transcript12);
              Cr.append_to_transcript(b"Cr_claim", &mut transcript12);
              let [_, rx, ry] = &mem_addr_poly_challenges;
              mem_addr_proofs.mem_addr_poly_r1cs_eval_proof.verify(
                &perm_poly_comm.comm,
                rx,
                ry,
                &mem_addr_proofs.mem_addr_poly_inst_evals,
                &perm_poly_gens.gens_r1cs_eval,
                &mut transcript12,
              ).unwrap();
              timer_eval_proof.stop();

              // COMPUTE POLY FOR PERM_EXEC
              let r_len = (total_num_mem_accesses * 4).log_2();
              mem_addr_proofs.proof_eval_mem_addr_prod.verify_plain(
                &vars_gens.gens_pc,
                &mut transcript12,
                &[vec![ZERO; r_len - 2], vec![ONE; 2]].concat(),
                &mem_addr_proofs.mem_addr_poly,
                &self.mem_addr_comm_w1[0],
              ).unwrap();
              mem_addr_proofs.mem_addr_poly
            });

            mem_addr_poly_bound_tau.join().unwrap()
          } else {
            ONE
          }
        };

        // --
        // ASSERT_CORRECTNESS_OF_MEMORY
        // --
        let mem_block_poly_bound_tau = mem_block_poly_bound_tau.join().unwrap();
        assert_eq!(mem_block_poly_bound_tau, mem_addr_poly_bound_tau);
      }


      // --
      // ASSERT_CORRECTNESS_OF_PERMUTATION
      // --
      let perm_block_poly_bound_tau = perm_block_poly_bound_tau.join().unwrap();
      let perm_exec_poly_bound_tau = perm_exec_poly_bound_tau.join().unwrap();
      assert_eq!(perm_block_poly_bound_tau, perm_exec_poly_bound_tau);

    });

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
      func_input_width,
      input_offset,
      output_offset,
      input,
      output,
      output_exec_num,
      &vars_gens,
      &mut transcript.clone()
    )?;
    timer_proof.stop();

    timer_verify.stop();
    Ok(())
  }
  */

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
    A.push((0, num_vars + 2, ONE.to_bytes())); // 1*a
    B.push((0, num_vars + 2, ONE.to_bytes())); // 1*a
    C.push((0, num_vars + 1, ONE.to_bytes())); // 1*z
    C.push((0, num_vars, (-Scalar::from(13u64)).to_bytes())); // -13*1
    C.push((0, num_vars + 3, (-ONE).to_bytes())); // -1*b

    // Var Assignments (Z_0 = 16 is the only output)
    let vars = vec![ZERO.to_bytes(); num_vars];

    // create an InputsAssignment (a = 1, b = 2)
    let mut inputs = vec![ZERO.to_bytes(); num_inputs];
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
