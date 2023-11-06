#![allow(non_snake_case)]
#![doc = include_str!("../README.md")]
#![deny(missing_docs)]
#![allow(clippy::assertions_on_result_states)]

// TODO: Proof might be incorrect if a block is never executed
// TODO: Differentiate between max_num_proofs and max_num_proofs_bound
// TODO: The verifier needs to check the first block and last block number are correct
// Q: Would it be insecure if an entry has valid = 0 but everything else not 0?
// Q: What should we do with the constant bit if the entry is invalid?
// Q: Can we trust that the Prover orders all valid = 1 before valid = 0?

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

use core::cmp::max;
use curve25519_dalek::ristretto::CompressedRistretto;
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

/// `ComputationCommitment` holds a public preprocessed NP statement (e.g., R1CS)
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

  /// pads Assignment to the specified length
  fn pad(&self, len: usize) -> VarsAssignment {
    // check that the new length is higher than current length
    assert!(len > self.assignment.len());

    let padded_assignment = {
      let mut padded_assignment = self.assignment.clone();
      padded_assignment.extend(vec![Scalar::zero(); len - self.assignment.len()]);
      padded_assignment
    };

    VarsAssignment {
      assignment: padded_assignment,
    }
  }
}

/// `VarsAssignment` holds an assignment of values to variables in an `Instance`
pub type VarsAssignment = Assignment;

/// `InputsAssignment` holds an assignment of values to variables in an `Instance`
pub type InputsAssignment = Assignment;

/// `Instance` holds the description of R1CS matrices and a hash of the matrices
pub struct Instance {
  inst: R1CSInstance,
  digest: Vec<u8>,
}

impl Instance {
  /// Constructs a new `Instance` and an associated satisfying assignment
  pub fn new(
    num_instances: usize,
    num_cons: usize,
    num_vars: usize,
    A: &Vec<Vec<(usize, usize, [u8; 32])>>,
    B: &Vec<Vec<(usize, usize, [u8; 32])>>,
    C: &Vec<Vec<(usize, usize, [u8; 32])>>,
  ) -> Result<Instance, R1CSError> {
    let num_instances_padded = num_instances.next_power_of_two();
    let (num_vars_padded, num_cons_padded) = {
      let num_vars_padded = {
        let mut num_vars_padded = num_vars;

        // ensure that num_vars_padded a power of two
        if num_vars_padded.next_power_of_two() != num_vars_padded {
          num_vars_padded = num_vars_padded.next_power_of_two();
        }
        num_vars_padded
      };

      let num_cons_padded = {
        let mut num_cons_padded = num_cons;

        // ensure that num_cons_padded is at least 2
        if num_cons_padded == 0 || num_cons_padded == 1 {
          num_cons_padded = 2;
        }

        // ensure that num_cons_padded is power of 2
        if num_cons.next_power_of_two() != num_cons {
          num_cons_padded = num_cons.next_power_of_two();
        }
        num_cons_padded
      };

      (num_vars_padded, num_cons_padded)
    };

    let bytes_to_scalar =
      |tups: &[(usize, usize, [u8; 32])]| -> Result<Vec<(usize, usize, Scalar)>, R1CSError> {
        let mut mat: Vec<(usize, usize, Scalar)> = Vec::new();
        for &(row, col, val_bytes) in tups {
          // row must be smaller than num_cons
          if row >= num_cons {
            println!("ROW: {}, NUM_CONS: {}", row, num_cons);
            return Err(R1CSError::InvalidIndex);
          }

          // col must be smaller than num_vars
          if col >= num_vars {
            println!("COL: {}, NUM_VARS: {}", col, num_vars);
            return Err(R1CSError::InvalidIndex);
          }

          let val = Scalar::from_bytes(&val_bytes);
          if val.is_some().unwrap_u8() == 1 {
            // if col >= num_vars, it means that it is referencing a 1 or input in the satisfying
            // assignment
            if col >= num_vars {
              mat.push((row, col + num_vars_padded - num_vars, val.unwrap()));
            } else {
              mat.push((row, col, val.unwrap()));
            }
          } else {
            return Err(R1CSError::InvalidScalar);
          }
        }

        // pad with additional constraints up until num_cons_padded if the original constraints were 0 or 1
        // we do not need to pad otherwise because the dummy constraints are implicit in the sum-check protocol
        if num_cons == 0 || num_cons == 1 {
          for i in tups.len()..num_cons_padded {
            mat.push((i, num_vars, Scalar::zero()));
          }
        }

        Ok(mat)
      };

    let mut A_scalar_list = Vec::new();
    let mut B_scalar_list = Vec::new();
    let mut C_scalar_list = Vec::new();

    for i in 0..num_instances {
      let A_scalar = bytes_to_scalar(&A[i]);
      if A_scalar.is_err() {
        return Err(A_scalar.err().unwrap());
      }
      A_scalar_list.push(A_scalar.unwrap());

      let B_scalar = bytes_to_scalar(&B[i]);
      if B_scalar.is_err() {
        return Err(B_scalar.err().unwrap());
      }
      B_scalar_list.push(B_scalar.unwrap());

      let C_scalar = bytes_to_scalar(&C[i]);
      if C_scalar.is_err() {
        return Err(C_scalar.err().unwrap());
      }
      C_scalar_list.push(C_scalar.unwrap());
    }

    let inst = R1CSInstance::new(
      num_instances_padded,
      num_cons_padded,
      num_vars_padded,
      &A_scalar_list,
      &B_scalar_list,
      &C_scalar_list,
    );

    let digest = inst.get_digest();

    Ok(Instance { inst, digest })
  }

  /*
  /// Checks if a given R1CSInstance is satisfiable with a given variables and inputs assignments
  pub fn is_sat(
    &self,
    vars: &VarsAssignment,
    inputs: &InputsAssignment,
  ) -> Result<bool, R1CSError> {
    if vars.assignment.len() > self.inst.get_num_vars() {
      return Err(R1CSError::InvalidNumberOfInputs);
    }

    if inputs.assignment.len() != self.inst.get_num_inputs() {
      return Err(R1CSError::InvalidNumberOfInputs);
    }

    // we might need to pad variables
    let padded_vars = {
      let num_padded_vars = self.inst.get_num_vars();
      let num_vars = vars.assignment.len();
      if num_padded_vars > num_vars {
        vars.pad(num_padded_vars)
      } else {
        vars.clone()
      }
    };

    Ok(
      self
        .inst
        .is_sat(&padded_vars.assignment, &inputs.assignment),
    )
  }
  */

  /*
  /// Constructs a new synthetic R1CS `Instance` and an associated satisfying assignment
  pub fn produce_synthetic_r1cs(
    num_cons: usize,
    num_vars: usize,
    num_inputs: usize,
  ) -> (Instance, VarsAssignment, InputsAssignment) {
    let (inst, vars, inputs) = R1CSInstance::produce_synthetic_r1cs(num_cons, num_vars, num_inputs);
    let digest = inst.get_digest();
    (
      Instance { inst, digest },
      VarsAssignment { assignment: vars },
      InputsAssignment { assignment: inputs },
    )
  }
  */
}

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

/// `SNARK` holds a proof produced by Spartan SNARK
#[derive(Serialize, Deserialize, Debug)]
pub struct SNARK {
  block_comm_vars_list: Vec<PolyCommitment>,
  block_comm_inputs_list: Vec<PolyCommitment>,
  exec_comm_inputs: PolyCommitment,
  perm_comm_w0: PolyCommitment,
  perm_block_comm_w2_list: Vec<PolyCommitment>,
  perm_block_comm_w3_list: Vec<PolyCommitment>,
  perm_block_comm_w3_concat: PolyCommitment,
  perm_exec_comm_w2: PolyCommitment,
  perm_exec_comm_w3: PolyCommitment,
  perm_exec_comm_w3_concat: PolyCommitment,
  consis_comm_w2: PolyCommitment,
  consis_comm_w3: PolyCommitment,

  block_r1cs_sat_proof: R1CSProof,
  block_inst_evals: (Scalar, Scalar, Scalar),
  block_r1cs_eval_proof: R1CSEvalProof,

  consis_comb_r1cs_sat_proof: R1CSProof,
  consis_comb_inst_evals: (Scalar, Scalar, Scalar),
  consis_comb_r1cs_eval_proof: R1CSEvalProof,

  perm_prelim_r1cs_sat_proof: R1CSProof,
  perm_prelim_inst_evals: (Scalar, Scalar, Scalar),
  perm_prelim_r1cs_eval_proof: R1CSEvalProof,
  proof_eval_perm_w0_at_zero: PolyEvalProof,
  proof_eval_perm_w0_at_one: PolyEvalProof,

  perm_block_root_r1cs_sat_proof: R1CSProof,
  perm_block_root_inst_evals: (Scalar, Scalar, Scalar),
  perm_block_root_r1cs_eval_proof: R1CSEvalProof,

  perm_block_poly_r1cs_sat_proof: R1CSProof,
  perm_block_poly_inst_evals: (Scalar, Scalar, Scalar),
  perm_block_poly_r1cs_eval_proof: R1CSEvalProof,
  perm_block_poly_list: Vec<Scalar>,
  proof_eval_perm_block_prod_list: Vec<PolyEvalProof>,
  
  perm_exec_root_r1cs_sat_proof: R1CSProof,
  perm_exec_root_inst_evals: (Scalar, Scalar, Scalar),
  perm_exec_root_r1cs_eval_proof: R1CSEvalProof,

  perm_exec_poly_r1cs_sat_proof: R1CSProof,
  perm_exec_poly_inst_evals: (Scalar, Scalar, Scalar),
  perm_exec_poly_r1cs_eval_proof: R1CSEvalProof,
  perm_exec_poly: Scalar,
  proof_eval_perm_exec_prod: PolyEvalProof,
}

impl SNARK {
  fn protocol_name() -> &'static [u8] {
    b"Spartan SNARK proof"
  }

  /// A public computation to create a commitment to an R1CS instance
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
    num_vars: usize,
    input_output_cutoff: usize,
    total_num_proofs_bound: usize,

    block_num_instances: usize,
    block_max_num_proofs_bound: usize,
    block_max_num_proofs: usize,
    block_num_proofs: &Vec<usize>,
    block_inst: &Instance,
    block_comm: &ComputationCommitment,
    block_decomm: &ComputationDecommitment,
    block_gens: &SNARKGens,

    consis_num_proofs: usize,
    consis_comb_inst: &Instance,
    consis_comb_comm: &ComputationCommitment,
    consis_comb_decomm: &ComputationDecommitment,
    consis_comb_gens: &SNARKGens,

    perm_prelim_inst: &Instance,
    perm_prelim_comm: &ComputationCommitment,
    perm_prelim_decomm: &ComputationDecommitment,
    perm_prelim_gens: &SNARKGens,

    perm_root_inst: &Instance,
    perm_root_comm: &ComputationCommitment,
    perm_root_decomm: &ComputationDecommitment,
    perm_root_gens: &SNARKGens,

    perm_block_poly_inst: &Instance,
    perm_block_poly_comm: &ComputationCommitment,
    perm_block_poly_decomm: &ComputationDecommitment,
    perm_block_poly_gens: &SNARKGens,

    perm_exec_poly_inst: &Instance,
    perm_exec_poly_comm: &ComputationCommitment,
    perm_exec_poly_decomm: &ComputationDecommitment,
    perm_exec_poly_gens: &SNARKGens,

    block_vars_mat: Vec<Vec<VarsAssignment>>,
    block_inputs_mat: Vec<Vec<InputsAssignment>>,
    exec_inputs_list: Vec<InputsAssignment>,
    vars_gens: &R1CSGens,
    proofs_times_vars_gens: &R1CSGens,
    total_proofs_times_vars_gens: &R1CSGens,

    transcript: &mut Transcript,
  ) -> Self {
    let timer_prove = Timer::new("SNARK::prove");

    // we create a Transcript object seeded with a random Scalar
    // to aid the prover produce its randomness
    let mut random_tape = RandomTape::new(b"proof");

    transcript.append_protocol_name(SNARK::protocol_name());
    block_comm.comm.append_to_transcript(b"block_comm", transcript);
    perm_prelim_comm.comm.append_to_transcript(b"block_comm", transcript);
    perm_root_comm.comm.append_to_transcript(b"block_comm", transcript);
    perm_block_poly_comm.comm.append_to_transcript(b"block_comm", transcript);
    consis_comb_comm.comm.append_to_transcript(b"consis_comm", transcript);
    perm_exec_poly_comm.comm.append_to_transcript(b"block_comm", transcript);

    // unwrap the assignments
    let block_vars_mat = block_vars_mat.into_iter().map(|a| a.into_iter().map(|v| v.assignment).collect_vec()).collect_vec();
    let block_inputs_mat = block_inputs_mat.into_iter().map(|a| a.into_iter().map(|v| v.assignment).collect_vec()).collect_vec();
    let exec_inputs_list = exec_inputs_list.into_iter().map(|v| v.assignment).collect_vec();

    // --
    // COMMITMENTS
    // --

    // Commit num_proofs
    let timer_commit = Timer::new("metacommit");
    let block_max_num_proofs_64: u64 = block_max_num_proofs.try_into().unwrap();
    Scalar::from(block_max_num_proofs_64).append_to_transcript(b"block_max_num_proofs", transcript);
    for n in block_num_proofs {
      let n_64: u64 = (*n).try_into().unwrap();
      Scalar::from(n_64).append_to_transcript(b"block_num_proofs", transcript);
    }
    timer_commit.stop();

    // Commit witnesses
    let (
      block_poly_vars_list,
      block_comm_vars_list,
      block_poly_inputs_list,
      block_comm_inputs_list,
      exec_poly_inputs, 
      exec_comm_inputs
    ) = {
      let timer_commit = Timer::new("polycommit");

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
      timer_commit.stop();

      (
        block_poly_vars_list,
        block_comm_vars_list,
        block_poly_inputs_list,
        block_comm_inputs_list,
        exec_poly_inputs, 
        exec_comm_inputs
      )
    };
    
    // --
    // CHALLENGES AND WITNESSES FOR PERMUTATION
    // --

    let (
      comb_tau,
      comb_r,
      perm_w0,
      perm_poly_w0,
      perm_comm_w0,

      perm_block_w2,
      perm_block_poly_w2_list,
      perm_block_comm_w2_list,
      perm_block_w3,
      perm_block_poly_w3_list,
      perm_block_comm_w3_list,
      perm_block_w3_concat,
      perm_block_poly_w3_concat,
      perm_block_comm_w3_concat,

      perm_exec_w2,
      perm_exec_poly_w2,
      perm_exec_comm_w2,
      perm_exec_w3,
      perm_exec_poly_w3,
      perm_exec_comm_w3,
      perm_exec_w3_concat,
      perm_exec_poly_w3_concat,
      perm_exec_comm_w3_concat,

      consis_w2,
      consis_poly_w2,
      consis_comm_w2,
      consis_w3,
      consis_poly_w3,
      consis_comm_w3,
    ) = {
      let comb_tau = transcript.challenge_scalar(b"challenge_tau");
      let comb_r = transcript.challenge_scalar(b"challenge_r");
      
      // w0 is (tau, r, r^2, ...)
      // set the first entry to 1 for multiplication and later revert it to tau
      let mut perm_w0 = Vec::new();
      perm_w0.push(Scalar::one());
      let mut r_tmp = comb_r;
      for _ in 1..num_vars {
        perm_w0.push(r_tmp);
        r_tmp *= comb_r;
      }
      
      // FOR PERM
      // w2 is block_inputs * <r>
      let perm_block_w2: Vec<Vec<Vec<Scalar>>> = block_inputs_mat.iter().map(
        |i| i.iter().map(
          |input| (0..input.len()).map(|j| perm_w0[j] * input[j]).collect()
        ).collect()
      ).collect();
      let perm_exec_w2: Vec<Vec<Scalar>> = exec_inputs_list.iter().map(
        |input| (0..input.len()).map(|j| perm_w0[j] * input[j]).collect()
      ).collect();
      perm_w0[0] = comb_tau;
      
      // w3 is [valid, tau - Xi, 1, ...]
      // See accumulator.rs
      let mut perm_block_w3: Vec<Vec<Vec<Scalar>>> = Vec::new();
      for p in 0..block_num_instances {
        perm_block_w3.push(vec![Vec::new(); block_num_proofs[p]]);
        for q in (0..block_num_proofs[p]).rev() {
          perm_block_w3[p][q] = vec![Scalar::zero(); num_vars];
          perm_block_w3[p][q][0] = block_inputs_mat[p][q][0];
          perm_block_w3[p][q][1] = (comb_tau - perm_block_w2[p][q].iter().fold(Scalar::zero(), |a, b| a + b)) * block_inputs_mat[p][q][0];
          perm_block_w3[p][q][2] = Scalar::one() * block_inputs_mat[p][q][0];
          if q != block_num_proofs[p] - 1 {
            perm_block_w3[p][q][4] = perm_block_w3[p][q + 1][0] * perm_block_w3[p][q + 1][3];
            perm_block_w3[p][q][5] = perm_block_w3[p][q][1] * (perm_block_w3[p][q][4] + Scalar::one() - perm_block_w3[p][q + 1][0]);
          } else {
            perm_block_w3[p][q][5] = perm_block_w3[p][q][1];
          }
          perm_block_w3[p][q][3] = perm_block_w3[p][q][0] * perm_block_w3[p][q][5];
        }
      }
      let mut perm_exec_w3 = vec![Vec::new(); consis_num_proofs];
      for q in (0..consis_num_proofs).rev() {
        perm_exec_w3[q] = vec![Scalar::zero(); num_vars];
        perm_exec_w3[q][0] = exec_inputs_list[q][0];
        perm_exec_w3[q][1] = (comb_tau - perm_exec_w2[q].iter().fold(Scalar::zero(), |a, b| a + b)) * exec_inputs_list[q][0];
        perm_exec_w3[q][2] = Scalar::one() * exec_inputs_list[q][0];
        if q != consis_num_proofs - 1 {
          perm_exec_w3[q][4] = perm_exec_w3[q + 1][0] * perm_exec_w3[q + 1][3];
          perm_exec_w3[q][5] = perm_exec_w3[q][1] * (perm_exec_w3[q][4] + Scalar::one() - perm_exec_w3[q + 1][0]);
        } else {
          perm_exec_w3[q][5] = perm_exec_w3[q][1];
        }
        perm_exec_w3[q][3] = perm_exec_w3[q][0] * perm_exec_w3[q][5];
      }
      
      // perm_block_w0 is perm_w0 copied num_proofs times
      let mut perm_block_w0 = Vec::new();
      for p in 0..block_num_instances {
        perm_block_w0.push(Vec::new());
        for _ in 0..block_num_proofs[p] {
          perm_block_w0[p].push(perm_w0.clone());
        }
      }
      let mut perm_exec_w0 = Vec::new();
      for _ in 0..consis_num_proofs {
        perm_exec_w0.push(perm_w0.clone());
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

      // Concat everything within the same instance in perm_block_w3 into the same vector
      // TODO: We shouldn't need length-block_max_num_proofs_bound!!
      let mut perm_block_w3_concat = Vec::new();
      for p in 0..block_num_instances {
        perm_block_w3_concat.push(perm_block_w3[p].iter().fold(Vec::new(), |a, b| [a, b.clone()].concat()));
        perm_block_w3_concat[p].extend(vec![Scalar::zero(); (block_max_num_proofs_bound - perm_block_w3[p].len()) * num_vars]);
      }
      let w3_concat_list_p = perm_block_w3_concat.iter().fold(Vec::new(), |a, b| [a, b.to_vec()].concat());
      let perm_block_poly_w3_concat = DensePolynomial::new(w3_concat_list_p);
      let (perm_block_comm_w3_concat, _blinds_vars) = perm_block_poly_w3_concat.commit(&proofs_times_vars_gens.gens_pc, None);
      perm_block_comm_w3_concat.append_to_transcript(b"poly_commitment", transcript);

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
          let perm_exec_poly_w3 = DensePolynomial::new(w3_list_p.clone());

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

      // Concat everything within the same instance in perm_exec_w3 into the same vector
      // TODO: We shouldn't need length-total_num_proofs_bound!!
      let mut perm_exec_w3_concat = perm_exec_w3.iter().fold(Vec::new(), |a, b| [a, b.clone()].concat());
      perm_exec_w3_concat.extend(vec![Scalar::zero(); (total_num_proofs_bound - perm_exec_w3.len()) * num_vars]);
      let perm_exec_poly_w3_concat = DensePolynomial::new(perm_exec_w3_concat.clone());
      let (perm_exec_comm_w3_concat, _blinds_vars) = perm_exec_poly_w3_concat.commit(&total_proofs_times_vars_gens.gens_pc, None);
      perm_exec_comm_w3_concat.append_to_transcript(b"poly_commitment", transcript);

      // FOR CONSIS
      // w2 is <0, i0 * r, i1 * r^2, ..., 0, o0 * r, o1 * r^2, ...>
      // w3 is <v, v * (cnst + i0 * r + i1 * r^2 + i2 * r^3 + ...), v * (cnst + o0 * r + o1 * r^2 + o2 * r^3 + ...), 0, 0, ...>
      let mut consis_w2 = Vec::new();
      let mut consis_w3 = Vec::new();
      for q in 0..consis_num_proofs {
        consis_w2.push(vec![Scalar::zero(); num_vars]);
        consis_w3.push(vec![Scalar::zero(); num_vars]);
        
        consis_w3[q][1] = exec_inputs_list[q][input_output_cutoff];
        consis_w3[q][2] = exec_inputs_list[q][input_output_cutoff];
        for i in 1..input_output_cutoff {
          consis_w2[q][i] = perm_w0[i] * exec_inputs_list[q][i];
          consis_w2[q][input_output_cutoff + i] = perm_w0[i] * exec_inputs_list[q][input_output_cutoff + i];
          consis_w3[q][1] += consis_w2[q][i];
          consis_w3[q][2] += consis_w2[q][input_output_cutoff + i];
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
        let consis_poly_w3 = DensePolynomial::new(w3_list_p.clone());

        // produce a commitment to the satisfying assignment
        let (consis_comm_w3, _blinds_vars) = consis_poly_w3.commit(&vars_gens.gens_pc, None);

        // add the commitment to the prover's transcript
        consis_comm_w3.append_to_transcript(b"poly_commitment", transcript);
        (consis_poly_w3, consis_comm_w3)
      };

      (
        comb_tau,
        comb_r,

        perm_w0,
        perm_poly_w0,
        perm_comm_w0,
        perm_block_w2,
        perm_block_poly_w2_list,
        perm_block_comm_w2_list,
        perm_block_w3,
        perm_block_poly_w3_list,
        perm_block_comm_w3_list,
        perm_block_w3_concat,
        perm_block_poly_w3_concat,
        perm_block_comm_w3_concat,

        perm_exec_w2,
        perm_exec_poly_w2,
        perm_exec_comm_w2,
        perm_exec_w3,
        perm_exec_poly_w3,
        perm_exec_comm_w3,
        perm_exec_w3_concat,
        perm_exec_poly_w3_concat,
        perm_exec_comm_w3_concat,

        consis_w2,
        consis_poly_w2,
        consis_comm_w2,
        consis_w3,
        consis_poly_w3,
        consis_comm_w3,
      )
    };

    // --
    // BLOCK CORRECTNESS
    // --

    let (block_r1cs_sat_proof, block_challenges) = {
      let (proof, block_challenges) = {
        R1CSProof::prove(
          2,
          0,
          block_num_instances,
          block_max_num_proofs,
          block_num_proofs,
          num_vars,
          &block_inst.inst,
          &vars_gens,
          vec![&block_vars_mat, &block_inputs_mat],
          vec![&block_poly_vars_list, &block_poly_inputs_list],
          transcript,
          &mut random_tape,
        )
      };

      let proof_encoded: Vec<u8> = bincode::serialize(&proof).unwrap();
      Timer::print(&format!("len_r1cs_sat_proof {:?}", proof_encoded.len()));

      (proof, block_challenges)
    };

    // Final evaluation on BLOCK
    let (block_inst_evals, block_r1cs_eval_proof) = {
      let [rp, _, rx, ry] = block_challenges;
      let inst = block_inst;
      let timer_eval = Timer::new("eval_sparse_polys");
      let inst_evals = {
        let (Ar, Br, Cr) = inst.inst.evaluate(&rp, &rx, &ry);
        Ar.append_to_transcript(b"Ar_claim", transcript);
        Br.append_to_transcript(b"Br_claim", transcript);
        Cr.append_to_transcript(b"Cr_claim", transcript);
        (Ar, Br, Cr)
      };
      timer_eval.stop();

      let r1cs_eval_proof = {
        let proof = R1CSEvalProof::prove(
          &block_decomm.decomm,
          &[rp, rx].concat(),
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

      timer_prove.stop();
      (inst_evals, r1cs_eval_proof)
    };

    // --
    // CONSIS_COMB
    // --

    let (consis_comb_r1cs_sat_proof, consis_comb_challenges) = {
      let (proof, consis_comb_challenges) = {
        R1CSProof::prove(
          4,
          1,
          1,
          consis_num_proofs,
          &vec![consis_num_proofs],
          num_vars,
          &consis_comb_inst.inst,
          &vars_gens,
          vec![&vec![vec![perm_w0.clone()]], &vec![exec_inputs_list.clone()], &vec![consis_w2], &vec![consis_w3]],
          vec![&vec![perm_poly_w0.clone()], &vec![exec_poly_inputs.clone()], &vec![consis_poly_w2], &vec![consis_poly_w3]],
          transcript,
          &mut random_tape,
        )
      };

      let proof_encoded: Vec<u8> = bincode::serialize(&proof).unwrap();
      Timer::print(&format!("len_r1cs_sat_proof {:?}", proof_encoded.len()));

      (proof, consis_comb_challenges)
    };

    // Final evaluation on PERM_BLOCK_ROOT
    let (consis_comb_inst_evals, consis_comb_r1cs_eval_proof) = {
      let [_, _, rx, ry] = consis_comb_challenges;
      let inst = consis_comb_inst;
      let timer_eval = Timer::new("eval_sparse_polys");
      let inst_evals = {
        let (Ar, Br, Cr) = inst.inst.evaluate(&Vec::new(), &rx, &ry);
        Ar.append_to_transcript(b"Ar_claim", transcript);
        Br.append_to_transcript(b"Br_claim", transcript);
        Cr.append_to_transcript(b"Cr_claim", transcript);
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
          transcript,
          &mut random_tape,
        );

        let proof_encoded: Vec<u8> = bincode::serialize(&proof).unwrap();
        Timer::print(&format!("len_r1cs_eval_proof {:?}", proof_encoded.len()));
        proof
      };

      timer_prove.stop();
      (inst_evals, r1cs_eval_proof)
    };

    // --
    // PERM_PRELIM
    // --

    let (
      perm_prelim_r1cs_sat_proof, 
      perm_prelim_challenges,
      proof_eval_perm_w0_at_zero,
      proof_eval_perm_w0_at_one
    ) = {
      let (proof, perm_prelim_challenges) = {
        R1CSProof::prove(
          1,
          0,
          1,
          1,
          &vec![1],
          num_vars,
          &perm_prelim_inst.inst,
          &vars_gens,
          vec![&vec![vec![perm_w0.clone()]]],
          vec![&vec![perm_poly_w0.clone()]],
          transcript,
          &mut random_tape,
        )
      };

      // Proof that first two entries of perm_w0 are tau and r
      let ry_len = perm_prelim_challenges[3].len();
      let (proof_eval_perm_w0_at_zero, _comm_perm_w0_at_zero) = PolyEvalProof::prove(
        &perm_poly_w0,
        None,
        &vec![Scalar::zero(); ry_len],
        &comb_tau,
        None,
        &vars_gens.gens_pc,
        transcript,
        &mut random_tape,
      );
      let (proof_eval_perm_w0_at_one, _comm_perm_w0_at_one) = PolyEvalProof::prove(
        &perm_poly_w0,
        None,
        &[vec![Scalar::zero(); ry_len - 1], vec![Scalar::one()]].concat(),
        &comb_r,
        None,
        &vars_gens.gens_pc,
        transcript,
        &mut random_tape,
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
      let inst = perm_prelim_inst;
      let timer_eval = Timer::new("eval_sparse_polys");
      let inst_evals = {
        let (Ar, Br, Cr) = inst.inst.evaluate(&rp, &rx, &ry);
        Ar.append_to_transcript(b"Ar_claim", transcript);
        Br.append_to_transcript(b"Br_claim", transcript);
        Cr.append_to_transcript(b"Cr_claim", transcript);
        (Ar, Br, Cr)
      };
      timer_eval.stop();

      let r1cs_eval_proof = {
        let proof = R1CSEvalProof::prove(
          &perm_prelim_decomm.decomm,
          &[rp, rx].concat(),
          &ry,
          &inst_evals,
          &perm_prelim_gens.gens_r1cs_eval,
          transcript,
          &mut random_tape,
        );

        let proof_encoded: Vec<u8> = bincode::serialize(&proof).unwrap();
        Timer::print(&format!("len_r1cs_eval_proof {:?}", proof_encoded.len()));
        proof
      };

      timer_prove.stop();
      (inst_evals, r1cs_eval_proof)
    };

    // --
    // PERM_BLOCK_ROOT
    // --

    let (perm_block_root_r1cs_sat_proof, perm_block_root_challenges) = {
      let (proof, perm_block_root_challenges) = {
        R1CSProof::prove(
          4,
          1,
          block_num_instances,
          block_max_num_proofs,
          block_num_proofs,
          num_vars,
          &perm_root_inst.inst,
          &vars_gens,
          vec![&vec![vec![perm_w0.clone()]], &block_inputs_mat, &perm_block_w2, &perm_block_w3],
          vec![&vec![perm_poly_w0.clone()], &block_poly_inputs_list, &perm_block_poly_w2_list, &perm_block_poly_w3_list],
          transcript,
          &mut random_tape,
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
        let (Ar, Br, Cr) = inst.inst.evaluate(&Vec::new(), &rx, &ry);
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

      timer_prove.stop();
      (inst_evals, r1cs_eval_proof)
    };

    // --
    // PERM_BLOCK_POLY
    // --

    let (perm_block_poly_r1cs_sat_proof, perm_block_poly_challenges) = {
      let (proof, perm_block_poly_challenges) = {
        R1CSProof::prove(
          1,
          0,
          1,
          block_num_instances,
          &vec![block_num_instances],
          block_max_num_proofs_bound * num_vars,
          &perm_block_poly_inst.inst,
          &proofs_times_vars_gens,
          vec![&vec![perm_block_w3_concat.clone()]],
          vec![&vec![perm_block_poly_w3_concat.clone()]],
          transcript,
          &mut random_tape,
        )
      };

      let proof_encoded: Vec<u8> = bincode::serialize(&proof).unwrap();
      Timer::print(&format!("len_r1cs_sat_proof {:?}", proof_encoded.len()));

      (proof, perm_block_poly_challenges)
    };

    // Final evaluation on PERM_BLOCK_POLY
    let (perm_block_poly_inst_evals, perm_block_poly_r1cs_eval_proof) = {
      let [rp, _, rx, ry] = perm_block_poly_challenges.clone();
      let inst = perm_block_poly_inst;
      let timer_eval = Timer::new("eval_sparse_polys");
      let inst_evals = {
        let (Ar, Br, Cr) = inst.inst.evaluate(&rp, &rx, &ry);
        Ar.append_to_transcript(b"Ar_claim", transcript);
        Br.append_to_transcript(b"Br_claim", transcript);
        Cr.append_to_transcript(b"Cr_claim", transcript);
        (Ar, Br, Cr)
      };
      timer_eval.stop();

      let r1cs_eval_proof = {
        let proof = R1CSEvalProof::prove(
          &perm_block_poly_decomm.decomm,
          &[rp, rx].concat(),
          &ry,
          &inst_evals,
          &perm_block_poly_gens.gens_r1cs_eval,
          transcript,
          &mut random_tape,
        );

        let proof_encoded: Vec<u8> = bincode::serialize(&proof).unwrap();
        Timer::print(&format!("len_r1cs_eval_proof {:?}", proof_encoded.len()));
        proof
      };

      timer_prove.stop();
      (inst_evals, r1cs_eval_proof)
    };

    // Record the prod of each instance
    let (perm_block_poly_list, proof_eval_perm_block_prod_list) = {
      let r_len = perm_block_poly_challenges[3].len();
      let mut perm_block_poly_list = Vec::new();
      let mut proof_eval_perm_block_prod_list = Vec::new();
      for p in 0..block_num_instances {
        // Convert p into binary
        let p_vec: Vec<Scalar> = (0..block_num_instances.log_2()).rev().map (|n| (p >> n) & 1).map(|i| Scalar::from(i as u64)).collect();
        // Prod is the 3rd entry
        let perm_block_poly = perm_block_w3_concat[p][3];
        let (proof_eval_perm_block_prod, _comm_perm_block_prod) = PolyEvalProof::prove(
          &perm_block_poly_w3_concat,
          None,
          &[p_vec, vec![Scalar::zero(); r_len - 2], vec![Scalar::one(); 2]].concat(),
          &perm_block_poly,
          None,
          &proofs_times_vars_gens.gens_pc,
          transcript,
          &mut random_tape,
        );
        perm_block_poly_list.push(perm_block_poly);
        proof_eval_perm_block_prod_list.push(proof_eval_perm_block_prod);
      }
      (perm_block_poly_list, proof_eval_perm_block_prod_list)
    };

    // --
    // PERM_EXEC_ROOT
    // --

    let (perm_exec_root_r1cs_sat_proof, perm_exec_root_challenges) = {
      let (proof, perm_exec_root_challenges) = {
        R1CSProof::prove(
          4,
          1,
          1,
          consis_num_proofs,
          &vec![consis_num_proofs],
          num_vars,
          &perm_root_inst.inst,
          &vars_gens,
          vec![&vec![vec![perm_w0]], &vec![exec_inputs_list], &vec![perm_exec_w2], &vec![perm_exec_w3]],
          vec![&vec![perm_poly_w0], &vec![exec_poly_inputs], &vec![perm_exec_poly_w2], &vec![perm_exec_poly_w3]],
          transcript,
          &mut random_tape,
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
        let (Ar, Br, Cr) = inst.inst.evaluate(&Vec::new(), &rx, &ry);
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

      timer_prove.stop();
      (inst_evals, r1cs_eval_proof)
    };

    // --
    // PERM_EXEC_POLY
    // --

    let (perm_exec_poly_r1cs_sat_proof, perm_exec_poly_challenges) = {
      let (proof, perm_exec_poly_challenges) = {
        R1CSProof::prove(
          1,
          0,
          1,
          1,
          &vec![1],
          total_num_proofs_bound * num_vars,
          &perm_exec_poly_inst.inst,
          &total_proofs_times_vars_gens,
          vec![&vec![vec![perm_exec_w3_concat.clone()]]],
          vec![&vec![perm_exec_poly_w3_concat.clone()]],
          transcript,
          &mut random_tape,
        )
      };

      let proof_encoded: Vec<u8> = bincode::serialize(&proof).unwrap();
      Timer::print(&format!("len_r1cs_sat_proof {:?}", proof_encoded.len()));

      (proof, perm_exec_poly_challenges)
    };

    // Final evaluation on PERM_EXEC_POLY
    let (perm_exec_poly_inst_evals, perm_exec_poly_r1cs_eval_proof) = {
      let [rp, _, rx, ry] = perm_exec_poly_challenges.clone();
      let inst = perm_exec_poly_inst;
      let timer_eval = Timer::new("eval_sparse_polys");
      let inst_evals = {
        let (Ar, Br, Cr) = inst.inst.evaluate(&rp, &rx, &ry);
        Ar.append_to_transcript(b"Ar_claim", transcript);
        Br.append_to_transcript(b"Br_claim", transcript);
        Cr.append_to_transcript(b"Cr_claim", transcript);
        (Ar, Br, Cr)
      };
      timer_eval.stop();

      let r1cs_eval_proof = {
        let proof = R1CSEvalProof::prove(
          &perm_exec_poly_decomm.decomm,
          &[rp, rx].concat(),
          &ry,
          &inst_evals,
          &perm_exec_poly_gens.gens_r1cs_eval,
          transcript,
          &mut random_tape,
        );

        let proof_encoded: Vec<u8> = bincode::serialize(&proof).unwrap();
        Timer::print(&format!("len_r1cs_eval_proof {:?}", proof_encoded.len()));
        proof
      };

      timer_prove.stop();
      (inst_evals, r1cs_eval_proof)
    };

    // Record the prod of instance
    let (perm_exec_poly, proof_eval_perm_exec_prod) = {
      let r_len = perm_exec_poly_challenges[3].len();
      // Prod is the 3rd entry
      let perm_exec_poly = perm_exec_w3_concat[3];
      let (proof_eval_perm_exec_prod, _comm_perm_exec_prod) = PolyEvalProof::prove(
        &perm_exec_poly_w3_concat,
        None,
        &[vec![Scalar::zero(); r_len - 2], vec![Scalar::one(); 2]].concat(),
        &perm_exec_poly,
        None,
        &total_proofs_times_vars_gens.gens_pc,
        transcript,
        &mut random_tape,
      );
      (perm_exec_poly, proof_eval_perm_exec_prod)
    };
    
    SNARK {
      block_comm_vars_list,
      block_comm_inputs_list,
      exec_comm_inputs,
      perm_comm_w0,
      perm_block_comm_w2_list,
      perm_block_comm_w3_list,
      perm_block_comm_w3_concat,
      perm_exec_comm_w2,
      perm_exec_comm_w3,
      perm_exec_comm_w3_concat,

      consis_comm_w2,
      consis_comm_w3,

      block_r1cs_sat_proof,
      block_inst_evals,
      block_r1cs_eval_proof,

      consis_comb_r1cs_sat_proof,
      consis_comb_inst_evals,
      consis_comb_r1cs_eval_proof,

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
    }
  }

  /// A method to verify the SNARK proof of the satisfiability of an R1CS instance
  pub fn verify(
    &self,
    num_vars: usize,
    total_num_proofs_bound: usize,
    block_num_instances: usize,
    block_max_num_proofs_bound: usize,
    block_max_num_proofs: usize,
    block_num_proofs: &Vec<usize>,
    block_num_cons: usize,
    block_comm: &ComputationCommitment,
    block_gens: &SNARKGens,

    consis_num_proofs: usize,
    consis_comb_num_cons: usize,
    consis_comb_comm: &ComputationCommitment,
    consis_comb_gens: &SNARKGens,

    perm_prelim_num_cons: usize,
    perm_prelim_comm: &ComputationCommitment,
    perm_prelim_gens: &SNARKGens,

    perm_root_num_cons: usize,
    perm_root_comm: &ComputationCommitment,
    perm_root_gens: &SNARKGens,

    perm_block_poly_num_cons: usize,
    perm_block_poly_comm: &ComputationCommitment,
    perm_block_poly_gens: &SNARKGens,

    perm_exec_poly_num_cons: usize,
    perm_exec_poly_comm: &ComputationCommitment,
    perm_exec_poly_gens: &SNARKGens,

    vars_gens: &R1CSGens,
    proofs_times_vars_gens: &R1CSGens,
    total_proofs_times_vars_gens: &R1CSGens,

    transcript: &mut Transcript,
  ) -> Result<(), ProofVerifyError> {
    let timer_verify = Timer::new("SNARK::verify");
    transcript.append_protocol_name(SNARK::protocol_name());

    // append a commitment to the computation to the transcript
    block_comm.comm.append_to_transcript(b"block_comm", transcript);
    perm_prelim_comm.comm.append_to_transcript(b"consis_comm", transcript);
    perm_root_comm.comm.append_to_transcript(b"consis_comm", transcript);
    perm_block_poly_comm.comm.append_to_transcript(b"consis_comm", transcript);
    consis_comb_comm.comm.append_to_transcript(b"consis_comm", transcript);
    perm_exec_poly_comm.comm.append_to_transcript(b"consis_comm", transcript);

    // --
    // COMMITMENTS
    // --

    {
      // Commit num_proofs
      let timer_commit = Timer::new("metacommit");
      let block_max_num_proofs_64: u64 = block_max_num_proofs.try_into().unwrap();
      Scalar::from(block_max_num_proofs_64).append_to_transcript(b"block_max_num_proofs", transcript);
      for n in block_num_proofs {
        let n_64: u64 = (*n).try_into().unwrap();
        Scalar::from(n_64).append_to_transcript(b"block_num_proofs", transcript);
      }
      timer_commit.stop();

      // add the commitment to the verifier's transcript
      for p in 0..block_num_instances {
        self.block_comm_vars_list[p].append_to_transcript(b"poly_commitment", transcript);
        self.block_comm_inputs_list[p].append_to_transcript(b"poly_commitment", transcript);
      }
      self.exec_comm_inputs.append_to_transcript(b"poly_commitment", transcript);
    }

    // --
    // SAMPLE CHALLENGES AND COMMIT WITNESSES FOR PERMUTATION
    // --

    let comb_tau = transcript.challenge_scalar(b"challenge_tau");
    let comb_r = transcript.challenge_scalar(b"challenge_r");
    {
      self.perm_comm_w0.append_to_transcript(b"poly_commitment", transcript);
      for p in 0..block_num_instances {
        self.perm_block_comm_w2_list[p].append_to_transcript(b"poly_commitment", transcript);
        self.perm_block_comm_w3_list[p].append_to_transcript(b"poly_commitment", transcript);
      }
      self.perm_block_comm_w3_concat.append_to_transcript(b"poly_commitment", transcript);
      self.perm_exec_comm_w2.append_to_transcript(b"poly_commitment", transcript);
      self.perm_exec_comm_w3.append_to_transcript(b"poly_commitment", transcript);
      self.perm_exec_comm_w3_concat.append_to_transcript(b"poly_commitment", transcript);
      self.consis_comm_w2.append_to_transcript(b"poly_commitment", transcript);
      self.consis_comm_w3.append_to_transcript(b"poly_commitment", transcript);
    }

    // --
    // BLOCK CORRECTNESS
    // --

    {
      let timer_sat_proof = Timer::new("verify_sat_proof");
      let block_challenges = self.block_r1cs_sat_proof.verify(
        2,
        0,
        block_num_instances,
        block_max_num_proofs,
        block_num_proofs,
        num_vars,
        block_num_cons,
        &vars_gens,
        &self.block_inst_evals,
        vec![&self.block_comm_vars_list, &self.block_comm_inputs_list],
        transcript,
      )?;
      timer_sat_proof.stop();

      let timer_eval_proof = Timer::new("verify_eval_proof");
      // Verify Evaluation on BLOCK
      let (Ar, Br, Cr) = &self.block_inst_evals;
      Ar.append_to_transcript(b"Ar_claim", transcript);
      Br.append_to_transcript(b"Br_claim", transcript);
      Cr.append_to_transcript(b"Cr_claim", transcript);
      let [rp, _, rx, ry] = block_challenges;
      self.block_r1cs_eval_proof.verify(
        &block_comm.comm,
        &[rp, rx].concat(),
        &ry,
        &self.block_inst_evals,
        &block_gens.gens_r1cs_eval,
        transcript,
      )?;
      timer_eval_proof.stop();
    }

    // --
    // CONSIS_COMB
    // --

    {
      let timer_sat_proof = Timer::new("verify_sat_proof");
      let consis_comb_challenges = self.consis_comb_r1cs_sat_proof.verify(
        4,
        1,
        1,
        consis_num_proofs,
        &vec![consis_num_proofs],
        num_vars,
        consis_comb_num_cons,
        &vars_gens,
        &self.consis_comb_inst_evals,
        vec![&vec![self.perm_comm_w0.clone()], &vec![self.exec_comm_inputs.clone()], &vec![self.consis_comm_w2.clone()], &vec![self.consis_comm_w3.clone()]],
        transcript,
      )?;
      timer_sat_proof.stop();

      let timer_eval_proof = Timer::new("verify_eval_proof");
      // Verify Evaluation on PERM_BLOCK_ROOT
      let (Ar, Br, Cr) = &self.consis_comb_inst_evals;
      Ar.append_to_transcript(b"Ar_claim", transcript);
      Br.append_to_transcript(b"Br_claim", transcript);
      Cr.append_to_transcript(b"Cr_claim", transcript);
      let [_, _, rx, ry] = consis_comb_challenges;
      self.consis_comb_r1cs_eval_proof.verify(
        &consis_comb_comm.comm,
        &rx,
        &ry,
        &self.consis_comb_inst_evals,
        &consis_comb_gens.gens_r1cs_eval,
        transcript,
      )?;
      timer_eval_proof.stop();
    }


    // --
    // PERM_PRELIM
    // --

    {
      let timer_sat_proof = Timer::new("verify_sat_proof");
      let perm_prelim_challenges = self.perm_prelim_r1cs_sat_proof.verify(
        1,
        0,
        1,
        1,
        &vec![1],
        num_vars,
        perm_prelim_num_cons,
        &vars_gens,
        &self.perm_prelim_inst_evals,
        vec![&vec![self.perm_comm_w0.clone()]],
        transcript,
      )?;
      // Proof that first two entries of perm_w0 are tau and r
      let ry_len = perm_prelim_challenges[3].len();
      self.proof_eval_perm_w0_at_zero.verify_plain(
        &vars_gens.gens_pc,
        transcript,
        &vec![Scalar::zero(); ry_len],
        &comb_tau,
        &self.perm_comm_w0,
      )?;
      self.proof_eval_perm_w0_at_one.verify_plain(
        &vars_gens.gens_pc,
        transcript,
        &[vec![Scalar::zero(); ry_len - 1], vec![Scalar::one()]].concat(),
        &comb_r,
        &self.perm_comm_w0,
      )?;
      timer_sat_proof.stop();

      let timer_eval_proof = Timer::new("verify_eval_proof");
      // Verify Evaluation on PERM_PRELIM
      let (Ar, Br, Cr) = &self.perm_prelim_inst_evals;
      Ar.append_to_transcript(b"Ar_claim", transcript);
      Br.append_to_transcript(b"Br_claim", transcript);
      Cr.append_to_transcript(b"Cr_claim", transcript);
      let [rp, _, rx, ry] = perm_prelim_challenges;
      self.perm_prelim_r1cs_eval_proof.verify(
        &perm_prelim_comm.comm,
        &[rp, rx].concat(),
        &ry,
        &self.perm_prelim_inst_evals,
        &perm_prelim_gens.gens_r1cs_eval,
        transcript,
      )?;
      timer_eval_proof.stop();
    }

    // --
    // PERM_BLOCK_ROOT
    // --

    {
      let timer_sat_proof = Timer::new("verify_sat_proof");
      let perm_block_root_challenges = self.perm_block_root_r1cs_sat_proof.verify(
        4,
        1,
        block_num_instances,
        block_max_num_proofs,
        block_num_proofs,
        num_vars,
        perm_root_num_cons,
        &vars_gens,
        &self.perm_block_root_inst_evals,
        vec![&vec![self.perm_comm_w0.clone()], &self.block_comm_inputs_list, &self.perm_block_comm_w2_list, &self.perm_block_comm_w3_list],
        transcript,
      )?;
      timer_sat_proof.stop();

      let timer_eval_proof = Timer::new("verify_eval_proof");
      // Verify Evaluation on PERM_BLOCK_ROOT
      let (Ar, Br, Cr) = &self.perm_block_root_inst_evals;
      Ar.append_to_transcript(b"Ar_claim", transcript);
      Br.append_to_transcript(b"Br_claim", transcript);
      Cr.append_to_transcript(b"Cr_claim", transcript);
      let [_, _, rx, ry] = perm_block_root_challenges;
      self.perm_block_root_r1cs_eval_proof.verify(
        &perm_root_comm.comm,
        &rx,
        &ry,
        &self.perm_block_root_inst_evals,
        &perm_root_gens.gens_r1cs_eval,
        transcript,
      )?;
      timer_eval_proof.stop();
    }

    // --
    // PERM_BLOCK_POLY
    // --

    let perm_block_poly_bound_tau = {
      let timer_sat_proof = Timer::new("verify_sat_proof");
      let perm_block_poly_challenges = self.perm_block_poly_r1cs_sat_proof.verify(
        1,
        0,
        1,
        block_num_instances,
       &vec![block_num_instances],
        block_max_num_proofs_bound * num_vars,
        perm_block_poly_num_cons,
        &proofs_times_vars_gens,
        &self.perm_block_poly_inst_evals,
        vec![&vec![self.perm_block_comm_w3_concat.clone()]],
        transcript,
      )?;
      timer_sat_proof.stop();

      let timer_eval_proof = Timer::new("verify_eval_proof");
      // Verify Evaluation on PERM_BLOCK_POLY
      let (Ar, Br, Cr) = &self.perm_block_poly_inst_evals;
      Ar.append_to_transcript(b"Ar_claim", transcript);
      Br.append_to_transcript(b"Br_claim", transcript);
      Cr.append_to_transcript(b"Cr_claim", transcript);
      let [rp, _, rx, ry] = perm_block_poly_challenges.clone();
      self.perm_block_poly_r1cs_eval_proof.verify(
        &perm_block_poly_comm.comm,
        &[rp, rx].concat(),
        &ry,
        &self.perm_block_poly_inst_evals,
        &perm_block_poly_gens.gens_r1cs_eval,
        transcript,
      )?;
      timer_eval_proof.stop();
      // !!!TODO: verify that perm_block_comm_w3_concat evaluated on (rp, rq, ry) is each individual perm_block_comm_w3 evaluated on (rq, ry) combined

      // COMPUTE POLY FOR PERM_BLOCK
      let mut perm_block_poly_bound_tau = Scalar::one();
      let r_len = perm_block_poly_challenges[3].len();
      for p in 0..block_num_instances {
        // Convert p into binary
        let p_vec: Vec<Scalar> = (0..block_num_instances.log_2()).rev().map (|n| (p >> n) & 1).map(|i| Scalar::from(i as u64)).collect();
        self.proof_eval_perm_block_prod_list[p].verify_plain(
          &proofs_times_vars_gens.gens_pc,
          transcript,
          &[p_vec, vec![Scalar::zero(); r_len - 2], vec![Scalar::one(); 2]].concat(),
          &self.perm_block_poly_list[p],
          &self.perm_block_comm_w3_concat,
        )?;
        perm_block_poly_bound_tau *= self.perm_block_poly_list[p];
      }
      perm_block_poly_bound_tau
    };

    // --
    // PERM_EXEC_ROOT
    // --

    {
      let timer_sat_proof = Timer::new("verify_sat_proof");
      let perm_exec_root_challenges = self.perm_exec_root_r1cs_sat_proof.verify(
        4,
        1,
        1,
        consis_num_proofs,
        &vec![consis_num_proofs],
        num_vars,
        perm_root_num_cons,
        &vars_gens,
        &self.perm_exec_root_inst_evals,
        vec![&vec![self.perm_comm_w0.clone()], &vec![self.exec_comm_inputs.clone()], &vec![self.perm_exec_comm_w2.clone()], &vec![self.perm_exec_comm_w3.clone()]],
        transcript,
      )?;
      timer_sat_proof.stop();

      let timer_eval_proof = Timer::new("verify_eval_proof");
      // Verify Evaluation on PERM_EXEC_ROOT
      let (Ar, Br, Cr) = &self.perm_exec_root_inst_evals;
      Ar.append_to_transcript(b"Ar_claim", transcript);
      Br.append_to_transcript(b"Br_claim", transcript);
      Cr.append_to_transcript(b"Cr_claim", transcript);
      let [_, _, rx, ry] = perm_exec_root_challenges;
      self.perm_exec_root_r1cs_eval_proof.verify(
        &perm_root_comm.comm,
        &rx,
        &ry,
        &self.perm_exec_root_inst_evals,
        &perm_root_gens.gens_r1cs_eval,
        transcript,
      )?;
      timer_eval_proof.stop();
    }

    // --
    // PERM_EXEC_POLY
    // --

    let perm_exec_poly_bound_tau = {
      let timer_sat_proof = Timer::new("verify_sat_proof");
      let perm_exec_poly_challenges = self.perm_exec_poly_r1cs_sat_proof.verify(
        1,
        0,
        1,
        1,
       &vec![1],
        total_num_proofs_bound * num_vars,
        perm_exec_poly_num_cons,
        &total_proofs_times_vars_gens,
        &self.perm_exec_poly_inst_evals,
        vec![&vec![self.perm_exec_comm_w3_concat.clone()]],
        transcript,
      )?;
      timer_sat_proof.stop();

      let timer_eval_proof = Timer::new("verify_eval_proof");
      // Verify Evaluation on PERM_EXEC_POLY
      let (Ar, Br, Cr) = &self.perm_exec_poly_inst_evals;
      Ar.append_to_transcript(b"Ar_claim", transcript);
      Br.append_to_transcript(b"Br_claim", transcript);
      Cr.append_to_transcript(b"Cr_claim", transcript);
      let [rp, _, rx, ry] = perm_exec_poly_challenges.clone();
      self.perm_exec_poly_r1cs_eval_proof.verify(
        &perm_exec_poly_comm.comm,
        &[rp, rx].concat(),
        &ry,
        &self.perm_exec_poly_inst_evals,
        &perm_exec_poly_gens.gens_r1cs_eval,
        transcript,
      )?;
      timer_eval_proof.stop();
      // !!!TODO: verify that perm_exec_comm_w3_concat evaluated on (rp, rq, ry) is each individual perm_exec_comm_w3 evaluated on (rq, ry) combined

      // COMPUTE POLY FOR PERM_BLOCK
      let r_len = perm_exec_poly_challenges[3].len();
      self.proof_eval_perm_exec_prod.verify_plain(
        &total_proofs_times_vars_gens.gens_pc,
        transcript,
        &[vec![Scalar::zero(); r_len - 2], vec![Scalar::one(); 2]].concat(),
        &self.perm_exec_poly,
        &self.perm_exec_comm_w3_concat,
      )?;
      self.perm_exec_poly
    };

    // --
    // ASSERT_CORRECTNESS_OF_PERMUTATION
    // --
    assert_eq!(perm_block_poly_bound_tau, perm_exec_poly_bound_tau);

    timer_verify.stop();
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
