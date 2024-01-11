use crate::transcript::AppendToTranscript;

use super::dense_mlpoly::DensePolynomial;
use super::custom_dense_mlpoly::DensePolynomialPqx;
use super::errors::ProofVerifyError;
use super::math::Math;
use super::random::RandomTape;
use super::scalar::Scalar;
use super::sparse_mlpoly::{
  MultiSparseMatPolynomialAsDense, SparseMatEntry, SparseMatPolyCommitment,
  SparseMatPolyCommitmentGens, SparseMatPolyEvalProof, SparseMatPolynomial,
};
use super::timer::Timer;
use flate2::{write::ZlibEncoder, Compression};
use merlin::Transcript;
use serde::{Deserialize, Serialize};

#[derive(Debug, Serialize, Deserialize)]
pub struct R1CSInstance {
  num_instances: usize,
  num_cons: usize,
  num_vars: usize,
  // List of individual A, B, C for matrix multiplication
  A_list: Vec<SparseMatPolynomial>,
  B_list: Vec<SparseMatPolynomial>,
  C_list: Vec<SparseMatPolynomial>,
  // Concat all A's into a (p * x) by q matrix for commitment and evaluation
  A_poly: SparseMatPolynomial,
  B_poly: SparseMatPolynomial,
  C_poly: SparseMatPolynomial,
}

pub struct R1CSCommitmentGens {
  gens: SparseMatPolyCommitmentGens,
}

impl R1CSCommitmentGens {
  pub fn new(
    label: &'static [u8],
    num_instances: usize,
    num_cons: usize,
    num_vars: usize,
    num_nz_entries: usize,
  ) -> R1CSCommitmentGens {
    let num_poly_vars_x = num_instances.log_2() * num_cons.log_2();
    let num_poly_vars_y = num_vars.log_2();
    let gens =
      SparseMatPolyCommitmentGens::new(label, num_poly_vars_x, num_poly_vars_y, num_instances * num_nz_entries, 3);
    R1CSCommitmentGens { gens }
  }
}

#[derive(Debug, Serialize, Deserialize)]
pub struct R1CSCommitment {
  num_cons: usize,
  num_vars: usize,
  comm: SparseMatPolyCommitment,
}

impl AppendToTranscript for R1CSCommitment {
  fn append_to_transcript(&self, _label: &'static [u8], transcript: &mut Transcript) {
    transcript.append_u64(b"num_cons", self.num_cons as u64);
    transcript.append_u64(b"num_vars", self.num_vars as u64);
    self.comm.append_to_transcript(b"comm", transcript);
  }
}

pub struct R1CSDecommitment {
  dense: MultiSparseMatPolynomialAsDense,
}

impl R1CSCommitment {
  pub fn get_num_cons(&self) -> usize {
    self.num_cons
  }

  pub fn get_num_vars(&self) -> usize {
    self.num_vars
  }
}

impl R1CSInstance {
  pub fn new(
    num_instances: usize,
    num_cons: usize,
    num_vars: usize,
    A_list: &Vec<Vec<(usize, usize, Scalar)>>,
    B_list: &Vec<Vec<(usize, usize, Scalar)>>,
    C_list: &Vec<Vec<(usize, usize, Scalar)>>,
  ) -> R1CSInstance {
    Timer::print(&format!("number_of_instances {num_instances}"));
    Timer::print(&format!("number_of_constraints {num_cons}"));
    Timer::print(&format!("number_of_variables {num_vars}"));
    // Timer::print(&format!("number_non-zero_entries_A {}", A.len()));
    // Timer::print(&format!("number_non-zero_entries_B {}", B.len()));
    // Timer::print(&format!("number_non-zero_entries_C {}", C.len()));

    // check that num_instances is a power of 2
    assert_eq!(num_instances.next_power_of_two(), num_instances);

    // check that num_cons is a power of 2
    assert_eq!(num_cons.next_power_of_two(), num_cons);

    // check that num_vars is a power of 2
    assert_eq!(num_vars.next_power_of_two(), num_vars);

    // check that length of A_list, B_list, C_list are the same
    assert_eq!(A_list.len(), B_list.len());
    assert_eq!(B_list.len(), C_list.len());

    // no errors, so create polynomials
    let num_poly_vars_px = (num_instances * num_cons).log_2();
    let num_poly_vars_x = num_cons.log_2();
    let num_poly_vars_y = num_vars.log_2();

    let mut poly_A_list = Vec::new();
    let mut poly_B_list = Vec::new();
    let mut poly_C_list = Vec::new();

    let mut mat_A = Vec::new();
    let mut mat_B = Vec::new();
    let mut mat_C = Vec::new();

    for inst in 0..A_list.len() {
      let A = &A_list[inst];
      let B = &B_list[inst];
      let C = &C_list[inst];
      let list_A = (0..A.len())
        .map(|i| SparseMatEntry::new(A[i].0, A[i].1, A[i].2))
        .collect::<Vec<SparseMatEntry>>();
      let list_B = (0..B.len())
        .map(|i| SparseMatEntry::new(B[i].0, B[i].1, B[i].2))
        .collect::<Vec<SparseMatEntry>>();
      let list_C = (0..C.len())
        .map(|i| SparseMatEntry::new(C[i].0, C[i].1, C[i].2))
        .collect::<Vec<SparseMatEntry>>();
      poly_A_list.push(SparseMatPolynomial::new(num_poly_vars_x, num_poly_vars_y, list_A));
      poly_B_list.push(SparseMatPolynomial::new(num_poly_vars_x, num_poly_vars_y, list_B));
      poly_C_list.push(SparseMatPolynomial::new(num_poly_vars_x, num_poly_vars_y, list_C));
      let mut list_A = (0..A.len())
        .map(|i| SparseMatEntry::new(inst * num_cons + A[i].0, A[i].1, A[i].2))
        .collect::<Vec<SparseMatEntry>>();
      let mut list_B = (0..B.len())
        .map(|i| SparseMatEntry::new(inst * num_cons + B[i].0, B[i].1, B[i].2))
        .collect::<Vec<SparseMatEntry>>();
      let mut list_C = (0..C.len())
        .map(|i| SparseMatEntry::new(inst * num_cons + C[i].0, C[i].1, C[i].2))
        .collect::<Vec<SparseMatEntry>>();
      mat_A.append(&mut list_A);
      mat_B.append(&mut list_B);
      mat_C.append(&mut list_C);
    }

    R1CSInstance {
      num_instances,
      num_cons,
      num_vars,
      A_list: poly_A_list,
      B_list: poly_B_list,
      C_list: poly_C_list,
      A_poly: SparseMatPolynomial::new(num_poly_vars_px, num_poly_vars_y, mat_A),
      B_poly: SparseMatPolynomial::new(num_poly_vars_px, num_poly_vars_y, mat_B),
      C_poly: SparseMatPolynomial::new(num_poly_vars_px, num_poly_vars_y, mat_C)
    }
  }

  pub fn get_num_instances(&self) -> usize {
    self.num_instances
  }

  pub fn get_num_vars(&self) -> usize {
    self.num_vars
  }

  pub fn get_num_cons(&self) -> usize {
    self.num_cons
  }

  pub fn get_digest(&self) -> Vec<u8> {
    let mut encoder = ZlibEncoder::new(Vec::new(), Compression::default());
    bincode::serialize_into(&mut encoder, &self).unwrap();
    encoder.finish().unwrap()
  }

  /*
  pub fn produce_synthetic_r1cs(
    num_instances: usize,
    num_proofs_list: Vec<usize>,
    num_cons: usize,
    num_vars: usize,
    num_inputs: usize,
  ) -> (R1CSInstance, Vec<Vec<Vec<Scalar>>>, Vec<Vec<Vec<Scalar>>>) {
    Timer::print(&format!("number_of_instances {num_instances}"));
    Timer::print(&format!("number_of_constraints {num_cons}"));
    Timer::print(&format!("number_of_variables {num_vars}"));
    Timer::print(&format!("number_of_inputs {num_inputs}"));

    let mut csprng: OsRng = OsRng;

    // assert everything is power of 2
    assert_eq!((num_instances.log_2()).pow2(), num_instances);
    for num_proofs in num_proofs_list {
      assert_eq!((num_proofs.log_2()).pow2(), num_proofs);
    }
    assert_eq!((num_cons.log_2()).pow2(), num_cons);
    assert_eq!((num_vars.log_2()).pow2(), num_vars);

    // find max_num_proofs and min_num_proofs
    let mut max_num_proofs = num_proofs_list[0];
    let mut min_num_proofs = num_proofs_list[0];
    for num_proofs in num_proofs_list {
      if num_proofs > max_num_proofs {
        max_num_proofs = num_proofs;
      }
      if num_proofs < min_num_proofs {
        min_num_proofs = num_proofs;
      }
    }

    // num_inputs + 1 <= num_vars
    assert!(num_inputs < num_vars);

    // z is organized as [vars,1,io]
    let size_z = num_vars + num_inputs + 1;

    // produce a random satisfying assignment for each instance
    let mut Z_mat = Vec::new();
    let mut A_list = Vec::new();
    let mut B_list = Vec::new();
    let mut C_list = Vec::new();
    for i in 0..num_instances {
      Z_mat.push(Vec::new());
      let mut Z: Vec<Scalar> = (0..size_z)
        .map(|_i| Scalar::random(&mut csprng))
        .collect::<Vec<Scalar>>();
      Z[num_vars] = Scalar::one();
      Z_mat[i].push(Z);

      // three sparse matrices for each instance
      let mut A: Vec<SparseMatEntry> = Vec::new();
      let mut B: Vec<SparseMatEntry> = Vec::new();
      let mut C: Vec<SparseMatEntry> = Vec::new();
      let one = Scalar::one();
      for i in 0..num_cons {
        let A_idx = i % size_z;
        let B_idx = (i + 2) % size_z;
        A.push(SparseMatEntry::new(i, A_idx, one));
        B.push(SparseMatEntry::new(i, B_idx, one));
        let AB_val = Z[A_idx] * Z[B_idx];

        let C_idx = (i + 3) % size_z;
        let C_val = Z[C_idx];

        if C_val == Scalar::zero() {
          C.push(SparseMatEntry::new(i, num_vars, AB_val));
        } else {
          C.push(SparseMatEntry::new(
            i,
            C_idx,
            AB_val * C_val.invert().unwrap(),
          ));
        }
      }

      // from A, B, C produce more Z
      for _ in 1..num_proofs_list[i] {

      }

      A_list.push(A);
      B_list.push(B);
      C_list.push(C);

      
    }

    Timer::print(&format!("number_non-zero_entries_A {}", A.len()));
    Timer::print(&format!("number_non-zero_entries_B {}", B.len()));
    Timer::print(&format!("number_non-zero_entries_C {}", C.len()));

    let num_poly_vars_x = num_cons.log_2();
    let num_poly_vars_y = (2 * num_vars).log_2();
    let poly_A = SparseMatPolynomial::new(num_poly_vars_x, num_poly_vars_y, A);
    let poly_B = SparseMatPolynomial::new(num_poly_vars_x, num_poly_vars_y, B);
    let poly_C = SparseMatPolynomial::new(num_poly_vars_x, num_poly_vars_y, C);

    let inst = R1CSInstance {
      num_cons,
      num_vars,
      num_inputs,
      A: poly_A,
      B: poly_B,
      C: poly_C,
    };

    assert!(inst.is_sat(&Z[..num_vars], &Z[num_vars + 1..]));

    (inst, Z[..num_vars].to_vec(), Z[num_vars + 1..].to_vec())
  }
  */

  pub fn is_sat(&self, vars: &Vec<Vec<Vec<Scalar>>>, input: &Vec<Vec<Vec<Scalar>>>) -> bool {
    assert_eq!(vars.len(), self.num_instances);
    assert_eq!(input.len(), self.num_instances);

    for p in 0..self.num_instances {
      assert_eq!(vars[p].len(), input[p].len());
      for q in 0..vars[p].len() {
        let vars = &vars[p][q];
        let input = &input[p][q];
        assert_eq!(vars.len(), self.num_vars);

        let z = {
          let mut z = vars.to_vec();
          z.extend(&vec![Scalar::one()]);
          z.extend(input);
          z
        };

        // verify if Az * Bz - Cz = [0...]
        let Az = self
          .A_list[p]
          .multiply_vec(self.num_cons, self.num_vars, &z);
        let Bz = self
          .B_list[p]
          .multiply_vec(self.num_cons, self.num_vars, &z);
        let Cz = self
          .C_list[p]
          .multiply_vec(self.num_cons, self.num_vars, &z);

        assert_eq!(Az.len(), self.num_cons);
        assert_eq!(Bz.len(), self.num_cons);
        assert_eq!(Cz.len(), self.num_cons);
        let res: usize = (0..self.num_cons)
          .map(|i| usize::from(Az[i] * Bz[i] != Cz[i]))
          .sum();

        if res != 0 { return false };
      }
    }
    return true;
  }

  // Az(p, q, x) <- A(p, x) * z(p, q, x), where we require p for A and z are the same
  // Return Az, Bz, Cz as DensePolynomialPqx
  pub fn multiply_vec_block(
    &self,
    num_instances: usize,
    num_proofs: &Vec<usize>,
    max_num_proofs: usize,
    num_rows: usize,
    num_cols: usize,
    z_mat: &Vec<Vec<Vec<Scalar>>>
  ) -> (DensePolynomialPqx, DensePolynomialPqx, DensePolynomialPqx) {
    assert!(self.num_instances == 1 || self.num_instances == num_instances);
    assert_eq!(num_rows, self.num_cons);
    assert_eq!(num_cols, self.num_vars);
    let mut Az = Vec::new();
    let mut Bz = Vec::new();
    let mut Cz = Vec::new();

    for p in 0..num_instances {
      let p_inst = if self.num_instances == 1 { 0 } else { p };

      let z_list = &z_mat[p];
      assert!(num_proofs[p] <= max_num_proofs);
      Az.push(Vec::new());
      Bz.push(Vec::new());
      Cz.push(Vec::new());
      for q in 0..num_proofs[p] {
        let z = &z_list[q];
        assert_eq!(z.len(), num_cols);

        Az[p].push(self.A_list[p_inst].multiply_vec(num_rows, num_cols, z));
        Bz[p].push(self.B_list[p_inst].multiply_vec(num_rows, num_cols, z));
        Cz[p].push(self.C_list[p_inst].multiply_vec(num_rows, num_cols, z));
      }
    }
    (
      DensePolynomialPqx::new_rev(&Az, num_proofs, max_num_proofs),
      DensePolynomialPqx::new_rev(&Bz, num_proofs, max_num_proofs),
      DensePolynomialPqx::new_rev(&Cz, num_proofs, max_num_proofs)
    )
  }

  // Multiply one instance by a list of inputs
  // Length of each input might be smaller than the length of the instance,
  // in that case need to append the result by 0
  pub fn multiply_vec_single(
    &self,
    num_instances: usize,
    num_proofs: &Vec<usize>,
    max_num_proofs_bound: usize,
    max_num_proofs: usize,
    num_rows: usize,
    num_cols: usize,
    z_list: &Vec<Vec<Scalar>>,
  ) -> (DensePolynomialPqx, DensePolynomialPqx, DensePolynomialPqx) {
    assert!(max_num_proofs <= max_num_proofs_bound);
    assert!(max_num_proofs_bound * num_rows <= self.num_cons);
    assert!(max_num_proofs_bound * num_cols <= self.num_vars);

    let mut Az = Vec::new();
    let mut Bz = Vec::new();
    let mut Cz = Vec::new();
    
    for p in 0..num_instances {
      let z = &z_list[p];
      assert!(num_proofs[p] <= max_num_proofs);
      // Each returns a num_proofs[p] * num_rows matrix
      Az.push(self.A_list[0].multiply_vec_pad(max_num_proofs_bound, num_proofs[p], num_rows, num_cols, z));
      Bz.push(self.B_list[0].multiply_vec_pad(max_num_proofs_bound, num_proofs[p], num_rows, num_cols, z));
      Cz.push(self.C_list[0].multiply_vec_pad(max_num_proofs_bound, num_proofs[p], num_rows, num_cols, z));
    }
    (
      DensePolynomialPqx::new_rev(&Az, num_proofs, max_num_proofs),
      DensePolynomialPqx::new_rev(&Bz, num_proofs, max_num_proofs),
      DensePolynomialPqx::new_rev(&Cz, num_proofs, max_num_proofs)
    )
  }

  pub fn multiply_vec(
    &self,
    p: usize,
    num_rows: usize,
    num_cols: usize,
    z: &[Scalar],
  ) -> (DensePolynomial, DensePolynomial, DensePolynomial) {
    assert_eq!(num_rows, self.num_cons);
    assert_eq!(z.len(), num_cols);
    assert!(num_cols > self.num_vars);
    (
      DensePolynomial::new(self.A_list[p].multiply_vec(num_rows, num_cols, z)),
      DensePolynomial::new(self.B_list[p].multiply_vec(num_rows, num_cols, z)),
      DensePolynomial::new(self.C_list[p].multiply_vec(num_rows, num_cols, z)),
    )
  }

  pub fn compute_eval_table_sparse(
    &self,
    num_instances: usize,
    num_rows: usize,
    num_cols: usize,
    evals: &[Scalar],
  ) -> (Vec<Scalar>, Vec<Scalar>, Vec<Scalar>) {
    assert!(self.num_instances == 1 || self.num_instances == num_instances);
    assert_eq!(num_rows, self.num_cons);
    assert_eq!(num_cols, self.num_vars);

    let mut evals_A_list = Vec::new();
    let mut evals_B_list = Vec::new();
    let mut evals_C_list = Vec::new();
    for p in 0..num_instances {
      let p_inst = if self.num_instances == 1 { 0 } else { p };

      let evals_A = self.A_list[p_inst].compute_eval_table_sparse(evals, num_rows, num_cols);
      let evals_B = self.B_list[p_inst].compute_eval_table_sparse(evals, num_rows, num_cols);
      let evals_C = self.C_list[p_inst].compute_eval_table_sparse(evals, num_rows, num_cols);
      evals_A_list.extend(evals_A);
      evals_B_list.extend(evals_B);
      evals_C_list.extend(evals_C);
    }

    (evals_A_list, evals_B_list, evals_C_list)
  }

  // Only compute the first max_num_proofs / max_num_proofs_bound entries
  // num_cols is already num_vars * max_num_proofs / max_num_proofs_bound
  pub fn compute_eval_table_sparse_single(
    &self,
    num_instances: usize,
    max_num_proofs: usize,
    max_num_proofs_bound: usize,
    num_rows: usize,
    num_cols: usize,
    evals: &[Scalar],
  ) -> (Vec<Scalar>, Vec<Scalar>, Vec<Scalar>) {
    assert!(self.num_instances == 1 || self.num_instances == num_instances);
    assert_eq!(num_rows, self.num_cons);
    assert!(num_cols <= self.num_vars * max_num_proofs / max_num_proofs_bound);

    let mut evals_A_list = Vec::new();
    let mut evals_B_list = Vec::new();
    let mut evals_C_list = Vec::new();
    for p in 0..num_instances {
      let p_inst = if self.num_instances == 1 { 0 } else { p };

      let evals_A = self.A_list[p_inst].compute_eval_table_sparse_single(evals, max_num_proofs, max_num_proofs_bound, num_rows, num_cols);
      let evals_B = self.B_list[p_inst].compute_eval_table_sparse_single(evals, max_num_proofs, max_num_proofs_bound, num_rows, num_cols);
      let evals_C = self.C_list[p_inst].compute_eval_table_sparse_single(evals, max_num_proofs, max_num_proofs_bound, num_rows, num_cols);
      evals_A_list.extend(evals_A);
      evals_B_list.extend(evals_B);
      evals_C_list.extend(evals_C);
    }

    (evals_A_list, evals_B_list, evals_C_list)
  }


  pub fn evaluate(&self, rp: &[Scalar], rx: &[Scalar], ry: &[Scalar]) -> (Scalar, Scalar, Scalar) {
    let evals = SparseMatPolynomial::multi_evaluate(&[&self.A_poly, &self.B_poly, &self.C_poly], &[rp, rx].concat(), ry);
    (evals[0], evals[1], evals[2])
  }

  pub fn commit(&self, gens: &R1CSCommitmentGens) -> (R1CSCommitment, R1CSDecommitment) {
    let (comm, dense) = SparseMatPolynomial::multi_commit(&[&self.A_poly, &self.B_poly, &self.C_poly], &gens.gens);
    let r1cs_comm = R1CSCommitment {
      num_cons: self.num_instances * self.num_cons,
      num_vars: self.num_vars,
      comm,
    };

    let r1cs_decomm = R1CSDecommitment { dense };

    (r1cs_comm, r1cs_decomm)
  }
}

#[derive(Debug, Serialize, Deserialize)]
pub struct R1CSEvalProof {
  proof: SparseMatPolyEvalProof,
}

impl R1CSEvalProof {
  pub fn prove(
    decomm: &R1CSDecommitment,
    rx: &[Scalar], // point at which the polynomial is evaluated
    ry: &[Scalar],
    evals: &(Scalar, Scalar, Scalar),
    gens: &R1CSCommitmentGens,
    transcript: &mut Transcript,
    random_tape: &mut RandomTape,
  ) -> R1CSEvalProof {
    let timer = Timer::new("R1CSEvalProof::prove");
    let proof = SparseMatPolyEvalProof::prove(
      &decomm.dense,
      rx,
      ry,
      &[evals.0, evals.1, evals.2],
      &gens.gens,
      transcript,
      random_tape,
    );
    timer.stop();

    R1CSEvalProof { proof }
  }

  pub fn verify(
    &self,
    comm: &R1CSCommitment,
    rx: &[Scalar], // point at which the R1CS matrix polynomials are evaluated
    ry: &[Scalar],
    evals: &(Scalar, Scalar, Scalar),
    gens: &R1CSCommitmentGens,
    transcript: &mut Transcript,
  ) -> Result<(), ProofVerifyError> {
    self.proof.verify(
      &comm.comm,
      rx,
      ry,
      &[evals.0, evals.1, evals.2],
      &gens.gens,
      transcript,
    )
  }
}
