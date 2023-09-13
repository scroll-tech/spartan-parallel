use core::num;

use crate::transcript::AppendToTranscript;

use super::dense_mlpoly::DensePolynomial;
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
use rand::rngs::OsRng;
use serde::{Deserialize, Serialize};

#[derive(Debug, Serialize, Deserialize)]
pub struct R1CSInstance {
  num_instances: usize,
  num_cons: usize,
  num_vars: usize,
  num_inputs: usize,
  A: SparseMatPolynomial,
  B: SparseMatPolynomial,
  C: SparseMatPolynomial,
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
    num_inputs: usize,
    num_nz_entries: usize,
  ) -> R1CSCommitmentGens {
    assert!(num_inputs < num_vars);
    let num_poly_vars_x = num_instances.log_2() * num_cons.log_2();
    let num_poly_vars_y = (2 * num_vars).log_2();
    let gens =
      SparseMatPolyCommitmentGens::new(label, num_poly_vars_x, num_poly_vars_y, num_instances * num_nz_entries, 3);
    R1CSCommitmentGens { gens }
  }
}

#[derive(Debug, Serialize, Deserialize)]
pub struct R1CSCommitment {
  num_cons: usize,
  num_vars: usize,
  num_inputs: usize,
  comm: SparseMatPolyCommitment,
}

impl AppendToTranscript for R1CSCommitment {
  fn append_to_transcript(&self, _label: &'static [u8], transcript: &mut Transcript) {
    transcript.append_u64(b"num_cons", self.num_cons as u64);
    transcript.append_u64(b"num_vars", self.num_vars as u64);
    transcript.append_u64(b"num_inputs", self.num_inputs as u64);
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

  pub fn get_num_inputs(&self) -> usize {
    self.num_inputs
  }
}

impl R1CSInstance {
  pub fn new(
    num_instances: usize,
    num_cons: usize,
    num_vars: usize,
    num_inputs: usize,
    A_list: &Vec<Vec<(usize, usize, Scalar)>>,
    B_list: &Vec<Vec<(usize, usize, Scalar)>>,
    C_list: &Vec<Vec<(usize, usize, Scalar)>>,
  ) -> R1CSInstance {
    Timer::print(&format!("number_of_instances {num_instances}"));
    Timer::print(&format!("number_of_constraints {num_cons}"));
    Timer::print(&format!("number_of_variables {num_vars}"));
    Timer::print(&format!("number_of_inputs {num_inputs}"));
    // Timer::print(&format!("number_non-zero_entries_A {}", A.len()));
    // Timer::print(&format!("number_non-zero_entries_B {}", B.len()));
    // Timer::print(&format!("number_non-zero_entries_C {}", C.len()));

    // check that num_instances is a power of 2
    assert_eq!(num_instances.next_power_of_two(), num_instances);

    // check that num_cons is a power of 2
    assert_eq!(num_cons.next_power_of_two(), num_cons);

    // check that num_vars is a power of 2
    assert_eq!(num_vars.next_power_of_two(), num_vars);

    // check that number_inputs + 1 <= num_vars
    assert!(num_inputs < num_vars);

    // check that length of A_list, B_list, C_list are the same
    assert_eq!(A_list.len(), B_list.len());
    assert_eq!(B_list.len(), C_list.len());

    // no errors, so create polynomials
    let num_poly_vars_x = (num_instances * num_cons).log_2();
    let num_poly_vars_y = (2 * num_vars).log_2();

    let mut mat_A_list = Vec::new();
    let mut mat_B_list = Vec::new();
    let mut mat_C_list = Vec::new();

    for inst in 0..A_list.len() {
      let A = &A_list[inst];
      let B = &B_list[inst];
      let C = &C_list[inst];
      let mut mat_A = (0..A.len())
        .map(|i| SparseMatEntry::new(num_cons * inst + A[i].0, A[i].1, A[i].2))
        .collect::<Vec<SparseMatEntry>>();
      let mut mat_B = (0..B.len())
        .map(|i| SparseMatEntry::new(num_cons * inst + B[i].0, B[i].1, B[i].2))
        .collect::<Vec<SparseMatEntry>>();
      let mut mat_C = (0..C.len())
        .map(|i| SparseMatEntry::new(num_cons * inst + C[i].0, C[i].1, C[i].2))
        .collect::<Vec<SparseMatEntry>>();
      mat_A_list.append(&mut mat_A);
      mat_B_list.append(&mut mat_B);
      mat_C_list.append(&mut mat_C);
    }

    let poly_A = SparseMatPolynomial::new(num_poly_vars_x, num_poly_vars_y, mat_A_list);
    let poly_B = SparseMatPolynomial::new(num_poly_vars_x, num_poly_vars_y, mat_B_list);
    let poly_C = SparseMatPolynomial::new(num_poly_vars_x, num_poly_vars_y, mat_C_list);

    R1CSInstance {
      num_instances,
      num_cons,
      num_vars,
      num_inputs,
      A: poly_A,
      B: poly_B,
      C: poly_C,
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

  pub fn get_num_inputs(&self) -> usize {
    self.num_inputs
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

  pub fn is_sat(&self, vars: &[Scalar], input: &[Scalar]) -> bool {
    assert_eq!(vars.len(), self.num_vars);
    assert_eq!(input.len(), self.num_inputs);

    let z = {
      let mut z = vars.to_vec();
      z.extend(&vec![Scalar::one()]);
      z.extend(input);
      z
    };

    // verify if Az * Bz - Cz = [0...]
    let Az = self
      .A
      .multiply_vec(self.num_cons, self.num_vars + self.num_inputs + 1, &z);
    let Bz = self
      .B
      .multiply_vec(self.num_cons, self.num_vars + self.num_inputs + 1, &z);
    let Cz = self
      .C
      .multiply_vec(self.num_cons, self.num_vars + self.num_inputs + 1, &z);

    assert_eq!(Az.len(), self.num_cons);
    assert_eq!(Bz.len(), self.num_cons);
    assert_eq!(Cz.len(), self.num_cons);
    let res: usize = (0..self.num_cons)
      .map(|i| usize::from(Az[i] * Bz[i] != Cz[i]))
      .sum();

    res == 0
  }

  // Pad the result of each A * z[i] to a power of 2 and concatenate them together
  // So the result looks like [A * z[0], 0, ..., 0, A * z[1], 0, ..., 0, A * z[3], ...]
  pub fn multiply_vec_bunched(
    &self,
    num_instances: usize,
    max_num_proofs: usize,
    num_rows: usize,
    num_cols: usize,
    z_mat: &Vec<Vec<Vec<Scalar>>>
  ) -> (DensePolynomial, DensePolynomial, DensePolynomial) {
    assert_eq!(num_rows, self.num_cons);
    assert!(num_cols > self.num_vars);
    // XXX: VERY UGLY!
    let mut Az = vec![Scalar::zero(); num_instances * max_num_proofs * num_rows];
    let mut Bz = vec![Scalar::zero(); num_instances * max_num_proofs * num_rows];
    let mut Cz = vec![Scalar::zero(); num_instances * max_num_proofs * num_rows];

    for p in 0..num_instances {
      let z_list = &z_mat[p];
      let num_proofs = z_list.len();
      assert!(num_proofs <= max_num_proofs);
      for q in 0..num_proofs {
        let z = &z_list[q];
        assert_eq!(z.len(), num_cols);
        let tmp_Az = self.A.multiply_vec(num_instances * num_rows, num_cols, z);
        let tmp_Bz = self.B.multiply_vec(num_instances * num_rows, num_cols, z);
        let tmp_Cz = self.C.multiply_vec(num_instances * num_rows, num_cols, z);

        // Select the correct instance
        for x in 0..num_rows {
          let i = p * num_rows + x;
          Az[x * max_num_proofs * num_instances + q * num_instances + p] = tmp_Az[i];
          Bz[x * max_num_proofs * num_instances + q * num_instances + p] = tmp_Bz[i];
          Cz[x * max_num_proofs * num_instances + q * num_instances + p] = tmp_Cz[i];
        }
      }
    }
    (
      DensePolynomial::new(Az),
      DensePolynomial::new(Bz),
      DensePolynomial::new(Cz),
    )
  }

  pub fn multiply_vec(
    &self,
    num_rows: usize,
    num_cols: usize,
    z: &[Scalar],
  ) -> (DensePolynomial, DensePolynomial, DensePolynomial) {
    assert_eq!(num_rows, self.num_cons);
    assert_eq!(z.len(), num_cols);
    assert!(num_cols > self.num_vars);
    (
      DensePolynomial::new(self.A.multiply_vec(num_rows, num_cols, z)),
      DensePolynomial::new(self.B.multiply_vec(num_rows, num_cols, z)),
      DensePolynomial::new(self.C.multiply_vec(num_rows, num_cols, z)),
    )
  }

  pub fn compute_eval_table_sparse(
    &self,
    num_rows: usize,
    num_cols: usize,
    evals: &[Scalar],
  ) -> (Vec<Scalar>, Vec<Scalar>, Vec<Scalar>) {
    assert_eq!(num_rows, self.num_instances * self.num_cons);
    assert!(num_cols > self.num_vars);

    let evals_A = self.A.compute_eval_table_sparse(evals, num_rows, num_cols);
    let evals_B = self.B.compute_eval_table_sparse(evals, num_rows, num_cols);
    let evals_C = self.C.compute_eval_table_sparse(evals, num_rows, num_cols);

    (evals_A, evals_B, evals_C)
  }

  pub fn evaluate(&self, rx: &[Scalar], ry: &[Scalar]) -> (Scalar, Scalar, Scalar) {
    let evals = SparseMatPolynomial::multi_evaluate(&[&self.A, &self.B, &self.C], rx, ry);
    (evals[0], evals[1], evals[2])
  }

  pub fn commit(&self, gens: &R1CSCommitmentGens) -> (R1CSCommitment, R1CSDecommitment) {
    let (comm, dense) = SparseMatPolynomial::multi_commit(&[&self.A, &self.B, &self.C], &gens.gens);
    let r1cs_comm = R1CSCommitment {
      num_cons: self.num_cons,
      num_vars: self.num_vars,
      num_inputs: self.num_inputs,
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
