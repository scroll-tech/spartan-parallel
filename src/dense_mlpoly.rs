#![allow(clippy::too_many_arguments)]
use super::commitments::{Commitments, MultiCommitGens};
use super::errors::ProofVerifyError;
use super::group::{CompressedGroup, GroupElement, VartimeMultiscalarMul};
use super::math::Math;
use super::nizk::{DotProductProofGens, DotProductProofLog};
use super::random::RandomTape;
use super::scalar::Scalar;
use super::transcript::{AppendToTranscript, ProofTranscript};
use core::ops::Index;
use curve25519_dalek::ristretto::RistrettoPoint;
use merlin::Transcript;
use serde::{Deserialize, Serialize};
use std::collections::HashMap;

#[cfg(feature = "multicore")]
use rayon::prelude::*;

#[derive(Debug, Clone)]
pub struct DensePolynomial {
  num_vars: usize, // the number of variables in the multilinear polynomial
  len: usize,
  Z: Vec<Scalar>, // evaluations of the polynomial in all the 2^num_vars Boolean inputs
}

#[derive(Clone, Serialize)]
pub struct PolyCommitmentGens {
  pub gens: DotProductProofGens,
}

impl PolyCommitmentGens {
  // the number of variables in the multilinear polynomial
  pub fn new(num_vars: usize, label: &'static [u8]) -> PolyCommitmentGens {
    let (_left, right) = EqPolynomial::compute_factored_lens(num_vars);
    let gens = DotProductProofGens::new(right.pow2(), label);
    PolyCommitmentGens { gens }
  }
}

pub struct PolyCommitmentBlinds {
  pub(crate) blinds: Vec<Scalar>,
}

#[derive(Debug, Serialize, Deserialize, Clone)]
pub struct PolyCommitment {
  pub(crate) C: Vec<CompressedGroup>,
}

impl PolyCommitment {
  pub fn empty() -> Self {
    PolyCommitment { C: Vec::new() }
  }
}

#[derive(Debug, Serialize, Deserialize)]
pub struct ConstPolyCommitment {
  C: CompressedGroup,
}

pub struct EqPolynomial {
  r: Vec<Scalar>,
}

impl EqPolynomial {
  pub fn new(r: Vec<Scalar>) -> Self {
    EqPolynomial { r }
  }

  pub fn evaluate(&self, rx: &[Scalar]) -> Scalar {
    assert_eq!(self.r.len(), rx.len());
    (0..rx.len())
      .map(|i| self.r[i] * rx[i] + (Scalar::one() - self.r[i]) * (Scalar::one() - rx[i]))
      .product()
  }

  pub fn evals(&self) -> Vec<Scalar> {
    let ell = self.r.len();

    let mut evals: Vec<Scalar> = vec![Scalar::one(); ell.pow2()];
    let mut size = 1;
    for j in 0..ell {
      // in each iteration, we double the size of chis
      size *= 2;
      for i in (0..size).rev().step_by(2) {
        // copy each element from the prior iteration twice
        let scalar = evals[i / 2];
        evals[i] = scalar * self.r[j];
        evals[i - 1] = scalar - evals[i];
      }
    }
    evals
  }

  // Only bound Eq on the first self.r.len() of the total_len variables
  pub fn _evals_front(&self, total_len: usize) -> Vec<Scalar> {
    let ell = self.r.len();

    let mut evals: Vec<Scalar> = vec![Scalar::one(); total_len.pow2()];
    let base_size = (total_len - ell).pow2();
    let mut size = base_size;
    for j in 0..ell {
      // in each iteration, we double the size of chis
      size *= 2;
      for i in (0..size).rev().step_by(base_size * 2) {
        // copy each element from the prior iteration twice
        let scalar = evals[i / 2];
        let high = scalar * self.r[j];
        let low = scalar - high;
        for k in 0..base_size {
          evals[i - k] = high;
          evals[i - base_size - k] = low;
        }
      }
    }
    evals
  }

  pub fn compute_factored_lens(ell: usize) -> (usize, usize) {
    (ell / 2, ell - ell / 2)
  }

  pub fn compute_factored_evals(&self) -> (Vec<Scalar>, Vec<Scalar>) {
    let ell = self.r.len();
    let (left_num_vars, _right_num_vars) = EqPolynomial::compute_factored_lens(ell);

    let L = EqPolynomial::new(self.r[..left_num_vars].to_vec()).evals();
    let R = EqPolynomial::new(self.r[left_num_vars..ell].to_vec()).evals();

    (L, R)
  }
}

pub struct IdentityPolynomial {
  size_point: usize,
}

impl IdentityPolynomial {
  pub fn new(size_point: usize) -> Self {
    IdentityPolynomial { size_point }
  }

  pub fn evaluate(&self, r: &[Scalar]) -> Scalar {
    let len = r.len();
    assert_eq!(len, self.size_point);
    (0..len)
      .map(|i| Scalar::from((len - i - 1).pow2() as u64) * r[i])
      .sum()
  }
}

impl DensePolynomial {
  pub fn new(mut Z: Vec<Scalar>) -> Self {
    // If length of Z is not a power of 2, append Z with 0
    let zero = Scalar::zero();
    Z.extend(vec![zero; Z.len().next_power_of_two() - Z.len()]);
    DensePolynomial {
      num_vars: Z.len().log_2(),
      len: Z.len(),
      Z,
    }
  }

  pub fn get_num_vars(&self) -> usize {
    self.num_vars
  }

  pub fn len(&self) -> usize {
    self.len
  }

  pub fn clone(&self) -> DensePolynomial {
    DensePolynomial::new(self.Z[0..self.len].to_vec())
  }

  pub fn split(&self, idx: usize) -> (DensePolynomial, DensePolynomial) {
    assert!(idx < self.len());
    (
      DensePolynomial::new(self.Z[..idx].to_vec()),
      DensePolynomial::new(self.Z[idx..2 * idx].to_vec()),
    )
  }

  #[cfg(feature = "multicore")]
  fn commit_inner(&self, blinds: &[Scalar], gens: &MultiCommitGens) -> PolyCommitment {
    let L_size = blinds.len();
    let R_size = self.Z.len() / L_size;
    assert_eq!(L_size * R_size, self.Z.len());
    let C = (0..L_size)
      .into_par_iter()
      .map(|i| {
        self.Z[R_size * i..R_size * (i + 1)]
          .commit(&blinds[i], gens)
          .compress()
      })
      .collect();
    PolyCommitment { C }
  }

  #[cfg(not(feature = "multicore"))]
  fn commit_inner(&self, blinds: &[Scalar], gens: &MultiCommitGens) -> PolyCommitment {
    let L_size = blinds.len();
    let R_size = self.Z.len() / L_size;
    assert_eq!(L_size * R_size, self.Z.len());
    let C = (0..L_size)
      .map(|i| {
        self.Z[R_size * i..R_size * (i + 1)]
          .commit(&blinds[i], gens)
          .compress()
      })
      .collect();
    PolyCommitment { C }
  }

  pub fn commit(
    &self,
    gens: &PolyCommitmentGens,
    random_tape: Option<&mut RandomTape>,
  ) -> (PolyCommitment, PolyCommitmentBlinds) {
    let n = self.Z.len();
    let ell = self.get_num_vars();
    assert_eq!(n, ell.pow2());

    let (left_num_vars, right_num_vars) = EqPolynomial::compute_factored_lens(ell);
    let L_size = left_num_vars.pow2();
    let R_size = right_num_vars.pow2();
    assert_eq!(L_size * R_size, n);

    let blinds = if let Some(t) = random_tape {
      PolyCommitmentBlinds {
        blinds: t.random_vector(b"poly_blinds", L_size),
      }
    } else {
      PolyCommitmentBlinds {
        blinds: vec![Scalar::zero(); L_size],
      }
    };

    (self.commit_inner(&blinds.blinds, &gens.gens.gens_n), blinds)
  }

  pub fn commit_with_blind(
    &self,
    gens: &PolyCommitmentGens,
    blinds: &PolyCommitmentBlinds,
  ) -> PolyCommitment {
    let n = self.Z.len();
    let ell = self.get_num_vars();
    assert_eq!(n, ell.pow2());

    let (left_num_vars, right_num_vars) = EqPolynomial::compute_factored_lens(ell);
    let L_size = left_num_vars.pow2();
    let R_size = right_num_vars.pow2();
    assert_eq!(L_size * R_size, n);

    self.commit_inner(&blinds.blinds, &gens.gens.gens_n)
  }

  pub fn bound(&self, L: &[Scalar]) -> Vec<Scalar> {
    let (left_num_vars, right_num_vars) = EqPolynomial::compute_factored_lens(self.get_num_vars());
    let L_size = left_num_vars.pow2();
    let R_size = right_num_vars.pow2();
    (0..R_size)
      .map(|i| (0..L_size).map(|j| L[j] * self.Z[j * R_size + i]).sum())
      .collect()
  }

  pub fn bound_poly_var_top(&mut self, r: &Scalar) {
    let n = self.len() / 2;
    for i in 0..n {
      self.Z[i] = self.Z[i] + r * (self.Z[i + n] - self.Z[i]);
    }
    self.Z.truncate(n); // Resize the vector Z to the new length
    self.num_vars -= 1;
    self.len = n;
  }

  // Bound_var_top but the polynomial is in (x, q, p) form and certain (p, q) pair is invalid
  pub fn bound_poly_var_top_disjoint_rounds(
    &mut self,
    r: &Scalar,
    proof_space: usize,
    instance_space: usize,
    cons_len: usize,
    proof_len: usize,
    instance_len: usize,
    num_proofs: &Vec<usize>,
  ) {
    let n = self.len() / 2;
    assert_eq!(n, cons_len * proof_len * instance_len);

    for p in 0..instance_len {
      // Certain p, q combinations within the boolean hypercube always evaluate to 0
      let max_q = if proof_len != proof_space {
        proof_len
      } else {
        num_proofs[p]
      };
      for q in 0..max_q {
        for x in 0..cons_len {
          let i = x * proof_space * instance_space + q * instance_space + p;
          self.Z[i] = self.Z[i] + r * (self.Z[i + n] - self.Z[i]);
        }
      }
    }
    self.num_vars -= 1;
    self.len = n;
  }

  // The polynomial is in (q, p, x) form and certain (p, q) pair is invalid
  // Binding the entire "q" section and q is in reverse order
  // Use "num_proofs" to record how many "q"s need to process for each "p"
  pub fn bound_poly_var_front_rq(
    &mut self,
    r_q: &Vec<Scalar>,
    mut max_proof_space: usize,
    instance_space: usize,
    cons_space: usize,
    mut num_proofs: Vec<usize>,
  ) {
    let mut n = self.len();
    assert_eq!(n, max_proof_space * instance_space * cons_space);

    for r in r_q {
      n /= 2;
      max_proof_space /= 2;

      for p in 0..instance_space {
        if num_proofs[p] == 1 {
          // q = 0
          for x in 0..cons_space {
            let i = p * cons_space + x;
            self.Z[i] = (Scalar::one() - r) * self.Z[i];
          }
        } else {
          num_proofs[p] /= 2;
          let step = max_proof_space / num_proofs[p];
          for q in (0..max_proof_space).step_by(step) {
            for x in 0..cons_space {
              let i = q * instance_space * cons_space + p * cons_space + x;
              self.Z[i] = self.Z[i] + r * (self.Z[i + n] - self.Z[i]);
            }
          }
        }
      }
      self.num_vars -= 1;
      self.len = n;
    }
  }

  pub fn bound_poly_var_bot(&mut self, r: &Scalar) {
    let n = self.len() / 2;
    for i in 0..n {
      self.Z[i] = self.Z[2 * i] + r * (self.Z[2 * i + 1] - self.Z[2 * i]);
    }
    self.Z.truncate(n); // Resize the vector Z to the new length
    self.num_vars -= 1;
    self.len = n;
  }

  // returns Z(r) in O(n) time
  pub fn evaluate(&self, r: &[Scalar]) -> Scalar {
    // r must have a value for each variable
    assert_eq!(r.len(), self.get_num_vars());
    let chis = EqPolynomial::new(r.to_vec()).evals();
    assert_eq!(chis.len(), self.Z.len());
    DotProductProofLog::compute_dotproduct(&self.Z, &chis)
  }

  fn vec(&self) -> &Vec<Scalar> {
    &self.Z
  }

  pub fn extend(&mut self, other: &DensePolynomial) {
    // TODO: allow extension even when some vars are bound
    assert_eq!(self.Z.len(), self.len);
    let other_vec = other.vec();
    assert_eq!(other_vec.len(), self.len);
    self.Z.extend(other_vec);
    self.num_vars += 1;
    self.len *= 2;
    assert_eq!(self.Z.len(), self.len);
  }

  pub fn merge<'a, I>(polys: I) -> DensePolynomial
  where
    I: IntoIterator<Item = &'a DensePolynomial>,
  {
    let mut Z: Vec<Scalar> = Vec::new();
    for poly in polys.into_iter() {
      Z.extend(poly.vec());
    }

    // pad the polynomial with zero polynomial at the end
    Z.resize(Z.len().next_power_of_two(), Scalar::zero());

    DensePolynomial::new(Z)
  }

  pub fn from_usize(Z: &[usize]) -> Self {
    DensePolynomial::new(
      (0..Z.len())
        .map(|i| Scalar::from(Z[i] as u64))
        .collect::<Vec<Scalar>>(),
    )
  }
}

impl Index<usize> for DensePolynomial {
  type Output = Scalar;

  #[inline(always)]
  fn index(&self, _index: usize) -> &Scalar {
    &(self.Z[_index])
  }
}

impl AppendToTranscript for PolyCommitment {
  fn append_to_transcript(&self, label: &'static [u8], transcript: &mut Transcript) {
    transcript.append_message(label, b"poly_commitment_begin");
    for i in 0..self.C.len() {
      transcript.append_point(b"poly_commitment_share", &self.C[i]);
    }
    transcript.append_message(label, b"poly_commitment_end");
  }
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct PolyEvalProof {
  proof: DotProductProofLog,
}

impl PolyEvalProof {
  fn protocol_name() -> &'static [u8] {
    b"polynomial evaluation proof"
  }

  pub fn prove(
    poly: &DensePolynomial,
    blinds_opt: Option<&PolyCommitmentBlinds>,
    r: &[Scalar],                  // point at which the polynomial is evaluated
    Zr: &Scalar,                   // evaluation of \widetilde{Z}(r)
    blind_Zr_opt: Option<&Scalar>, // specifies a blind for Zr
    gens: &PolyCommitmentGens,
    transcript: &mut Transcript,
    random_tape: &mut RandomTape,
  ) -> (PolyEvalProof, CompressedGroup) {
    transcript.append_protocol_name(PolyEvalProof::protocol_name());

    // assert vectors are of the right size
    assert_eq!(poly.get_num_vars(), r.len());

    let (left_num_vars, right_num_vars) = EqPolynomial::compute_factored_lens(r.len());
    let L_size = left_num_vars.pow2();
    let R_size = right_num_vars.pow2();

    let default_blinds = PolyCommitmentBlinds {
      blinds: vec![Scalar::zero(); L_size],
    };
    let blinds = blinds_opt.map_or(&default_blinds, |p| p);

    assert_eq!(blinds.blinds.len(), L_size);

    let zero = Scalar::zero();
    let blind_Zr = blind_Zr_opt.map_or(&zero, |p| p);

    // compute the L and R vectors
    let eq = EqPolynomial::new(r.to_vec());
    let (L, R) = eq.compute_factored_evals();
    assert_eq!(L.len(), L_size);
    assert_eq!(R.len(), R_size);

    // compute the vector underneath L*Z and the L*blinds
    // compute vector-matrix product between L and Z viewed as a matrix
    let LZ = poly.bound(&L);
    let LZ_blind: Scalar = (0..L.len()).map(|i| blinds.blinds[i] * L[i]).sum();

    // a dot product proof of size R_size
    let (proof, _C_LR, C_Zr_prime) = DotProductProofLog::prove(
      &gens.gens,
      transcript,
      random_tape,
      &LZ,
      &LZ_blind,
      &R,
      Zr,
      blind_Zr,
    );

    (PolyEvalProof { proof }, C_Zr_prime)
  }

  pub fn verify(
    &self,
    gens: &PolyCommitmentGens,
    transcript: &mut Transcript,
    r: &[Scalar],           // point at which the polynomial is evaluated
    C_Zr: &CompressedGroup, // commitment to \widetilde{Z}(r)
    comm: &PolyCommitment,
  ) -> Result<(), ProofVerifyError> {
    transcript.append_protocol_name(PolyEvalProof::protocol_name());

    // compute L and R
    let eq = EqPolynomial::new(r.to_vec());
    let (L, R) = eq.compute_factored_evals();

    // compute a weighted sum of commitments and L
    let C_decompressed = comm.C.iter().map(|pt| pt.decompress().unwrap());

    let C_LZ = GroupElement::vartime_multiscalar_mul(&L, C_decompressed).compress();

    self
      .proof
      .verify(R.len(), &gens.gens, transcript, &R, &C_LZ, C_Zr)
  }

  pub fn verify_plain(
    &self,
    gens: &PolyCommitmentGens,
    transcript: &mut Transcript,
    r: &[Scalar], // point at which the polynomial is evaluated
    Zr: &Scalar,  // evaluation \widetilde{Z}(r)
    comm: &PolyCommitment,
  ) -> Result<(), ProofVerifyError> {
    // compute a commitment to Zr with a blind of zero
    let C_Zr = Zr.commit(&Scalar::zero(), &gens.gens.gens_1).compress();

    self.verify(gens, transcript, r, &C_Zr, comm)
  }

  // Evaluation of multiple points on the same instance
  pub fn prove_batched_points(
    poly: &DensePolynomial,
    blinds_opt: Option<&PolyCommitmentBlinds>,
    r_list: Vec<Vec<Scalar>>, // point at which the polynomial is evaluated
    Zr_list: Vec<Scalar>,     // evaluation of \widetilde{Z}(r) on each point
    blind_Zr_opt: Option<&Scalar>, // specifies a blind for Zr
    gens: &PolyCommitmentGens,
    transcript: &mut Transcript,
    random_tape: &mut RandomTape,
  ) -> Vec<PolyEvalProof> {
    transcript.append_protocol_name(PolyEvalProof::protocol_name());

    // assert vectors are of the right size
    assert_eq!(r_list.len(), Zr_list.len());
    for r in &r_list {
      assert_eq!(poly.get_num_vars(), r.len());
    }

    let (left_num_vars, right_num_vars) = EqPolynomial::compute_factored_lens(r_list[0].len());
    let L_size = left_num_vars.pow2();
    let R_size = right_num_vars.pow2();

    let default_blinds = PolyCommitmentBlinds {
      blinds: vec![Scalar::zero(); L_size],
    };
    let blinds = blinds_opt.map_or(&default_blinds, |p| p);

    assert_eq!(blinds.blinds.len(), L_size);

    let zero = Scalar::zero();
    let blind_Zr = blind_Zr_opt.map_or(&zero, |p| p);

    // compute the L and R vectors
    // We can perform batched opening if L is the same, so we regroup the proofs by L vector
    // Map from the left half of the r to index in L_list
    let mut index_map: HashMap<Vec<Scalar>, usize> = HashMap::new();
    let mut L_list: Vec<Vec<Scalar>> = Vec::new();
    let mut R_list: Vec<Vec<Scalar>> = Vec::new();
    let mut Zc_list: Vec<Scalar> = Vec::new();

    let c_base = transcript.challenge_scalar(b"challenge_c");
    let mut c = Scalar::one();
    for i in 0..r_list.len() {
      let eq = EqPolynomial::new(r_list[i].to_vec());
      let (Li, Ri) = eq.compute_factored_evals();
      assert_eq!(Li.len(), L_size);
      assert_eq!(Ri.len(), R_size);
      if let Some(index) = index_map.get(&r_list[i][..left_num_vars]) {
        // L already exist
        // generate coefficient for RLC
        c *= c_base;
        R_list[*index] = (0..R_size).map(|j| R_list[*index][j] + c * Ri[j]).collect();
        Zc_list[*index] += c * Zr_list[i];
      } else {
        let next_index = L_list.len();
        index_map.insert(r_list[i][..left_num_vars].to_vec(), next_index);
        L_list.push(Li);
        R_list.push(Ri);
        Zc_list.push(Zr_list[i]);
      }
    }

    let mut proof_list = Vec::new();
    for i in 0..L_list.len() {
      let L = &L_list[i];
      let R = &R_list[i];
      // compute the vector underneath L*Z and the L*blinds
      // compute vector-matrix product between L and Z viewed as a matrix
      let LZ = poly.bound(L);
      let LZ_blind: Scalar = (0..L.len()).map(|i| blinds.blinds[i] * L[i]).sum();

      // a dot product proof of size R_size
      let (proof, _C_LR, _C_Zr_prime) = DotProductProofLog::prove(
        &gens.gens,
        transcript,
        random_tape,
        &LZ,
        &LZ_blind,
        &R,
        &Zc_list[i],
        blind_Zr,
      );
      proof_list.push(proof);
    }

    proof_list
      .iter()
      .map(|proof| PolyEvalProof {
        proof: proof.clone(),
      })
      .collect()
  }

  pub fn verify_plain_batched_points(
    proof_list: &Vec<PolyEvalProof>,
    gens: &PolyCommitmentGens,
    transcript: &mut Transcript,
    r_list: Vec<Vec<Scalar>>, // point at which the polynomial is evaluated
    Zr_list: Vec<Scalar>,     // commitment to \widetilde{Z}(r) on each point
    comm: &PolyCommitment,
  ) -> Result<(), ProofVerifyError> {
    transcript.append_protocol_name(PolyEvalProof::protocol_name());

    let (left_num_vars, _) = EqPolynomial::compute_factored_lens(r_list[0].len());

    // compute the L and R
    // We can perform batched opening if L is the same, so we regroup the proofs by L vector
    // Map from the left half of the r to index in L_list
    let mut index_map: HashMap<Vec<Scalar>, usize> = HashMap::new();
    let mut L_list: Vec<Vec<Scalar>> = Vec::new();
    let mut R_list: Vec<Vec<Scalar>> = Vec::new();
    let mut Zc_list: Vec<Scalar> = Vec::new();

    let c_base = transcript.challenge_scalar(b"challenge_c");
    let mut c = Scalar::one();
    for i in 0..r_list.len() {
      let eq = EqPolynomial::new(r_list[i].to_vec());
      let (Li, Ri) = eq.compute_factored_evals();
      if let Some(index) = index_map.get(&r_list[i][..left_num_vars]) {
        // L already exist
        // generate coefficient for RLC
        c *= c_base;
        R_list[*index] = (0..Ri.len())
          .map(|j| R_list[*index][j] + c * Ri[j])
          .collect();
        Zc_list[*index] += c * Zr_list[i];
      } else {
        let next_index = L_list.len();
        index_map.insert(r_list[i][..left_num_vars].to_vec(), next_index);
        L_list.push(Li);
        R_list.push(Ri);
        Zc_list.push(Zr_list[i]);
      }
    }
    assert_eq!(L_list.len(), proof_list.len());

    for i in 0..L_list.len() {
      let C_Zc = Zc_list[i]
        .commit(&Scalar::zero(), &gens.gens.gens_1)
        .compress();
      let L = &L_list[i];
      let R = &R_list[i];

      // compute a weighted sum of commitments and L
      let C_decompressed = comm.C.iter().map(|pt| pt.decompress().unwrap());

      let C_LZ = GroupElement::vartime_multiscalar_mul(L, C_decompressed).compress();

      proof_list[i]
        .proof
        .verify(R.len(), &gens.gens, transcript, &R, &C_LZ, &C_Zc)?
    }

    Ok(())
  }

  // Evaluation on multiple instances, each at different point
  // Size of each instance might be different, but all are larger than the evaluation point
  pub fn prove_batched_instances(
    poly_list: &Vec<DensePolynomial>, // list of instances
    blinds_opt: Option<&PolyCommitmentBlinds>,
    r_list: Vec<&Vec<Scalar>>, // point at which the polynomial is evaluated
    Zr_list: &Vec<Scalar>,     // evaluation of \widetilde{Z}(r) on each instance
    blind_Zr_opt: Option<&Scalar>, // specifies a blind for Zr
    gens: &PolyCommitmentGens,
    transcript: &mut Transcript,
    random_tape: &mut RandomTape,
  ) -> Vec<PolyEvalProof> {
    transcript.append_protocol_name(PolyEvalProof::protocol_name());
    // assert vectors are of the right size
    assert_eq!(poly_list.len(), r_list.len());
    assert_eq!(poly_list.len(), Zr_list.len());

    // We need one proof per poly size & R
    let mut index_map: HashMap<(usize, Vec<Scalar>), usize> = HashMap::new();
    let mut LZ_list: Vec<Vec<Scalar>> = Vec::new();
    let mut Zc_list = Vec::new();
    let mut L_list: Vec<Vec<Scalar>> = Vec::new();
    let mut R_list: Vec<Vec<Scalar>> = Vec::new();

    // generate coefficient for RLC
    let c_base = transcript.challenge_scalar(b"challenge_c");
    let mut c = Scalar::one();
    let zero = Scalar::zero();
    for i in 0..poly_list.len() {
      let poly = &poly_list[i];
      let num_vars = poly.get_num_vars();

      // compute L and R
      let (L, R) = {
        let r = r_list[i];
        // pad or trim r to correct length
        let r = {
          if num_vars >= r.len() {
            [vec![zero; num_vars - r.len()], r.to_vec()].concat()
          } else {
            r[r.len() - num_vars..].to_vec()
          }
        };
        let eq = EqPolynomial::new(r);
        eq.compute_factored_evals()
      };

      if let Some(index) = index_map.get(&(num_vars, R.clone())) {
        c *= c_base;
        let LZ = poly.bound(&L);
        LZ_list[*index] = (0..LZ.len())
          .map(|j| LZ_list[*index][j] + c * LZ[j])
          .collect();
        Zc_list[*index] += c * Zr_list[i];
      } else {
        index_map.insert((num_vars, R.clone()), LZ_list.len());
        Zc_list.push(Zr_list[i]);
        // compute a weighted sum of commitments and L
        let LZ = poly.bound(&L);
        L_list.push(L);
        R_list.push(R);
        LZ_list.push(LZ);
      }
    }

    let mut proof_list = Vec::new();
    for i in 0..LZ_list.len() {
      let L = &L_list[i];
      let L_size = L.len();

      let default_blinds = PolyCommitmentBlinds {
        blinds: vec![Scalar::zero(); L_size],
      };
      let blinds = blinds_opt.map_or(&default_blinds, |p| p);
      assert_eq!(blinds.blinds.len(), L_size);
      let blind_Zr = blind_Zr_opt.map_or(&zero, |p| p);
      let LZ_blind: Scalar = (0..L.len()).map(|i| blinds.blinds[i] * L[i]).sum();

      // a dot product proof of size R_size
      let (proof, _C_LR, _C_Zr_prime) = DotProductProofLog::prove(
        &gens.gens,
        transcript,
        random_tape,
        &LZ_list[i],
        &LZ_blind,
        &R_list[i],
        &Zc_list[i],
        blind_Zr,
      );
      proof_list.push(PolyEvalProof { proof });
    }

    proof_list
  }

  pub fn verify_plain_batched_instances(
    proof_list: &Vec<PolyEvalProof>,
    gens: &PolyCommitmentGens,
    transcript: &mut Transcript,
    r_list: Vec<&Vec<Scalar>>, // point at which the polynomial is evaluated
    Zr_list: &Vec<Scalar>,     // commitment to \widetilde{Z}(r) of each instance
    comm_list: &Vec<PolyCommitment>, // commitment of each instance
    num_vars_list: &Vec<usize>, // size of each polynomial
  ) -> Result<(), ProofVerifyError> {
    transcript.append_protocol_name(PolyEvalProof::protocol_name());
    assert_eq!(comm_list.len(), r_list.len());

    // We need one proof per poly size + L size
    let mut index_map: HashMap<(usize, Vec<Scalar>), usize> = HashMap::new();
    let mut LZ_list: Vec<RistrettoPoint> = Vec::new();
    let mut Zc_list = Vec::new();
    let mut L_list: Vec<Vec<Scalar>> = Vec::new();
    let mut R_list: Vec<Vec<Scalar>> = Vec::new();

    // generate coefficient for RLC
    let c_base = transcript.challenge_scalar(b"challenge_c");
    let mut c = Scalar::one();
    let zero = Scalar::zero();
    for i in 0..comm_list.len() {
      let C_decompressed: Vec<RistrettoPoint> = comm_list[i]
        .C
        .iter()
        .map(|pt| pt.decompress().unwrap())
        .collect();
      let num_vars = num_vars_list[i];

      // compute L and R
      let (L, R) = {
        let r = r_list[i];
        // pad or trim r to correct length
        let r = {
          if num_vars >= r.len() {
            [vec![zero; num_vars - r.len()], r.to_vec()].concat()
          } else {
            r[r.len() - num_vars..].to_vec()
          }
        };
        let eq = EqPolynomial::new(r);
        eq.compute_factored_evals()
      };

      if let Some(index) = index_map.get(&(num_vars, R.clone())) {
        c *= c_base;
        let LZ = GroupElement::vartime_multiscalar_mul(L, &C_decompressed);
        LZ_list[*index] += c * LZ;
        Zc_list[*index] += c * Zr_list[i];
      } else {
        index_map.insert((num_vars, R.clone()), LZ_list.len());
        Zc_list.push(Zr_list[i]);
        // compute a weighted sum of commitments and L
        let LZ = GroupElement::vartime_multiscalar_mul(&L, &C_decompressed);
        L_list.push(L);
        R_list.push(R);
        LZ_list.push(LZ);
      }
    }
    assert_eq!(LZ_list.len(), proof_list.len());

    // Verify proofs
    for i in 0..LZ_list.len() {
      let R = &R_list[i];
      let C_LZ = LZ_list[i].compress();
      let C_Zc = Zc_list[i]
        .commit(&Scalar::zero(), &gens.gens.gens_1)
        .compress();
      proof_list[i]
        .proof
        .verify(R.len(), &gens.gens, transcript, R, &C_LZ, &C_Zc)?;
    }
    Ok(())
  }

  // Like prove_batched_instances, but r is divided into rq ++ ry
  // Each polynomial is supplemented with num_proofs and num_inputs
  pub fn prove_batched_instances_disjoint_rounds(
    poly_list: &Vec<&DensePolynomial>,
    num_proofs_list: &Vec<usize>,
    num_inputs_list: &Vec<usize>,
    blinds_opt: Option<&PolyCommitmentBlinds>,
    rq: &[Scalar],
    ry: &[Scalar],
    Zr_list: &Vec<Scalar>,
    blind_Zr_opt: Option<&Scalar>,
    gens: &PolyCommitmentGens,
    transcript: &mut Transcript,
    random_tape: &mut RandomTape,
  ) -> Vec<PolyEvalProof> {
    transcript.append_protocol_name(PolyEvalProof::protocol_name());
    // assert vectors are of the right size
    assert_eq!(poly_list.len(), Zr_list.len());

    // We need one proof per (num_proofs, num_inputs) pair
    let mut index_map: HashMap<(usize, usize), usize> = HashMap::new();
    let mut LZ_list: Vec<Vec<Scalar>> = Vec::new();
    let mut Zc_list = Vec::new();
    let mut L_list: Vec<Vec<Scalar>> = Vec::new();
    let mut R_list = Vec::new();

    // generate coefficient for RLC
    let c_base = transcript.challenge_scalar(b"challenge_c");
    let mut c = Scalar::one();
    let zero = Scalar::zero();
    for i in 0..poly_list.len() {
      let poly = poly_list[i];
      let num_proofs = num_proofs_list[i];
      let num_inputs = num_inputs_list[i];
      if let Some(index) = index_map.get(&(num_proofs, num_inputs)) {
        c *= c_base;
        let L = &L_list[*index].to_vec();
        let LZ = poly.bound(&L);
        LZ_list[*index] = (0..LZ.len())
          .map(|j| LZ_list[*index][j] + c * LZ[j])
          .collect();
        Zc_list[*index] += c * Zr_list[i];
      } else {
        index_map.insert((num_proofs, num_inputs), LZ_list.len());
        Zc_list.push(Zr_list[i]);
        let num_vars_q = num_proofs.log_2();
        let num_vars_y = num_inputs.log_2();
        // pad or trim rq and ry to correct length
        let (L, R) = {
          let ry_short = {
            if num_vars_y >= ry.len() {
              let ry_pad = &vec![zero; num_vars_y - ry.len()];
              [ry_pad, ry].concat()
            }
            // Else ry_short is the last w.num_inputs[p].log_2() entries of ry
            // thus, to obtain the actual ry, need to multiply by (1 - ry2)(1 - ry3)..., which is ry_factors[num_rounds_y - w.num_inputs[p]]
            else {
              ry[ry.len() - num_vars_y..].to_vec()
            }
          };
          let rq_short = rq[rq.len() - num_vars_q..].to_vec();
          let r = [rq_short, ry_short.clone()].concat();
          let eq = EqPolynomial::new(r);
          eq.compute_factored_evals()
        };
        // compute a weighted sum of commitments and L
        let LZ = poly.bound(&L);
        L_list.push(L);
        R_list.push(R);
        LZ_list.push(LZ);
      }
    }

    let mut proof_list = Vec::new();
    for i in 0..LZ_list.len() {
      let L = &L_list[i];
      let L_size = L.len();
      let default_blinds = PolyCommitmentBlinds {
        blinds: vec![Scalar::zero(); L_size],
      };
      let blinds = blinds_opt.map_or(&default_blinds, |p| p);

      assert_eq!(blinds.blinds.len(), L_size);

      let blind_Zr = blind_Zr_opt.map_or(&zero, |p| p);
      let LZ_blind: Scalar = (0..L.len()).map(|i| blinds.blinds[i] * L[i]).sum();

      // a dot product proof of size R_size
      let (proof, _C_LR, _C_Zr_prime) = DotProductProofLog::prove(
        &gens.gens,
        transcript,
        random_tape,
        &LZ_list[i],
        &LZ_blind,
        &R_list[i],
        &Zc_list[i],
        blind_Zr,
      );
      proof_list.push(PolyEvalProof { proof });
    }
    proof_list
  }

  pub fn verify_batched_instances_disjoint_rounds(
    proof_list: &Vec<PolyEvalProof>,
    num_proofs_list: &Vec<usize>,
    num_inputs_list: &Vec<usize>,
    gens: &PolyCommitmentGens,
    transcript: &mut Transcript,
    rq: &[Scalar],
    ry: &[Scalar],
    Zr_list: &Vec<RistrettoPoint>,
    comm_list: &Vec<&PolyCommitment>,
  ) -> Result<(), ProofVerifyError> {
    transcript.append_protocol_name(PolyEvalProof::protocol_name());

    // We need one proof per poly size
    let mut index_map: HashMap<(usize, usize), usize> = HashMap::new();
    let mut LZ_list: Vec<RistrettoPoint> = Vec::new();
    let mut Zc_list = Vec::new();
    let mut L_list = Vec::new();
    let mut R_list = Vec::new();

    // generate coefficient for RLC
    let c_base = transcript.challenge_scalar(b"challenge_c");
    let mut c = Scalar::one();
    let zero = Scalar::zero();
    for i in 0..comm_list.len() {
      let C_decompressed: Vec<RistrettoPoint> = comm_list[i]
        .C
        .iter()
        .map(|pt| pt.decompress().unwrap())
        .collect();
      let num_proofs = num_proofs_list[i];
      let num_inputs = num_inputs_list[i];
      if let Some(index) = index_map.get(&(num_proofs, num_inputs)) {
        c *= c_base;
        let L = &L_list[*index];
        let LZ = GroupElement::vartime_multiscalar_mul(L, &C_decompressed);
        LZ_list[*index] += c * LZ;
        Zc_list[*index] += c * Zr_list[i];
      } else {
        index_map.insert((num_proofs, num_inputs), LZ_list.len());
        Zc_list.push(Zr_list[i]);
        let num_vars_q = num_proofs.log_2();
        let num_vars_y = num_inputs.log_2();
        // pad or trim rq and ry to correct length
        let (L, R) = {
          let ry_short = {
            if num_vars_y >= ry.len() {
              let ry_pad = &vec![zero; num_vars_y - ry.len()];
              [ry_pad, ry].concat()
            }
            // Else ry_short is the last w.num_inputs[p].log_2() entries of ry
            // thus, to obtain the actual ry, need to multiply by (1 - ry2)(1 - ry3)..., which is ry_factors[num_rounds_y - w.num_inputs[p]]
            else {
              ry[ry.len() - num_vars_y..].to_vec()
            }
          };
          let rq_short = rq[rq.len() - num_vars_q..].to_vec();
          let r = [rq_short, ry_short.clone()].concat();
          let eq = EqPolynomial::new(r);
          eq.compute_factored_evals()
        };
        // compute a weighted sum of commitments and L
        let LZ = GroupElement::vartime_multiscalar_mul(&L, &C_decompressed);
        L_list.push(L);
        R_list.push(R);
        LZ_list.push(LZ);
      }
    }
    assert_eq!(LZ_list.len(), proof_list.len());

    // Verify proofs
    for i in 0..LZ_list.len() {
      let R = &R_list[i];
      let C_LZ = LZ_list[i].compress();
      let C_Zc = Zc_list[i].compress();
      proof_list[i]
        .proof
        .verify(R.len(), &gens.gens, transcript, R, &C_LZ, &C_Zc)?;
    }

    Ok(())
  }

  // Treat the polynomial(s) as univariate and open on a single point
  pub fn prove_uni_batched_instances(
    poly_list: &Vec<&DensePolynomial>,
    r: &Scalar,       // point at which the polynomial is evaluated
    Zr: &Vec<Scalar>, // evaluation of \widetilde{Z}(r)
    gens: &PolyCommitmentGens,
    transcript: &mut Transcript,
    random_tape: &mut RandomTape,
  ) -> (PolyEvalProof, CompressedGroup) {
    transcript.append_protocol_name(PolyEvalProof::protocol_name());

    let max_num_vars = poly_list.iter().fold(0, |m, p| {
      if p.get_num_vars() > m {
        p.get_num_vars()
      } else {
        m
      }
    });
    let zero = Scalar::zero();

    // L differs depending on size of the polynomial, but R always stay the same
    let (_, right_num_vars) = EqPolynomial::compute_factored_lens(max_num_vars);
    let R_size = right_num_vars.pow2();

    // compute R = <1, r, r^2, ...>
    let R = {
      let mut r_base = Scalar::one();
      let mut R = Vec::new();
      for _ in 0..R_size {
        R.push(r_base);
        r_base *= r;
      }
      R
    };
    let mut L_map: HashMap<usize, Vec<Scalar>> = HashMap::new();

    // compute the vector underneath L*Z
    // compute vector-matrix product between L and Z viewed as a matrix
    let c_base = transcript.challenge_scalar(b"challenge_c");
    let mut c = Scalar::one();
    let mut LZ_comb = vec![zero; R_size];
    let mut Zr_comb = zero;

    for i in 0..poly_list.len() {
      let poly = &poly_list[i];
      let num_vars = poly.get_num_vars();
      let L = if let Some(L) = L_map.get(&num_vars) {
        L
      } else {
        let (left_num_vars, right_num_vars) = EqPolynomial::compute_factored_lens(num_vars);
        let L_size = left_num_vars.pow2();
        let R_size = right_num_vars.pow2();
        let r_base = (0..R_size).fold(Scalar::one(), |p, _| p * r);
        // L is 1, r^k, r^2k, ...
        let mut l_base = Scalar::one();
        let mut L = Vec::new();
        for _ in 0..L_size {
          L.push(l_base);
          l_base *= r_base;
        }
        L_map.insert(num_vars, L.clone());
        L_map.get(&num_vars).unwrap()
      };

      let LZ = poly.bound(&L);
      LZ_comb = (0..R_size)
        .map(|i| LZ_comb[i] + if i < LZ.len() { c * LZ[i] } else { zero })
        .collect();
      Zr_comb += c * Zr[i];
      c *= c_base;
    }

    // a dot product proof of size R_size
    let (proof, _C_LR, C_Zr_prime) = DotProductProofLog::prove(
      &gens.gens,
      transcript,
      random_tape,
      &LZ_comb,
      &zero,
      &R,
      &Zr_comb,
      &zero,
    );

    (PolyEvalProof { proof }, C_Zr_prime)
  }

  pub fn verify_uni_batched_instances(
    &self,
    gens: &PolyCommitmentGens,
    transcript: &mut Transcript,
    r: &Scalar,                 // point at which the polynomial is evaluated
    C_Zr: &Vec<RistrettoPoint>, // commitment to \widetilde{Z}(r)
    comm_list: &Vec<&PolyCommitment>,
    poly_size: Vec<usize>,
  ) -> Result<(), ProofVerifyError> {
    transcript.append_protocol_name(PolyEvalProof::protocol_name());

    let max_poly_size = poly_size.iter().fold(0, |m, i| if *i > m { *i } else { m });
    // compute L and R
    let (_, right_num_vars) =
      EqPolynomial::compute_factored_lens(max_poly_size.next_power_of_two().log_2());
    let R_size = right_num_vars.pow2();

    // compute R = <1, r, r^2, ...>
    let R = {
      let mut r_base = Scalar::one();
      let mut R = Vec::new();
      for _ in 0..R_size {
        R.push(r_base);
        r_base *= r;
      }
      R
    };
    let mut L_map: HashMap<usize, Vec<Scalar>> = HashMap::new();

    // compute a weighted sum of commitments and L
    let c_base = transcript.challenge_scalar(b"challenge_c");
    let mut c = Scalar::one();
    let mut C_LZ_comb = Scalar::zero().commit(&Scalar::zero(), &gens.gens.gens_1);
    let mut C_Zr_comb = Scalar::zero().commit(&Scalar::zero(), &gens.gens.gens_1);

    for i in 0..comm_list.len() {
      let comm = comm_list[i];
      let num_vars = poly_size[i].next_power_of_two().log_2();
      let L = if let Some(L) = L_map.get(&num_vars) {
        L
      } else {
        let (left_num_vars, right_num_vars) = EqPolynomial::compute_factored_lens(num_vars);
        let L_size = left_num_vars.pow2();
        let R_size = right_num_vars.pow2();
        let r_base = (0..R_size).fold(Scalar::one(), |p, _| p * r);
        // L is 1, r^k, r^2k, ...
        let mut l_base = Scalar::one();
        let mut L = Vec::new();
        for _ in 0..L_size {
          L.push(l_base);
          l_base *= r_base;
        }
        L_map.insert(num_vars, L.clone());
        L_map.get(&num_vars).unwrap()
      };

      let C_decompressed = comm.C.iter().map(|pt| pt.decompress().unwrap());
      let C_LZ = GroupElement::vartime_multiscalar_mul(L, C_decompressed);
      C_LZ_comb += c * C_LZ;
      C_Zr_comb += c * C_Zr[i];
      c *= c_base;
    }

    self.proof.verify(
      R.len(),
      &gens.gens,
      transcript,
      &R,
      &C_LZ_comb.compress(),
      &C_Zr_comb.compress(),
    )
  }
}

#[cfg(test)]
mod tests {
  use super::super::scalar::ScalarFromPrimitives;
  use super::*;
  use rand::rngs::OsRng;

  fn evaluate_with_LR(Z: &[Scalar], r: &[Scalar]) -> Scalar {
    let eq = EqPolynomial::new(r.to_vec());
    let (L, R) = eq.compute_factored_evals();

    let ell = r.len();
    // ensure ell is even
    assert!(ell % 2 == 0);
    // compute n = 2^\ell
    let n = ell.pow2();
    // compute m = sqrt(n) = 2^{\ell/2}
    let m = (n as f64).sqrt() as usize;

    // compute vector-matrix product between L and Z viewed as a matrix
    let LZ = (0..m)
      .map(|i| (0..m).map(|j| L[j] * Z[j * m + i]).sum())
      .collect::<Vec<Scalar>>();

    // compute dot product between LZ and R
    DotProductProofLog::compute_dotproduct(&LZ, &R)
  }

  #[test]
  fn check_polynomial_evaluation() {
    // Z = [1, 2, 1, 4]
    let Z = vec![
      Scalar::one(),
      (2_usize).to_scalar(),
      (1_usize).to_scalar(),
      (4_usize).to_scalar(),
    ];

    // r = [4,3]
    let r = vec![(4_usize).to_scalar(), (3_usize).to_scalar()];

    let eval_with_LR = evaluate_with_LR(&Z, &r);
    let poly = DensePolynomial::new(Z);

    let eval = poly.evaluate(&r);
    assert_eq!(eval, (28_usize).to_scalar());
    assert_eq!(eval_with_LR, eval);
  }

  pub fn compute_factored_chis_at_r(r: &[Scalar]) -> (Vec<Scalar>, Vec<Scalar>) {
    let mut L: Vec<Scalar> = Vec::new();
    let mut R: Vec<Scalar> = Vec::new();

    let ell = r.len();
    assert!(ell % 2 == 0); // ensure ell is even
    let n = ell.pow2();
    let m = (n as f64).sqrt() as usize;

    // compute row vector L
    for i in 0..m {
      let mut chi_i = Scalar::one();
      for j in 0..ell / 2 {
        let bit_j = ((m * i) & (1 << (r.len() - j - 1))) > 0;
        if bit_j {
          chi_i *= r[j];
        } else {
          chi_i *= Scalar::one() - r[j];
        }
      }
      L.push(chi_i);
    }

    // compute column vector R
    for i in 0..m {
      let mut chi_i = Scalar::one();
      for j in ell / 2..ell {
        let bit_j = (i & (1 << (r.len() - j - 1))) > 0;
        if bit_j {
          chi_i *= r[j];
        } else {
          chi_i *= Scalar::one() - r[j];
        }
      }
      R.push(chi_i);
    }
    (L, R)
  }

  pub fn compute_chis_at_r(r: &[Scalar]) -> Vec<Scalar> {
    let ell = r.len();
    let n = ell.pow2();
    let mut chis: Vec<Scalar> = Vec::new();
    for i in 0..n {
      let mut chi_i = Scalar::one();
      for j in 0..r.len() {
        let bit_j = (i & (1 << (r.len() - j - 1))) > 0;
        if bit_j {
          chi_i *= r[j];
        } else {
          chi_i *= Scalar::one() - r[j];
        }
      }
      chis.push(chi_i);
    }
    chis
  }

  pub fn compute_outerproduct(L: Vec<Scalar>, R: Vec<Scalar>) -> Vec<Scalar> {
    assert_eq!(L.len(), R.len());
    (0..L.len())
      .map(|i| (0..R.len()).map(|j| L[i] * R[j]).collect::<Vec<Scalar>>())
      .collect::<Vec<Vec<Scalar>>>()
      .into_iter()
      .flatten()
      .collect::<Vec<Scalar>>()
  }

  #[test]
  fn check_memoized_chis() {
    let mut csprng: OsRng = OsRng;

    let s = 10;
    let mut r: Vec<Scalar> = Vec::new();
    for _i in 0..s {
      r.push(Scalar::random(&mut csprng));
    }
    let chis = tests::compute_chis_at_r(&r);
    let chis_m = EqPolynomial::new(r).evals();
    assert_eq!(chis, chis_m);
  }

  #[test]
  fn check_factored_chis() {
    let mut csprng: OsRng = OsRng;

    let s = 10;
    let mut r: Vec<Scalar> = Vec::new();
    for _i in 0..s {
      r.push(Scalar::random(&mut csprng));
    }
    let chis = EqPolynomial::new(r.clone()).evals();
    let (L, R) = EqPolynomial::new(r).compute_factored_evals();
    let O = compute_outerproduct(L, R);
    assert_eq!(chis, O);
  }

  #[test]
  fn check_memoized_factored_chis() {
    let mut csprng: OsRng = OsRng;

    let s = 10;
    let mut r: Vec<Scalar> = Vec::new();
    for _i in 0..s {
      r.push(Scalar::random(&mut csprng));
    }
    let (L, R) = tests::compute_factored_chis_at_r(&r);
    let eq = EqPolynomial::new(r);
    let (L2, R2) = eq.compute_factored_evals();
    assert_eq!(L, L2);
    assert_eq!(R, R2);
  }

  #[test]
  fn check_polynomial_commit() {
    let Z = vec![
      (1_usize).to_scalar(),
      (2_usize).to_scalar(),
      (1_usize).to_scalar(),
      (4_usize).to_scalar(),
    ];
    let poly = DensePolynomial::new(Z);

    // r = [4,3]
    let r = vec![(4_usize).to_scalar(), (3_usize).to_scalar()];
    let eval = poly.evaluate(&r);
    assert_eq!(eval, (28_usize).to_scalar());

    let gens = PolyCommitmentGens::new(poly.get_num_vars(), b"test-two");
    let (poly_commitment, blinds) = poly.commit(&gens, None);

    let mut random_tape = RandomTape::new(b"proof");
    let mut prover_transcript = Transcript::new(b"example");
    let (proof, C_Zr) = PolyEvalProof::prove(
      &poly,
      Some(&blinds),
      &r,
      &eval,
      None,
      &gens,
      &mut prover_transcript,
      &mut random_tape,
    );

    let mut verifier_transcript = Transcript::new(b"example");
    assert!(proof
      .verify(&gens, &mut verifier_transcript, &r, &C_Zr, &poly_commitment)
      .is_ok());
  }
}
