#![allow(clippy::too_many_arguments)]
use crate::dense_mlpoly::{DensePolynomial, EqPolynomial, PolyCommitmentGens};

use super::commitments::Commitments;
use super::errors::ProofVerifyError;
use super::group::{CompressedGroup, GroupElement, VartimeMultiscalarMul};
use super::math::Math;
use super::nizk::DotProductProofLog;
use super::random::RandomTape;
use super::scalar::Scalar;
use super::transcript::{AppendToTranscript, ProofTranscript};
use merlin::Transcript;
use serde::{Deserialize, Serialize};

// Customized Dense ML Polynomials for Data-Parallelism
// These Dense ML Polys are aimed for space-efficiency by removing the 0s for invalid (p, q) pair

// Dense polynomial with variable order: p, q_rev, x
// Used by Z_poly in r1csproof
#[derive(Debug, Clone)]
pub struct DensePolynomial_PQX {
  num_vars_p: usize,
  num_vars_q: usize,
  num_vars_x: usize,
  num_instances: usize,
  num_proofs: Vec<usize>,
  max_num_proofs: usize,
  num_inputs: usize,
  Z: Vec<Vec<Vec<Scalar>>>, // Evaluations of the polynomial in all the 2^num_vars Boolean inputs of order (p, q_rev, x)
                            // Let Q_max = max_num_proofs, assume that for a given P, num_proofs[P] = Q_i, then let STEP = Q_max / Q_i,
                            // Z(P, y, .) is only non-zero if y is a multiple of STEP, so Z[P][j][.] actually stores Z(P, j*STEP, .)
}

// Reverse the bits in q
fn rev_bits(q: usize, max_num_proofs: usize) -> usize {
    (0..max_num_proofs.log_2()).rev().map(|i| q / (i.pow2()) % 2 * (max_num_proofs / i.pow2() / 2)).fold(0, |a, b| a + b)
}

impl DensePolynomial_PQX {
  // Assume z_mat is of form (p, q_rev, x), construct DensePoly
  pub fn new(z_mat: &Vec<Vec<Vec<Scalar>>>, num_proofs: &Vec<usize>, max_num_proofs: usize) -> Self {
      let num_instances = z_mat.len();
      let num_inputs = z_mat[0][0].len();
      DensePolynomial_PQX {
        num_vars_q: max_num_proofs.log_2(),
        num_vars_p: num_instances.log_2(),
        num_vars_x: num_inputs.log_2(),
        num_instances,
        num_proofs: num_proofs.clone(),
        max_num_proofs,
        num_inputs,
        Z: z_mat.clone()
      }
    }

  // Assume z_mat is in its standard form of (p, q, x) as what a reasonable front end would provide
  // Convert it to (p, q_rev, x)
  pub fn new_rev(z_mat: &Vec<Vec<Vec<Scalar>>>, num_proofs: &Vec<usize>, max_num_proofs: usize) -> Self {
    let mut Z = Vec::new();
    let num_instances = z_mat.len();
    let num_inputs = z_mat[0][0].len();
    for p in 0..num_instances {
      Z.push(vec![Vec::new(); num_proofs[p]]);
      let step = max_num_proofs / num_proofs[p];

      for q in 0..num_proofs[p] {
          // Reverse the bits of q. q_rev is a multiple of step
          let q_rev = rev_bits(q, max_num_proofs);
          // Now q_rev is between 0 to num_proofs[p]
          let q_rev = q_rev / step;
          for x in 0..num_inputs {
              Z[p][q_rev].push(z_mat[p][q][x].clone());
          }
      }
    }
    DensePolynomial_PQX {
      num_vars_q: max_num_proofs.log_2(),
      num_vars_p: num_instances.log_2(),
      num_vars_x: num_inputs.log_2(),
      num_instances,
      num_proofs: num_proofs.clone(),
      max_num_proofs,
      num_inputs,
      Z
    }
  }

  pub fn len(&self) -> usize {
      return self.num_instances * self.max_num_proofs * self.num_inputs;
  }

  pub fn get_num_vars(&self) -> usize {
      return self.num_vars_p + self.num_vars_q + self.num_vars_x;
  }

  // Given (p, q_rev, x) return Z[p][q_rev][x]
  pub fn index(&mut self, p: usize, q_rev: usize, x: usize) -> Scalar {
      return self.Z[p][q_rev][x];
  }

  // Given (p, q_rev, x) and a mode, return Z[p*][q_rev*][x*]
  // Mode = 1 ==> p* is p with first bit set to 1
  // Mode = 2 ==> q_rev* is q_rev with first bit set to 1
  // Mode = 3 ==> x* is x with first bit set to 1
  // Assume that first bit of the corresponding index is 0, otherwise throw out of bound exception
  pub fn index_high(&mut self, p: usize, q_rev: usize, x: usize, mode: usize) -> Scalar {
      match mode {
          1 => { return self.Z[p + self.num_instances / 2][q_rev][x]; }
          2 => { return if self.num_proofs[p] == 1 { Scalar::zero() } else { self.Z[p][q_rev + self.num_proofs[p] / 2][x] }; }
          3 => { return self.Z[p][q_rev][x + self.num_inputs / 2]; }
          _ => { panic!("DensePolynomial_PQX bound failed: unrecognized mode {}!", mode); }
      }
  }

  // Bound a variable to r according to mode
  // Mode = 1 ==> Bound first variable of "p" section to r
  // Mode = 2 ==> Bound first variable of "q" section to r
  // Mode = 3 ==> Bound first variable of "x" section to r
  pub fn bound_poly(&mut self, r: &Scalar, mode: usize) {
      match mode {
          1 => { self.bound_poly_p(r); }
          2 => { self.bound_poly_q(r); }
          3 => { self.bound_poly_x(r); }
          _ => { panic!("DensePolynomial_PQX bound failed: unrecognized mode {}!", mode); }
      }
  }

  // Bound the first variable of "p" section to r
  // We are only allowed to bound "p" if we have bounded the entire q section
  pub fn bound_poly_p(&mut self, r: &Scalar) {
      assert_eq!(self.max_num_proofs, 1);
      self.num_instances /= 2;
      for p in 0..self.num_instances {
          for x in 0..self.num_inputs {
              self.Z[p][0][x] = self.Z[p][0][x] + r * (self.Z[p + self.num_instances][0][x] - self.Z[p][0][x]);
          }
      }
      self.num_vars_p -= 1;
  }

  // Bound the first variable of "q" section to r
  pub fn bound_poly_q(&mut self, r: &Scalar) {
      self.max_num_proofs /= 2;

      for p in 0..self.num_instances {
        if self.num_proofs[p] == 1 {
          // q = 0
          for x in 0..self.num_inputs {
            self.Z[p][0][x] = (Scalar::one() - r) * self.Z[p][0][x];
          }
        } else {
          self.num_proofs[p] /= 2;
          for q in 0..self.num_proofs[p] {
              for x in 0..self.num_inputs {
                  self.Z[p][q][x] = self.Z[p][q][x] + r * (self.Z[p][q + self.num_proofs[p]][x] - self.Z[p][q][x]);
              }
          }
        }
      }
      self.num_vars_q -= 1;
  }

  // Bound the first variable of "x" section to r
  pub fn bound_poly_x(&mut self, r: &Scalar) {
      self.num_inputs /= 2;

      for p in 0..self.num_instances {
          for q in 0..self.num_proofs[p] {
              for x in 0..self.num_inputs {
                  self.Z[p][q][x] = self.Z[p][q][x] + r * (self.Z[p][q][x + self.num_inputs] - self.Z[p][q][x]);
              }
          }
      }
      self.num_vars_x -= 1;
  }

  // Bound the entire "p" section to r_p
  // Must occur after r_q's are bounded
  pub fn bound_poly_vars_rp(&mut self, 
      r_p: &Vec<Scalar>,
    ) {
      for r in r_p {
        self.bound_poly_q(r);
      }
    }


  // Bound the entire "q_rev" section to r_q
  pub fn bound_poly_vars_rq(&mut self, 
    r_q: &Vec<Scalar>,
  ) {
    for r in r_q {
      self.bound_poly_q(r);
    }
  }

  // Bound the entire "x" section to r_x
  pub fn bound_poly_vars_rx(&mut self, 
    r_x: &Vec<Scalar>,
  ) {
    for r in r_x {
      self.bound_poly_x(r);
    }
  }

  pub fn evaluate(&mut self,
    r_p: &Vec<Scalar>,
    r_q: &Vec<Scalar>,
    r_x: &Vec<Scalar>,
  ) -> Scalar {
    let mut cl = self.clone();
    cl.bound_poly_vars_rx(r_x);
    cl.bound_poly_vars_rq(r_q);
    cl.bound_poly_vars_rp(r_p);
    return cl.index(0, 0, 0);
  }

  pub fn commit(
      &self,
      gens: &PolyCommitmentGens,
      random_tape: Option<&mut RandomTape>,
  ) -> (PolyCommitment_PQX, PolyCommitmentBlinds_PQX) {

      let mut blinds = Vec::new();
      if let Some(t) = random_tape {
          for p in 0..self.num_instances {
              blinds.push(t.random_vector(b"poly_blinds", self.num_proofs[p]));
          } 
      } else {
          for p in 0..self.num_instances {
              blinds.push(vec![Scalar::zero(); self.num_proofs[p]]);
          };
      }

      let blinds = PolyCommitmentBlinds_PQX { blinds };

      let mut C = Vec::new();
      for p in 0..self.num_instances {
          C.push(Vec::new());
          for q in 0..self.num_proofs[p] {
              C[p].push(self.Z[p][q].commit(&blinds.blinds[p][q], &gens.gens.gens_n).compress());
          }
      }

      (PolyCommitment_PQX { C }, blinds)
  }    

  // Convert to a (p, q_rev, x) regular dense poly
  pub fn to_dense_poly(&self) -> DensePolynomial {
      let mut Z_poly = vec![Scalar::zero(); self.num_instances * self.max_num_proofs * self.num_inputs];
      for p in 0..self.num_instances {
        let step = self.max_num_proofs / self.num_proofs[p];
        for q in 0..self.num_proofs[p] {
          for x in 0..self.num_inputs {
              Z_poly[p * self.max_num_proofs * self.num_inputs + q * step * self.num_inputs + x] = self.Z[p][q][x];
          }
        }
      }
      DensePolynomial::new(Z_poly)
  }
}

pub struct PolyCommitmentBlinds_PQX {
    blinds: Vec<Vec<Scalar>>,
  }

#[derive(Debug, Serialize, Deserialize)]
pub struct PolyCommitment_PQX {
    C: Vec<Vec<CompressedGroup>>,
}

impl AppendToTranscript for PolyCommitment_PQX {
    fn append_to_transcript(&self, label: &'static [u8], transcript: &mut Transcript) {
      transcript.append_message(label, b"poly_commitment_begin");
      for p in 0..self.C.len() {
        for q in 0..self.C[p].len() {
            transcript.append_point(b"poly_commitment_share", &self.C[p][q]);
        }
      }
      transcript.append_message(label, b"poly_commitment_end");
    }
  }
  

#[derive(Debug, Serialize, Deserialize)]
pub struct PolyEvalProof_PQX {
  proof: DotProductProofLog,
}

impl PolyEvalProof_PQX {
  fn protocol_name() -> &'static [u8] {
    b"polynomial evaluation proof"
  }

  pub fn prove(
    mut poly: DensePolynomial_PQX,
    num_proofs: Vec<usize>,
    blinds_opt: Option<&PolyCommitmentBlinds_PQX>,
    rp: &[Scalar],                 // point at which the polynomial is evaluated
    rq: &[Scalar],                 // rq is in reversed order, i.e. the same order as the polynomial
    rx: &[Scalar],
    Zr: &Scalar,                   // evaluation of \widetilde{Z}(r)
    blind_Zr_opt: Option<&Scalar>, // specifies a blind for Zr
    gens: &PolyCommitmentGens,
    transcript: &mut Transcript,
    random_tape: &mut RandomTape,
  ) -> (PolyEvalProof_PQX, CompressedGroup) {
    transcript.append_protocol_name(PolyEvalProof_PQX::protocol_name());

    // assert vectors are of the right size
    assert_eq!(poly.get_num_vars(), rp.len() + rq.len() + rx.len());
    let num_instances = rp.len().pow2();
    let max_num_proofs = rq.len().pow2();

    let mut default_blinds = Vec::new();
    for p in 0..num_instances {
        default_blinds.push(vec![Scalar::zero(); num_proofs[p]]);
    }

    let default_blinds = PolyCommitmentBlinds_PQX { blinds: default_blinds };
    let blinds = blinds_opt.map_or(&default_blinds, |p| p);

    assert_eq!(blinds.blinds.len(), num_instances);
    for p in 0..num_instances {
        assert_eq!(blinds.blinds[p].len(), num_proofs[p]);
    }

    let zero = Scalar::zero();
    let blind_Zr = blind_Zr_opt.map_or(&zero, |p| p);

    // compute the L and R vectors
    // TODO: Reduce complexity of this
    let L = EqPolynomial::new([rp, rq].concat()).evals();
    let R = EqPolynomial::new(rx.to_vec()).evals();

    // compute the vector underneath L*Z and the L*blinds
    // compute vector-matrix product between L and Z viewed as a matrix
    poly.bound_poly_vars_rq(&rq.to_vec());
    poly.bound_poly_vars_rp(&rp.to_vec());
    let LZ = &poly.Z[0][0];
    let mut LZ_blind = Scalar::zero();
    for p in 0..num_instances {
        for q in 0..num_proofs[p] {
            LZ_blind += blinds.blinds[p][q] * L[p * max_num_proofs + q];
        }
    }

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

    (PolyEvalProof_PQX { proof }, C_Zr_prime)
  }

  pub fn verify(
    &self,
    gens: &PolyCommitmentGens,
    transcript: &mut Transcript,
    rp: &[Scalar],                 // point at which the polynomial is evaluated
    rq: &[Scalar],                 // rq is in reversed order, i.e. the same order as the polynomial
    rx: &[Scalar],
    C_Zr: &CompressedGroup, // commitment to \widetilde{Z}(r)
    comm: &PolyCommitment_PQX,
  ) -> Result<(), ProofVerifyError> {
    transcript.append_protocol_name(PolyEvalProof_PQX::protocol_name());

    let max_num_proofs = rq.len().pow2();

    // compute L and R
    // TODO: Reduce complexity of this
    let L = EqPolynomial::new([rp, rq].concat()).evals();
    let R = EqPolynomial::new(rx.to_vec()).evals();

    // compute a weighted sum of commitments and L
    let mut L_compact = Vec::new();
    let mut C_decompressed = Vec::new();
    for p in 0..comm.C.len() {
        for q in 0..comm.C[p].len() {
            L_compact.push(L[p * max_num_proofs + q]);
            C_decompressed.push(comm.C[p][q].decompress().unwrap());
        }
    }

    let C_LZ = GroupElement::vartime_multiscalar_mul(&L_compact, C_decompressed).compress();

    self
      .proof
      .verify(R.len(), &gens.gens, transcript, &R, &C_LZ, C_Zr)
  }
}
