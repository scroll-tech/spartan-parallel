#![allow(clippy::too_many_arguments)]
use crate::dense_mlpoly::{DensePolynomial, EqPolynomial};

use super::commitments::{Commitments, MultiCommitGens};
use super::errors::ProofVerifyError;
use super::group::{CompressedGroup, GroupElement, VartimeMultiscalarMul};
use super::math::Math;
use super::nizk::{DotProductProofGens, DotProductProofLog};
use super::random::RandomTape;
use super::scalar::Scalar;
use super::transcript::{AppendToTranscript, ProofTranscript};
use core::ops::Index;
use merlin::Transcript;
use serde::{Deserialize, Serialize};

// Customized Dense ML Polynomials for Data-Parallelism
// These Dense ML Polys are aimed for space-efficiency by removing the 0s for invalid (p, q) pair

// Dense polynomial with variable order: p, q_rev, x
// Used by Z_poly in r1csproof
#[derive(Debug)]
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

    // Bound the entire "q_rev" section to r_q
    pub fn bound_poly_vars_rq(&mut self, 
      r_q: &Vec<Scalar>,
    ) {
      for r in r_q {
        self.bound_poly_q(r);
      }
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
