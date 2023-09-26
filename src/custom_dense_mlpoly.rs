#![allow(clippy::too_many_arguments)]
use crate::dense_mlpoly::DensePolynomial;

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

impl DensePolynomial_PQX {
    // Assume z_mat is in its standard form of (p, q, x) as what a reasonable front end would provide
    // Convert it to (p, q_rev, x)
    pub fn new(z_mat: &Vec<Vec<Vec<Scalar>>>, num_proofs: &Vec<usize>, max_num_proofs: usize) -> Self {
      let mut Z = Vec::new();
      let num_instances = z_mat.len();
      let num_inputs = z_mat[0][0].len();
      for p in 0..num_instances {
        Z.push(vec![Vec::new(); num_proofs[p]]);
        let step = max_num_proofs / num_proofs[p];
        for q in 0..num_proofs[p] {
            // Reverse the bits of q. q_rev is a multiple of step
            let q_rev = (0..max_num_proofs.log_2()).rev().map(|i| q / (i.pow2()) % 2 * (max_num_proofs / i.pow2() / 2)).fold(0, |a, b| a + b);
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
  
    // Binding the entire "q_rev" section to r_q
    pub fn bound_poly_rq(&mut self, 
      r_q: &Vec<Scalar>,
    ) {
      for r in r_q {
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
  