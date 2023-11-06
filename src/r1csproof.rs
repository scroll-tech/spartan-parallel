#![allow(clippy::too_many_arguments)]
// use crate::custom_dense_mlpoly::{PolyEvalProof_PQX, PolyCommitment_PQX};

use super::commitments::{Commitments, MultiCommitGens};
use super::dense_mlpoly::{
  DensePolynomial, EqPolynomial, PolyCommitment, PolyCommitmentGens, PolyEvalProof,
};
use super::custom_dense_mlpoly::DensePolynomial_PQX;
use super::errors::ProofVerifyError;
use super::group::{CompressedGroup, GroupElement, VartimeMultiscalarMul};
use super::math::Math;
use super::nizk::{EqualityProof, KnowledgeProof, ProductProof};
use super::r1csinstance::R1CSInstance;
use super::random::RandomTape;
use super::scalar::Scalar;
use super::sumcheck::ZKSumcheckInstanceProof;
use super::timer::Timer;
use super::transcript::{AppendToTranscript, ProofTranscript};
use core::iter;
use curve25519_dalek::ristretto::{RistrettoPoint, CompressedRistretto};
use merlin::Transcript;
use serde::{Deserialize, Serialize};

#[derive(Serialize, Deserialize, Debug)]
pub struct R1CSProof {
  sc_proof_phase1: ZKSumcheckInstanceProof,
  claims_phase2: (
    CompressedGroup,
    CompressedGroup,
    CompressedGroup,
    CompressedGroup,
  ),
  pok_claims_phase2: (KnowledgeProof, ProductProof),
  proof_eq_sc_phase1: EqualityProof,
  sc_proof_phase2: ZKSumcheckInstanceProof,
  // Need to commit vars for short and long witnesses separately
  // The long version must exist, the short version might not
  comm_short_vars_at_ry: Option<CompressedGroup>,
  comm_vars_at_ry_list: Vec<CompressedGroup>,
  comm_vars_at_ry: CompressedGroup,
  proof_eval_short_vars_at_ry: Option<PolyEvalProof>,
  proof_eval_vars_at_ry_list: Vec<PolyEvalProof>,
  proof_eq_sc_phase2: EqualityProof,
}

pub struct R1CSSumcheckGens {
  gens_1: MultiCommitGens,
  gens_3: MultiCommitGens,
  gens_4: MultiCommitGens,
}

// TODO: fix passing gens_1_ref
impl R1CSSumcheckGens {
  pub fn new(label: &'static [u8], gens_1_ref: &MultiCommitGens) -> Self {
    let gens_1 = gens_1_ref.clone();
    let gens_3 = MultiCommitGens::new(3, label);
    let gens_4 = MultiCommitGens::new(4, label);

    R1CSSumcheckGens {
      gens_1,
      gens_3,
      gens_4,
    }
  }
}

pub struct R1CSGens {
  pub gens_sc: R1CSSumcheckGens,
  pub gens_pc: PolyCommitmentGens,
}

impl R1CSGens {
  pub fn new(label: &'static [u8], _num_cons: usize, num_vars: usize) -> Self {
    let num_poly_vars = num_vars.log_2();
    let gens_pc = PolyCommitmentGens::new(num_poly_vars, label, false);
    let gens_sc = R1CSSumcheckGens::new(label, &gens_pc.gens.gens_1);
    R1CSGens { gens_sc, gens_pc }
  }
}

impl R1CSProof {
  fn prove_phase_one(
    num_rounds: usize,
    num_rounds_x: usize,
    num_rounds_q_max: usize,
    num_rounds_p: usize,
    num_proofs: &Vec<usize>,
    evals_tau_p: &mut DensePolynomial,
    evals_tau_q: &mut DensePolynomial,
    evals_tau_x: &mut DensePolynomial,
    evals_Az: &mut DensePolynomial_PQX,
    evals_Bz: &mut DensePolynomial_PQX,
    evals_Cz: &mut DensePolynomial_PQX,
    gens: &R1CSSumcheckGens,
    transcript: &mut Transcript,
    random_tape: &mut RandomTape,
  ) -> (ZKSumcheckInstanceProof, Vec<Scalar>, Vec<Scalar>, Scalar) {
    let comb_func = |poly_A_comp: &Scalar,
                     poly_B_comp: &Scalar,
                     poly_C_comp: &Scalar,
                     poly_D_comp: &Scalar|
     -> Scalar { poly_A_comp * (poly_B_comp * poly_C_comp - poly_D_comp) };

    let (sc_proof_phase_one, r, claims, blind_claim_postsc) =
      ZKSumcheckInstanceProof::prove_cubic_with_additive_term_disjoint_rounds(
        &Scalar::zero(), // claim is zero
        &Scalar::zero(), // blind for claim is also zero
        num_rounds,
        num_rounds_x,
        num_rounds_q_max,
        num_rounds_p,
        num_proofs.clone(),
        evals_tau_p,
        evals_tau_q,
        evals_tau_x,
        evals_Az,
        evals_Bz,
        evals_Cz,
        comb_func,
        &gens.gens_1,
        &gens.gens_4,
        transcript,
        random_tape,
      );

    (sc_proof_phase_one, r, claims, blind_claim_postsc)
  }

  fn prove_phase_two(
    num_rounds: usize,
    claim: &Scalar,
    blind_claim: &Scalar,
    evals_z: &mut DensePolynomial,
    evals_ABC: &mut DensePolynomial,
    evals_eq: &mut DensePolynomial,
    gens: &R1CSSumcheckGens,
    transcript: &mut Transcript,
    random_tape: &mut RandomTape,
  ) -> (ZKSumcheckInstanceProof, Vec<Scalar>, Vec<Scalar>, Scalar) {
    let comb_func =
      |poly_A_comp: &Scalar, poly_B_comp: &Scalar, poly_C_comp: &Scalar| -> Scalar { poly_A_comp * poly_B_comp * poly_C_comp };
    let (sc_proof_phase_two, r, claims, blind_claim_postsc) = ZKSumcheckInstanceProof::prove_cubic(
      claim,
      blind_claim,
      num_rounds,
      evals_z,
      evals_ABC,
      evals_eq,
      comb_func,
      &gens.gens_1,
      &gens.gens_4,
      transcript,
      random_tape,
    );

    (sc_proof_phase_two, r, claims, blind_claim_postsc)
  }

  fn protocol_name() -> &'static [u8] {
    b"R1CS proof"
  }

  // A generic R1CS prover that enables data-parallelism on instances
  pub fn prove(
    // How many sections does each Z vector have?
    // num_witness secs can be 1, 2, or 4
    num_witness_secs: usize,
    // How many of these witnesses secs are short?
    // A short witness sect has just one copy, versus a long sect which has num_instances * num_proofs different versions
    // We assume the first num_shorts witness sects are short and the rest are long
    // There are at least one long witness sects
    num_shorts: usize,
    
    num_instances: usize,
    max_num_proofs: usize,
    num_proofs: &Vec<usize>,
    num_inputs: usize,
    inst: &R1CSInstance,
    gens: &R1CSGens,
    // Depends on num_witness_secs, witnesses are separated into w[0], w[1], w[2], w[3]
    // Each committed separately but concacted together to form Z
    w_mat: Vec<&Vec<Vec<Vec<Scalar>>>>,
    // The polynomial interpolated from each witness section
    poly_w_list: Vec<&Vec<DensePolynomial>>,
    transcript: &mut Transcript,
    random_tape: &mut RandomTape,
  ) -> (R1CSProof, [Vec<Scalar>; 4]) { 
    let timer_prove = Timer::new("R1CSProof::prove");
    transcript.append_protocol_name(R1CSProof::protocol_name());

    // Assert num_witness_secs is valid
    assert!(num_witness_secs == 1 || num_witness_secs == 2 || num_witness_secs == 4);
    assert_eq!(num_witness_secs, w_mat.len());
    assert_eq!(num_witness_secs, poly_w_list.len());
    // Currently, only support the case of num_witness_secs = 4 && num_shorts = 1
    assert!(num_shorts == 0 || num_shorts == 1 && num_witness_secs == 4);

    // Assert everything is a power of 2
    assert_eq!(num_instances, num_instances.next_power_of_two());
    assert_eq!(max_num_proofs, max_num_proofs.next_power_of_two());
    for p in num_proofs {
      assert_eq!(*p, p.next_power_of_two());
      assert!(*p <= max_num_proofs);
    }
    assert_eq!(num_inputs, num_inputs.next_power_of_two());

    // Number of instances is either one or matches num_instances
    assert!(inst.get_num_instances() == 1 || inst.get_num_instances() == num_instances);
    // Number of each witness is either one or matches num_instances and num_proofs
    for i in 0..num_witness_secs {
      assert!(i < num_shorts && w_mat[i].len() == 1 || !(i < num_shorts) && w_mat[i].len() == num_instances);
      for p in 0..w_mat[i].len() {
        assert!(i < num_shorts && w_mat[i][p].len() == 1 || !(i < num_shorts) && w_mat[i][p].len() == num_proofs[p]);
        for q in 0..w_mat[i][p].len() {
          assert_eq!(w_mat[i][p][q].len(), num_inputs);
        }
      }
    }

    // --
    // PHASE 1
    // --
    let num_cons = inst.get_num_cons();
    let timer_sc_proof_phase1 = Timer::new("prove_sc_phase_one");

    // append input to variables to create a single vector z
    let mut z_mat = Vec::new();
    for p in 0..num_instances {
      z_mat.push(Vec::new());
      for q in 0..num_proofs[p] {
        z_mat[p].push(Vec::new());
        for w in 0..num_witness_secs {
          let p_w = if w < num_shorts { 0 } else { p };
          let q_w = if w < num_shorts { 0 } else { q };
          z_mat[p][q].extend(w_mat[w][p_w][q_w].clone());
        }
      }
    }
    let z_len = num_inputs * num_witness_secs;

    // derive the verifier's challenge \tau
    let (num_rounds_p, num_rounds_q, num_rounds_x, num_rounds_y) = 
      (num_instances.log_2(), max_num_proofs.log_2(), num_cons.log_2(), z_len.log_2());
    let tau_p = transcript.challenge_vector(b"challenge_tau_p", num_rounds_p);
    let tau_q = transcript.challenge_vector(b"challenge_tau_q", num_rounds_q);
    let tau_x = transcript.challenge_vector(b"challenge_tau_x", num_rounds_x);

    // compute the initial evaluation table for R(\tau, x)
    let mut poly_tau_p = DensePolynomial::new(EqPolynomial::new(tau_p).evals());
    let mut poly_tau_q = DensePolynomial::new(EqPolynomial::new(tau_q).evals());
    let mut poly_tau_x = DensePolynomial::new(EqPolynomial::new(tau_x).evals());
    let (mut poly_Az, mut poly_Bz, mut poly_Cz) =
      inst.multiply_vec_block(num_instances, num_proofs, max_num_proofs, num_cons, z_len, &z_mat);

    // Sumcheck 1: (Az * Bz - Cz) * eq(x, q, p) = 0
    let (sc_proof_phase1, rx, _claims_phase1, blind_claim_postsc1) = R1CSProof::prove_phase_one(
      num_rounds_x + num_rounds_q + num_rounds_p,
      num_rounds_x,
      num_rounds_q,
      num_rounds_p,
      &num_proofs,
      &mut poly_tau_p,
      &mut poly_tau_q,
      &mut poly_tau_x,
      &mut poly_Az,
      &mut poly_Bz,
      &mut poly_Cz,
      &gens.gens_sc,
      transcript,
      random_tape,
    );
    assert_eq!(poly_tau_p.len(), 1);
    assert_eq!(poly_tau_q.len(), 1);
    assert_eq!(poly_tau_x.len(), 1);
    assert_eq!(poly_Az.len(), 1);
    assert_eq!(poly_Bz.len(), 1);
    assert_eq!(poly_Cz.len(), 1);
    timer_sc_proof_phase1.stop();

    let (tau_claim, Az_claim, Bz_claim, Cz_claim) =
      (&(poly_tau_p[0] * poly_tau_q[0] * poly_tau_x[0]), &poly_Az.index(0, 0, 0), &poly_Bz.index(0, 0, 0), &poly_Cz.index(0, 0, 0));

    let (Az_blind, Bz_blind, Cz_blind, prod_Az_Bz_blind) = (
      random_tape.random_scalar(b"Az_blind"),
      random_tape.random_scalar(b"Bz_blind"),
      random_tape.random_scalar(b"Cz_blind"),
      random_tape.random_scalar(b"prod_Az_Bz_blind"),
    );

    let (pok_Cz_claim, comm_Cz_claim) = {
      KnowledgeProof::prove(
        &gens.gens_sc.gens_1,
        transcript,
        random_tape,
        Cz_claim,
        &Cz_blind,
      )
    };

    let (proof_prod, comm_Az_claim, comm_Bz_claim, comm_prod_Az_Bz_claims) = {
      let prod = Az_claim * Bz_claim;
      ProductProof::prove(
        &gens.gens_sc.gens_1,
        transcript,
        random_tape,
        Az_claim,
        &Az_blind,
        Bz_claim,
        &Bz_blind,
        &prod,
        &prod_Az_Bz_blind,
      )
    };

    comm_Az_claim.append_to_transcript(b"comm_Az_claim", transcript);
    comm_Bz_claim.append_to_transcript(b"comm_Bz_claim", transcript);
    comm_Cz_claim.append_to_transcript(b"comm_Cz_claim", transcript);
    comm_prod_Az_Bz_claims.append_to_transcript(b"comm_prod_Az_Bz_claims", transcript);

    // prove the final step of sum-check #1
    let taus_bound_rx = tau_claim;

    let blind_expected_claim_postsc1 = taus_bound_rx * (prod_Az_Bz_blind - Cz_blind);
    let claim_post_phase1 = (Az_claim * Bz_claim - Cz_claim) * taus_bound_rx;
    let (proof_eq_sc_phase1, _C1, _C2) = EqualityProof::prove(
      &gens.gens_sc.gens_1,
      transcript,
      random_tape,
      &claim_post_phase1,
      &blind_expected_claim_postsc1,
      &claim_post_phase1,
      &blind_claim_postsc1,
    );

    // Separate the result rx into rp, rq, and rx
    let (rx, rq_rev) = rx.split_at(num_rounds_x);
    let (rq_rev, rp) = rq_rev.split_at(num_rounds_q);
    let rx = rx.to_vec();
    let rq_rev = rq_rev.to_vec();
    let rq: Vec<Scalar> = rq_rev.iter().copied().rev().collect();
    let rp = rp.to_vec();

    // --
    // PHASE 2
    // --
    let timer_sc_proof_phase2 = Timer::new("prove_sc_phase_two");
    // combine the three claims into a single claim
    let r_A = transcript.challenge_scalar(b"challenge_Az");
    let r_B = transcript.challenge_scalar(b"challenge_Bz");
    let r_C = transcript.challenge_scalar(b"challenge_Cz");

    let claim_phase2 = r_A * Az_claim + r_B * Bz_claim + r_C * Cz_claim;
    let blind_claim_phase2 = r_A * Az_blind + r_B * Bz_blind + r_C * Cz_blind;

    let evals_ABC = {
      // compute the initial evaluation table for R(\tau, x)
      let evals_rx = EqPolynomial::new(rx.clone()).evals();
      let (evals_A, evals_B, evals_C) =
      inst.compute_eval_table_sparse(num_instances, inst.get_num_cons(), z_len, &evals_rx);

      assert_eq!(evals_A.len(), evals_B.len());
      assert_eq!(evals_A.len(), evals_C.len());
      (0..evals_A.len())
        .map(|i| r_A * evals_A[i] + r_B * evals_B[i] + r_C * evals_C[i])
        .collect::<Vec<Scalar>>()
    };
    let mut ABC_poly = DensePolynomial::new(evals_ABC);

    // Construct a p * q * len(z) matrix Z and bound it to r_q
    let mut Z = DensePolynomial_PQX::new_rev(&z_mat, &num_proofs, max_num_proofs);
    Z.bound_poly_vars_rq(&rq_rev.to_vec());
    let mut Z_poly = Z.to_dense_poly();

    // An Eq function to match p with rp
    let mut eq_p_rp_poly = DensePolynomial::new(EqPolynomial::new(rp).evals_front(num_rounds_p + num_rounds_y));

    // Sumcheck 2: (rA + rB + rC) * Z * eq(p) = e
    let (sc_proof_phase2, ry, claims_phase2, blind_claim_postsc2) = R1CSProof::prove_phase_two(
      num_rounds_p + num_rounds_y,
      &claim_phase2,
      &blind_claim_phase2,
      &mut Z_poly,
      &mut ABC_poly,
      &mut eq_p_rp_poly,
      &gens.gens_sc,
      transcript,
      random_tape,
    );
    timer_sc_proof_phase2.stop();

    // Separate ry into rp and ry
    let (rp, ry) = ry.split_at(num_rounds_p);
    let rp = rp.to_vec();
    let ry = ry.to_vec();

    assert_eq!(Z_poly.len(), 1);
    assert_eq!(ABC_poly.len(), 1);

    // Bind the witnesses and inputs instance-by-instance
    let mut eval_vars_at_ry_list = Vec::new();
    let mut proof_eval_vars_at_ry_list = Vec::new();
    let mut comm_vars_at_ry_list = Vec::new();
    let eval_short_vars_at_ry: Option<Scalar>;
    let proof_eval_short_vars_at_ry: Option<PolyEvalProof>;
    let comm_short_vars_at_ry: Option<CompressedRistretto>;
    let timer_polyeval = Timer::new("polyeval");

    // poly_long
    for p in 0..num_instances {
      // if poly_vars exists, compute combined_poly as (Scalar::one() - ry[0]) * poly_vars + ry[0] * poly_inputs
      // otherwise combined_poly is just poly_inputs
      let (combined_poly, r) = {
        // if num_proofs[p] < max_num_proofs, then only the last few entries of rq needs to be binded
        let rq_short = &rq[num_rounds_q - num_proofs[p].log_2()..];
        match (num_witness_secs, num_shorts) {
          (1, 0) => (poly_w_list[0][p].clone(), [rq_short, &ry].concat()),
          (2, 0) => (
            DensePolynomial::new(
              (0..num_proofs[p] * num_inputs).map(
                |i| {
                  (Scalar::one() - ry[0]) * poly_w_list[0][p][i]
                        + ry[0] * poly_w_list[1][p][i]
                }
              ).collect()),
            [rq_short, &ry[1..]].concat()
          ),
          (4, 0) => (
            DensePolynomial::new(
              (0..num_proofs[p] * num_inputs).map(
                |i| {
                  (Scalar::one() - ry[0]) * (Scalar::one() - ry[1]) * poly_w_list[0][p][i]
                        + (Scalar::one() - ry[0]) * ry[1] * poly_w_list[1][p][i]
                        + ry[0] * (Scalar::one() - ry[1]) * poly_w_list[2][p][i]
                        + ry[0] * ry[1] * poly_w_list[3][p][i]
                }
              ).collect()),
            [rq_short, &ry[2..]].concat()
          ),
          (4, 1) => (
            DensePolynomial::new(
              (0..num_proofs[p] * num_inputs).map(
                |i| {
                  (Scalar::one() - ry[0]) * ry[1] * poly_w_list[1][p][i]
                    + ry[0] * (Scalar::one() - ry[1]) * poly_w_list[2][p][i]
                    + ry[0] * ry[1] * poly_w_list[3][p][i]
                }
              ).collect()),
            [rq_short, &ry[2..]].concat()
          ),
          _ => panic!("PROOF Failed: Unsupported (num_witness_secs, num_shorts) pair: ({}, {})", num_witness_secs, num_shorts)
        }
      };

      let eval_vars_at_ry = combined_poly.evaluate(&r);
      let (proof_eval_vars_at_ry, comm_vars_at_ry) = PolyEvalProof::prove(
        &combined_poly,
        None,
        &r,
        &eval_vars_at_ry,
        None,
        &gens.gens_pc,
        transcript,
        random_tape,
      );

      eval_vars_at_ry_list.push(eval_vars_at_ry);
      proof_eval_vars_at_ry_list.push(proof_eval_vars_at_ry);
      comm_vars_at_ry_list.push(comm_vars_at_ry);
    }
    // poly_short
    match (num_witness_secs, num_shorts) {
      (_, 0) => {
        (eval_short_vars_at_ry, proof_eval_short_vars_at_ry, comm_short_vars_at_ry) = (None, None, None);
      },
      (4, 1) => {
        let c = poly_w_list[0][0].clone();
        let e = c.evaluate(&ry[2..]);
        let (p, c) = PolyEvalProof::prove(
          &c,
          None,
          &ry[2..],
          &e,
          None,
          &gens.gens_pc,
          transcript,
          random_tape,
        );
        (eval_short_vars_at_ry, proof_eval_short_vars_at_ry, comm_short_vars_at_ry) = (Some(e), Some(p), Some(c));
      },
      _ => panic!("PROOF Failed: Unsupported (num_witness_secs, num_shorts) pair: ({}, {})", num_witness_secs, num_shorts)
    }
    timer_polyeval.stop();
    
    // Bind the resulting witness list to rp
    // poly_vars stores the result of each witness matrix bounded to (rq_short ++ ry)
    // but we want to bound them to (rq ++ ry)
    // So we need to multiply each entry by (1 - rq0)(1 - rq1)...
    for p in 0..num_instances {
      if num_shorts > 0 {
        assert_eq!(num_witness_secs, 4);
        assert_eq!(num_shorts, 1);
        eval_vars_at_ry_list[p] += (Scalar::one() - ry[0]) * (Scalar::one() - ry[1]) * eval_short_vars_at_ry.unwrap();
      }
      for q in 0..(num_rounds_q - num_proofs[p].log_2()) {
        eval_vars_at_ry_list[p] *= Scalar::one() - rq[q];
      }
    }

    let poly_vars = DensePolynomial::new(eval_vars_at_ry_list);
    let eval_vars_at_ry = poly_vars.evaluate(&rp);

    let comm_vars_at_ry = eval_vars_at_ry.commit(&Scalar::zero(), &gens.gens_pc.gens.gens_1).compress();

    // prove the final step of sum-check #2
    let blind_expected_claim_postsc2 = Scalar::zero();
    let claim_post_phase2 = claims_phase2[0] * claims_phase2[1] * claims_phase2[2];

    let (proof_eq_sc_phase2, _C1, _C2) = EqualityProof::prove(
      &gens.gens_pc.gens.gens_1,
      transcript,
      random_tape,
      &claim_post_phase2,
      &blind_expected_claim_postsc2,
      &claim_post_phase2,
      &blind_claim_postsc2,
    );

    timer_prove.stop();

    let claims_phase2 = (
      comm_Az_claim,
      comm_Bz_claim,
      comm_Cz_claim,
      comm_prod_Az_Bz_claims,
    );
    let pok_claims_phase2 = (
      pok_Cz_claim, proof_prod
    );

    (
      R1CSProof {
        sc_proof_phase1,
        claims_phase2,
        pok_claims_phase2,
        proof_eq_sc_phase1,
        sc_proof_phase2,
        comm_short_vars_at_ry,
        comm_vars_at_ry_list,
        comm_vars_at_ry,
        proof_eval_short_vars_at_ry,
        proof_eval_vars_at_ry_list,
        proof_eq_sc_phase2
      },
      [rp, rq_rev, rx, ry]
    )
  }

  pub fn verify(
    &self,
    // num_witness secs can be 1, 2, or 4
    num_witness_secs: usize,
    num_shorts: usize,

    num_instances: usize,
    max_num_proofs: usize,
    num_proofs: &Vec<usize>,
    num_inputs: usize,
    num_cons: usize,
    gens: &R1CSGens,
    evals: &(Scalar, Scalar, Scalar),
    // Commitment for witnesses
    comm_w_list: Vec<&Vec<PolyCommitment>>,
    transcript: &mut Transcript,
  ) -> Result<[Vec<Scalar>; 4], ProofVerifyError> {
    transcript.append_protocol_name(R1CSProof::protocol_name());

    // Assert num_witness_secs is valid
    assert!(num_witness_secs == 1 || num_witness_secs == 2 || num_witness_secs == 4);
    assert_eq!(num_witness_secs, comm_w_list.len());

    let z_len = num_inputs * num_witness_secs;
    let (num_rounds_x, num_rounds_p, num_rounds_q, num_rounds_y) = (num_cons.log_2(), num_instances.log_2(), max_num_proofs.log_2(), z_len.log_2());

    // derive the verifier's challenge tau
    let tau_p = transcript.challenge_vector(b"challenge_tau_p", num_rounds_p);
    let tau_q = transcript.challenge_vector(b"challenge_tau_q", num_rounds_q);
    let tau_x = transcript.challenge_vector(b"challenge_tau_x", num_rounds_x);

    // verify the first sum-check instance
    let claim_phase1 = Scalar::zero()
      .commit(&Scalar::zero(), &gens.gens_sc.gens_1)
      .compress();
    let (comm_claim_post_phase1, rx) = self.sc_proof_phase1.verify(
      &claim_phase1,
      num_rounds_x + num_rounds_q + num_rounds_p,
      3,
      &gens.gens_sc.gens_1,
      &gens.gens_sc.gens_4,
      transcript,
    )?;

    // perform the intermediate sum-check test with claimed Az, Bz, and Cz
    let (comm_Az_claim, comm_Bz_claim, comm_Cz_claim, comm_prod_Az_Bz_claims) = &self.claims_phase2;
    let (pok_Cz_claim, proof_prod) = &self.pok_claims_phase2;

    pok_Cz_claim.verify(&gens.gens_sc.gens_1, transcript, comm_Cz_claim)?;
    proof_prod.verify(
      &gens.gens_sc.gens_1,
      transcript,
      comm_Az_claim,
      comm_Bz_claim,
      comm_prod_Az_Bz_claims,
    )?;

    comm_Az_claim.append_to_transcript(b"comm_Az_claim", transcript);
    comm_Bz_claim.append_to_transcript(b"comm_Bz_claim", transcript);
    comm_Cz_claim.append_to_transcript(b"comm_Cz_claim", transcript);
    comm_prod_Az_Bz_claims.append_to_transcript(b"comm_prod_Az_Bz_claims", transcript);

    // Separate the result rx into rp_round1, rq, and rx
    let (rx, rq_rev) = rx.split_at(num_rounds_x);
    let (rq_rev, rp_round1) = rq_rev.split_at(num_rounds_q);
    let rx = rx.to_vec();
    let rq_rev = rq_rev.to_vec();
    let rq: Vec<Scalar> = rq_rev.iter().copied().rev().collect();
    let rp_round1 = rp_round1.to_vec();

    // taus_bound_rx is really taus_bound_rx_rq_rp
    let taus_bound_rp: Scalar = (0..rp_round1.len())
      .map(|i| rp_round1[i] * tau_p[i] + (Scalar::one() - rp_round1[i]) * (Scalar::one() - tau_p[i]))
      .product();
    let taus_bound_rq: Scalar = (0..rq_rev.len())
      .map(|i| rq_rev[i] * tau_q[i] + (Scalar::one() - rq_rev[i]) * (Scalar::one() - tau_q[i]))
      .product();
    let taus_bound_rx: Scalar = (0..rx.len())
      .map(|i| rx[i] * tau_x[i] + (Scalar::one() - rx[i]) * (Scalar::one() - tau_x[i]))
      .product();
    let taus_bound_rx = taus_bound_rp * taus_bound_rq * taus_bound_rx;

    let expected_claim_post_phase1 = (taus_bound_rx
      * (comm_prod_Az_Bz_claims.decompress().unwrap() - comm_Cz_claim.decompress().unwrap()))
    .compress();

    // verify proof that expected_claim_post_phase1 == claim_post_phase1
    self.proof_eq_sc_phase1.verify(
      &gens.gens_sc.gens_1,
      transcript,
      &expected_claim_post_phase1,
      &comm_claim_post_phase1,
    )?;

    // derive three public challenges and then derive a joint claim
    let r_A = transcript.challenge_scalar(b"challenge_Az");
    let r_B = transcript.challenge_scalar(b"challenge_Bz");
    let r_C = transcript.challenge_scalar(b"challenge_Cz");

    // r_A * comm_Az_claim + r_B * comm_Bz_claim + r_C * comm_Cz_claim;
    let comm_claim_phase2 = GroupElement::vartime_multiscalar_mul(
      iter::once(&r_A)
        .chain(iter::once(&r_B))
        .chain(iter::once(&r_C)),
      iter::once(&comm_Az_claim)
        .chain(iter::once(&comm_Bz_claim))
        .chain(iter::once(&comm_Cz_claim))
        .map(|pt| pt.decompress().unwrap())
        .collect::<Vec<GroupElement>>(),
    )
    .compress();

    // verify the joint claim with a sum-check protocol
    let (comm_claim_post_phase2, ry) = self.sc_proof_phase2.verify(
      &comm_claim_phase2,
      num_rounds_p + num_rounds_y,
      3,
      &gens.gens_sc.gens_1,
      &gens.gens_sc.gens_4,
      transcript,
    )?;

    // Separate ry into rp and ry
    let (rp, ry) = ry.split_at(num_rounds_p);
    let rp = rp.to_vec();
    let ry = ry.to_vec();

    // An Eq function to match p with rp
    let p_rp_poly_bound_ry: Scalar = (0..rp.len())
      .map(|i| rp[i] * rp_round1[i] + (Scalar::one() - rp[i]) * (Scalar::one() - rp_round1[i]))
      .product();

    // verify Z(rp, rq, ry) proof against the initial commitment
    // First instance-by-instance on ry
    for p in 0..num_instances {
      // if comm_vars exists, comm_combined = (Scalar::one() - ry[0]) * comm_vars + ry[0] * comm_inputs
      // otherwise comm_combined is just comm_inputs
      let (comm_combined, r) = {
        // if num_proofs[p] < max_num_proofs, then only the last few entries of rq needs to be binded
        let rq_short = &rq[num_rounds_q - num_proofs[p].log_2()..];

        match (num_witness_secs, num_shorts) {
          (1, 0) => (PolyCommitment { C: comm_w_list[0][p].C.clone() }, [rq_short, &ry].concat()),
          (2, 0) => (
            PolyCommitment {
              C: (0..comm_w_list[0][p].C.len()).map(
                |i| ((Scalar::one() - ry[0]) * comm_w_list[0][p].C[i].decompress().unwrap()
                            + ry[0] * comm_w_list[1][p].C[i].decompress().unwrap()
                ).compress()
              ).collect()
            },
            [rq_short, &ry[1..]].concat()
          ),
          (4, 0) => (
            PolyCommitment {
              C: (0..comm_w_list[0][p].C.len()).map(
                |i| ((Scalar::one() - ry[0]) * (Scalar::one() - ry[1]) * comm_w_list[0][p].C[i].decompress().unwrap()
                         + (Scalar::one() - ry[0]) * ry[1] * comm_w_list[1][p].C[i].decompress().unwrap()
                         + (ry[0] * (Scalar::one() - ry[1]) * comm_w_list[2][p].C[i].decompress().unwrap()
                         + ry[0] * ry[1] * comm_w_list[3][p].C[i].decompress().unwrap())
                ).compress()
              ).collect()
            },
            [rq_short, &ry[2..]].concat()
          ),
          (4, 1) => (
            PolyCommitment {
              C: (0..comm_w_list[1][p].C.len()).map(
                |i| ((Scalar::one() - ry[0]) * ry[1] * comm_w_list[1][p].C[i].decompress().unwrap()
                         + (ry[0] * (Scalar::one() - ry[1]) * comm_w_list[2][p].C[i].decompress().unwrap()
                         + ry[0] * ry[1] * comm_w_list[3][p].C[i].decompress().unwrap())
                ).compress()
              ).collect()
            },
            [rq_short, &ry[2..]].concat()
          ),
          _ => panic!("PROOF Failed: Unsupported (num_witness_secs, num_shorts) pair: ({}, {})", num_witness_secs, num_shorts)
        }
      };

      self.proof_eval_vars_at_ry_list[p].verify(
        &gens.gens_pc,
        transcript,
        &r,
        &self.comm_vars_at_ry_list[p],
        &comm_combined,
      )?;
    }

    match (num_witness_secs, num_shorts) {
      (_, 0) => {},
      (4, 1) => {
        let comm_combined_short = PolyCommitment { C: comm_w_list[0][0].C.clone() };
        self.proof_eval_short_vars_at_ry.as_ref().unwrap().verify(
          &gens.gens_pc,
          transcript,
          &ry[2..],
          &self.comm_short_vars_at_ry.unwrap(),
          &comm_combined_short,
        )?;
      },
      _ => panic!("PROOF Failed: Unsupported (num_witness_secs, num_shorts) pair: ({}, {})", num_witness_secs, num_shorts)
    }

    // Then on rp
    let mut expected_comm_vars_list: Vec<RistrettoPoint> = self.comm_vars_at_ry_list.iter().map(|i| i.decompress().unwrap()).collect();
    for p in 0..num_instances {
      if num_shorts > 0 {
        assert_eq!(num_witness_secs, 4);
        assert_eq!(num_shorts, 1);
        expected_comm_vars_list[p] += (Scalar::one() - ry[0]) * (Scalar::one() - ry[1]) * self.comm_short_vars_at_ry.unwrap().decompress().unwrap();
      }
      for q in 0..(num_rounds_q - num_proofs[p].log_2()) {
        expected_comm_vars_list[p] *= Scalar::one() - rq[q];
      }
    }
    let EQ_p = EqPolynomial::new(rp.clone()).evals();
    let expected_comm_vars_at_ry = GroupElement::vartime_multiscalar_mul(&EQ_p, expected_comm_vars_list).compress();
    assert_eq!(expected_comm_vars_at_ry, self.comm_vars_at_ry);

    // compute commitment to eval_Z_at_ry = (Scalar::one() - ry[0]) * self.eval_vars_at_ry + ry[0] * poly_input_eval
    let comm_eval_Z_at_ry = &self.comm_vars_at_ry.decompress().unwrap();

    // perform the final check in the second sum-check protocol
    let (eval_A_r, eval_B_r, eval_C_r) = evals;
    let expected_claim_post_phase2 =
      ((r_A * eval_A_r + r_B * eval_B_r + r_C * eval_C_r) * comm_eval_Z_at_ry * p_rp_poly_bound_ry).compress();
    // verify proof that expected_claim_post_phase2 == claim_post_phase2
    self.proof_eq_sc_phase2.verify(
      &gens.gens_sc.gens_1,
      transcript,
      &expected_claim_post_phase2,
      &comm_claim_post_phase2,
    )?;

    Ok([rp, rq_rev, rx, ry])
  }

  // Proving a single instance with multiple proofs specialized for PERM_POLY and CONSIS_CHECK
  // Constraints is of size max_input_rows * base_constraint_size
  // Inputs of each proof is of size max_input_rows * base_input_size
  // However, only first input_rows[i] * base_input_size entries are non-zero, and only these input_rows[i] * base_input_size entries are supplied
  // Moreover, when multiplying the instance with the inputs, only the first input_rows[i] * base_constraint_size products will be non_zero
  // All of max_input_rows, input_rows[i], base_input_size, and base_constraint_size are powers of 2
  //
  // The strategy of prove_single is to redefine the variables such that
  // num_proofs -> num_instances, input_rows -> num_proofs, base_input_size -> num_inputs, base_constraint_size -> num_constraints
  // And apply the data-paralleled version
  pub fn prove_single(
    num_proofs: usize,
    base_constraint_size: usize,
    base_input_size: usize,
    max_input_rows: usize,
    input_rows: Vec<usize>,

    inst: &R1CSInstance,
    w_mat: &Vec<Vec<Scalar>>,
    gens: &R1CSGens,
    transcript: &mut Transcript,
    random_tape: &mut RandomTape,
  ) -> (R1CSProof, Vec<Scalar>, Vec<Scalar>) {
    let timer_prove = Timer::new("R1CSProof::prove");
    transcript.append_protocol_name(R1CSProof::protocol_name());

    // Assert meta values are correct
    assert_eq!(num_proofs, input_rows.len());
    assert_eq!(num_proofs, num_proofs.next_power_of_two());
    assert_eq!(base_constraint_size, base_constraint_size.next_power_of_two());
    assert_eq!(base_input_size, base_input_size.next_power_of_two());
    assert_eq!(max_input_rows, max_input_rows.next_power_of_two());
    assert_eq!(w_mat.len(), num_proofs);
    assert_eq!(inst.get_num_cons(), max_input_rows * base_constraint_size);
    for i in 0..input_rows.len() {
      let input = input_rows[i];
      assert!(input <= max_input_rows);
      assert_eq!(input, input.next_power_of_two());
      assert_eq!(w_mat[i].len(), input);
    }

    let timer_sc_proof_phase1 = Timer::new("prove_sc_phase_one");

    // append input to variables to create a single vector z
    let z_list = w_mat;
    let z_len = z_list[0].len();

    // derive the verifier's challenge tau
    let (num_rounds_q, num_rounds_x, num_rounds_y) = (num_proofs.log_2(), inst.get_num_cons().log_2(), (max_input_rows * base_input_size).log_2());
    let tau = transcript.challenge_vector(b"challenge_tau", num_rounds_q + num_rounds_x);

    // compute the initial evaluation table for R(\tau, x)
    let mut poly_tau = DensePolynomial::new(EqPolynomial::new(tau).evals());
    let (mut poly_Az, mut poly_Bz, mut poly_Cz) =
      inst.multiply_vec(inst.get_num_cons(), z.len(), &z);

    let (sc_proof_phase1, rx, _claims_phase1, blind_claim_postsc1) = R1CSProof::prove_phase_one(
      num_rounds_x,
      &mut poly_tau,
      &mut poly_Az,
      &mut poly_Bz,
      &mut poly_Cz,
      &gens.gens_sc,
      transcript,
      random_tape,
    );
    assert_eq!(poly_tau.len(), 1);
    assert_eq!(poly_Az.len(), 1);
    assert_eq!(poly_Bz.len(), 1);
    assert_eq!(poly_Cz.len(), 1);
    timer_sc_proof_phase1.stop();

    let (tau_claim, Az_claim, Bz_claim, Cz_claim) =
      (&poly_tau[0], &poly_Az[0], &poly_Bz[0], &poly_Cz[0]);
    let (Az_blind, Bz_blind, Cz_blind, prod_Az_Bz_blind) = (
      random_tape.random_scalar(b"Az_blind"),
      random_tape.random_scalar(b"Bz_blind"),
      random_tape.random_scalar(b"Cz_blind"),
      random_tape.random_scalar(b"prod_Az_Bz_blind"),
    );

    println!("\nTotal: {:?}", Az_claim * Bz_claim - Cz_claim);

    let (pok_Cz_claim, comm_Cz_claim) = {
      KnowledgeProof::prove(
        &gens.gens_sc.gens_1,
        transcript,
        random_tape,
        Cz_claim,
        &Cz_blind,
      )
    };

    let (proof_prod, comm_Az_claim, comm_Bz_claim, comm_prod_Az_Bz_claims) = {
      let prod = Az_claim * Bz_claim;
      ProductProof::prove(
        &gens.gens_sc.gens_1,
        transcript,
        random_tape,
        Az_claim,
        &Az_blind,
        Bz_claim,
        &Bz_blind,
        &prod,
        &prod_Az_Bz_blind,
      )
    };

    comm_Az_claim.append_to_transcript(b"comm_Az_claim", transcript);
    comm_Bz_claim.append_to_transcript(b"comm_Bz_claim", transcript);
    comm_Cz_claim.append_to_transcript(b"comm_Cz_claim", transcript);
    comm_prod_Az_Bz_claims.append_to_transcript(b"comm_prod_Az_Bz_claims", transcript);

    // prove the final step of sum-check #1
    let taus_bound_rx = tau_claim;
    let blind_expected_claim_postsc1 = taus_bound_rx * (prod_Az_Bz_blind - Cz_blind);
    let claim_post_phase1 = (Az_claim * Bz_claim - Cz_claim) * taus_bound_rx;
    let (proof_eq_sc_phase1, _C1, _C2) = EqualityProof::prove(
      &gens.gens_sc.gens_1,
      transcript,
      random_tape,
      &claim_post_phase1,
      &blind_expected_claim_postsc1,
      &claim_post_phase1,
      &blind_claim_postsc1,
    );

    let timer_sc_proof_phase2 = Timer::new("prove_sc_phase_two");
    // combine the three claims into a single claim
    let r_A = transcript.challenge_scalar(b"challenege_Az");
    let r_B = transcript.challenge_scalar(b"challenege_Bz");
    let r_C = transcript.challenge_scalar(b"challenege_Cz");
    let claim_phase2 = r_A * Az_claim + r_B * Bz_claim + r_C * Cz_claim;
    let blind_claim_phase2 = r_A * Az_blind + r_B * Bz_blind + r_C * Cz_blind;

    let evals_ABC = {
      // compute the initial evaluation table for R(\tau, x)
      let evals_rx = EqPolynomial::new(rx.clone()).evals();
      let (evals_A, evals_B, evals_C) =
        inst.compute_eval_table_sparse(inst.get_num_cons(), z.len(), &evals_rx);

      assert_eq!(evals_A.len(), evals_B.len());
      assert_eq!(evals_A.len(), evals_C.len());
      (0..evals_A.len())
        .map(|i| r_A * evals_A[i] + r_B * evals_B[i] + r_C * evals_C[i])
        .collect::<Vec<Scalar>>()
    };

    // REMOVE!!!
    let Z_poly_clone = DensePolynomial::new(z.clone());
    let evals_ABC_clone = evals_ABC.clone();

    // another instance of the sum-check protocol
    let (sc_proof_phase2, ry, claims_phase2, blind_claim_postsc2) = R1CSProof::prove_phase_two(
      num_rounds_y,
      &claim_phase2,
      &blind_claim_phase2,
      &mut DensePolynomial::new(z),
      &mut DensePolynomial::new(evals_ABC),
      &gens.gens_sc,
      transcript,
      random_tape,
    );
    timer_sc_proof_phase2.stop();

    let timer_commit = Timer::new("polycommit");
    let (poly_vars, comm_vars, blinds_vars) = {
      // create a multilinear polynomial using the supplied assignment for variables
      let poly_vars = DensePolynomial::new(vars.clone());

      // produce a commitment to the satisfying assignment
      let (comm_vars, blinds_vars) = poly_vars.commit(&gens.gens_pc, Some(random_tape));

      // add the commitment to the prover's transcript
      // comm_vars.append_to_transcript(b"poly_commitment", transcript);
      (poly_vars, comm_vars, blinds_vars)
    };
    timer_commit.stop();

    let timer_polyeval = Timer::new("polyeval");
    let eval_vars_at_ry = poly_vars.evaluate(&ry[1..]);
    let blind_eval = random_tape.random_scalar(b"blind_eval");
    let (proof_eval_vars_at_ry, comm_vars_at_ry) = PolyEvalProof::prove(
      &poly_vars,
      Some(&blinds_vars),
      &ry[1..],
      &eval_vars_at_ry,
      Some(&blind_eval),
      &gens.gens_pc,
      transcript,
      random_tape,
    );
    timer_polyeval.stop();

    // prove the final step of sum-check #2
    let blind_eval_Z_at_ry = (Scalar::one() - ry[0]) * blind_eval;
    let blind_expected_claim_postsc2 = claims_phase2[1] * blind_eval_Z_at_ry;
    let claim_post_phase2 = claims_phase2[0] * claims_phase2[1];
    let (proof_eq_sc_phase2, _C1, _C2) = EqualityProof::prove(
      &gens.gens_pc.gens.gens_1,
      transcript,
      random_tape,
      &claim_post_phase2,
      &blind_expected_claim_postsc2,
      &claim_post_phase2,
      &blind_claim_postsc2,
    );

    timer_prove.stop();

    let poly_ABC = DensePolynomial::new(evals_ABC_clone);
    let Z_eval = Z_poly_clone.evaluate(&ry);
    println!("PROVER EXPECTED 1: {:?}", poly_ABC.evaluate(&ry) * Z_eval);

    (
      R1CSProof {
        comm_vars,
        sc_proof_phase1,
        claims_phase2: (
          comm_Az_claim,
          comm_Bz_claim,
          comm_Cz_claim,
          comm_prod_Az_Bz_claims,
        ),
        pok_claims_phase2: (pok_Cz_claim, proof_prod),
        proof_eq_sc_phase1,
        sc_proof_phase2,
        comm_vars_at_ry,
        proof_eval_vars_at_ry,
        proof_eq_sc_phase2,
      },
      rx,
      ry,
    )
  }

  pub fn verify_single(
    &self,
    num_vars: usize,
    num_cons: usize,
    input: &[Scalar],
    evals: &(Scalar, Scalar, Scalar),
    transcript: &mut Transcript,
    gens: &R1CSGens,
  ) -> Result<(Vec<Scalar>, Vec<Scalar>), ProofVerifyError> {
    transcript.append_protocol_name(R1CSProof::protocol_name());

    input.append_to_transcript(b"input", transcript);

    let n = num_vars;
    // add the commitment to the verifier's transcript
    // self
      // .comm_vars
      // .append_to_transcript(b"poly_commitment", transcript);

    let (num_rounds_x, num_rounds_y) = (num_cons.log_2(), (2 * num_vars).log_2());

    // derive the verifier's challenge tau
    let tau = transcript.challenge_vector(b"challenge_tau", num_rounds_x);

    println!("VERIFIER TAU: {:?}; {}", tau[0], tau.len());

    // verify the first sum-check instance
    let claim_phase1 = Scalar::zero()
      .commit(&Scalar::zero(), &gens.gens_sc.gens_1)
      .compress();
    let (comm_claim_post_phase1, rx) = self.sc_proof_phase1.verify(
      &claim_phase1,
      num_rounds_x,
      3,
      &gens.gens_sc.gens_1,
      &gens.gens_sc.gens_4,
      transcript,
    )?;
    // perform the intermediate sum-check test with claimed Az, Bz, and Cz
    let (comm_Az_claim, comm_Bz_claim, comm_Cz_claim, comm_prod_Az_Bz_claims) = &self.claims_phase2;
    let (pok_Cz_claim, proof_prod) = &self.pok_claims_phase2;

    println!("AAA");

    pok_Cz_claim.verify(&gens.gens_sc.gens_1, transcript, comm_Cz_claim)?;
    proof_prod.verify(
      &gens.gens_sc.gens_1,
      transcript,
      comm_Az_claim,
      comm_Bz_claim,
      comm_prod_Az_Bz_claims,
    )?;

    comm_Az_claim.append_to_transcript(b"comm_Az_claim", transcript);
    comm_Bz_claim.append_to_transcript(b"comm_Bz_claim", transcript);
    comm_Cz_claim.append_to_transcript(b"comm_Cz_claim", transcript);
    comm_prod_Az_Bz_claims.append_to_transcript(b"comm_prod_Az_Bz_claims", transcript);

    let taus_bound_rx: Scalar = (0..rx.len())
      .map(|i| rx[i] * tau[i] + (Scalar::one() - rx[i]) * (Scalar::one() - tau[i]))
      .product();
    let expected_claim_post_phase1 = (taus_bound_rx
      * (comm_prod_Az_Bz_claims.decompress().unwrap() - comm_Cz_claim.decompress().unwrap()))
    .compress();

    // verify proof that expected_claim_post_phase1 == claim_post_phase1
    self.proof_eq_sc_phase1.verify(
      &gens.gens_sc.gens_1,
      transcript,
      &expected_claim_post_phase1,
      &comm_claim_post_phase1,
    )?;

    println!("CCC");

    // derive three public challenges and then derive a joint claim
    let r_A = transcript.challenge_scalar(b"challenege_Az");
    let r_B = transcript.challenge_scalar(b"challenege_Bz");
    let r_C = transcript.challenge_scalar(b"challenege_Cz");

    // r_A * comm_Az_claim + r_B * comm_Bz_claim + r_C * comm_Cz_claim;
    let comm_claim_phase2 = GroupElement::vartime_multiscalar_mul(
      iter::once(&r_A)
        .chain(iter::once(&r_B))
        .chain(iter::once(&r_C)),
      iter::once(&comm_Az_claim)
        .chain(iter::once(&comm_Bz_claim))
        .chain(iter::once(&comm_Cz_claim))
        .map(|pt| pt.decompress().unwrap())
        .collect::<Vec<GroupElement>>(),
    )
    .compress();

    // verify the joint claim with a sum-check protocol
    let (comm_claim_post_phase2, ry) = self.sc_proof_phase2.verify(
      &comm_claim_phase2,
      num_rounds_y,
      2,
      &gens.gens_sc.gens_1,
      &gens.gens_sc.gens_3,
      transcript,
    )?;

    // verify Z(ry) proof against the initial commitment
    self.proof_eval_vars_at_ry.verify(
      &gens.gens_pc,
      transcript,
      &ry[1..],
      &self.comm_vars_at_ry,
      &self.comm_vars,
    )?;

    let poly_input_eval = {
      // constant term
      let mut input_as_sparse_poly_entries = vec![SparsePolyEntry::new(0, Scalar::one())];
      //remaining inputs
      input_as_sparse_poly_entries.extend(
        (0..input.len())
          .map(|i| SparsePolyEntry::new(i + 1, input[i]))
          .collect::<Vec<SparsePolyEntry>>(),
      );
      SparsePolynomial::new(n.log_2(), input_as_sparse_poly_entries).evaluate(&ry[1..])
    };

    // compute commitment to eval_Z_at_ry = (Scalar::one() - ry[0]) * self.eval_vars_at_ry + ry[0] * poly_input_eval
    let comm_eval_Z_at_ry = GroupElement::vartime_multiscalar_mul(
      iter::once(Scalar::one() - ry[0]).chain(iter::once(ry[0])),
      iter::once(&self.comm_vars_at_ry.decompress().unwrap()).chain(iter::once(
        &poly_input_eval.commit(&Scalar::zero(), &gens.gens_pc.gens.gens_1),
      )),
    );

    println!("FFF");

    // perform the final check in the second sum-check protocol
    let (eval_A_r, eval_B_r, eval_C_r) = evals;
    let expected_claim_post_phase2 =
      ((r_A * eval_A_r + r_B * eval_B_r + r_C * eval_C_r) * comm_eval_Z_at_ry).compress();
    // verify proof that expected_claim_post_phase1 == claim_post_phase1
    self.proof_eq_sc_phase2.verify(
      &gens.gens_sc.gens_1,
      transcript,
      &expected_claim_post_phase2,
      &comm_claim_post_phase2,
    )?;

    println!("{:?}", &expected_claim_post_phase2);
    println!("{:?}", &comm_claim_post_phase2);

    Ok((rx, ry))
  }

}

#[cfg(test)]
mod tests {
  use super::*;
  use rand::rngs::OsRng;

  fn produce_tiny_r1cs() -> (R1CSInstance, Vec<Scalar>, Vec<Scalar>) {
    // three constraints over five variables Z1, Z2, Z3, Z4, and Z5
    // rounded to the nearest power of two
    let num_cons = 128;
    let num_vars = 256;
    let num_inputs = 2;

    // encode the above constraints into three matrices
    let mut A: Vec<(usize, usize, Scalar)> = Vec::new();
    let mut B: Vec<(usize, usize, Scalar)> = Vec::new();
    let mut C: Vec<(usize, usize, Scalar)> = Vec::new();

    let one = Scalar::one();
    // constraint 0 entries
    // (Z1 + Z2) * I0 - Z3 = 0;
    A.push((0, 0, one));
    A.push((0, 1, one));
    B.push((0, num_vars + 1, one));
    C.push((0, 2, one));

    // constraint 1 entries
    // (Z1 + I1) * (Z3) - Z4 = 0
    A.push((1, 0, one));
    A.push((1, num_vars + 2, one));
    B.push((1, 2, one));
    C.push((1, 3, one));
    // constraint 3 entries
    // Z5 * 1 - 0 = 0
    A.push((2, 4, one));
    B.push((2, num_vars, one));

    let inst = R1CSInstance::new(num_cons, num_vars, num_inputs, &A, &B, &C);

    // compute a satisfying assignment
    let mut csprng: OsRng = OsRng;
    let i0 = Scalar::random(&mut csprng);
    let i1 = Scalar::random(&mut csprng);
    let z1 = Scalar::random(&mut csprng);
    let z2 = Scalar::random(&mut csprng);
    let z3 = (z1 + z2) * i0; // constraint 1: (Z1 + Z2) * I0 - Z3 = 0;
    let z4 = (z1 + i1) * z3; // constraint 2: (Z1 + I1) * (Z3) - Z4 = 0
    let z5 = Scalar::zero(); //constraint 3

    let mut vars = vec![Scalar::zero(); num_vars];
    vars[0] = z1;
    vars[1] = z2;
    vars[2] = z3;
    vars[3] = z4;
    vars[4] = z5;

    let mut input = vec![Scalar::zero(); num_inputs];
    input[0] = i0;
    input[1] = i1;

    (inst, vars, input)
  }

  #[test]
  fn test_tiny_r1cs() {
    let (inst, vars, input) = tests::produce_tiny_r1cs();
    let is_sat = inst.is_sat(&vars, &input);
    assert!(is_sat);
  }

  #[test]
  fn test_synthetic_r1cs() {
    let (inst, vars, input) = R1CSInstance::produce_synthetic_r1cs(1024, 1024, 10);
    let is_sat = inst.is_sat(&vars, &input);
    assert!(is_sat);
  }

  #[test]
  pub fn check_r1cs_proof() {
    let num_vars = 1024;
    let num_cons = num_vars;
    let num_inputs = 10;
    let (inst, vars, input) = R1CSInstance::produce_synthetic_r1cs(num_cons, num_vars, num_inputs);

    let gens = R1CSGens::new(b"test-m", num_cons, num_vars);

    let mut random_tape = RandomTape::new(b"proof");
    let mut prover_transcript = Transcript::new(b"example");
    let (proof, rx, ry) = R1CSProof::prove(
      &inst,
      vars,
      &input,
      &gens,
      &mut prover_transcript,
      &mut random_tape,
    );

    let inst_evals = inst.evaluate(&rx, &ry);

    let mut verifier_transcript = Transcript::new(b"example");
    assert!(proof
      .verify(
        inst.get_num_vars(),
        inst.get_num_cons(),
        &input,
        &inst_evals,
        &mut verifier_transcript,
        &gens,
      )
      .is_ok());
  }
}
