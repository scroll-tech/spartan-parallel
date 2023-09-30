#![allow(clippy::too_many_arguments)]
use crate::custom_dense_mlpoly::{PolyEvalProof_PQX, PolyCommitment_PQX};

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
use super::sparse_mlpoly::{SparsePolyEntry, SparsePolynomial};
use super::sumcheck::ZKSumcheckInstanceProof;
use super::timer::Timer;
use super::transcript::{AppendToTranscript, ProofTranscript};
use core::{iter, num};
use std::env::var;
use merlin::Transcript;
use serde::{Deserialize, Serialize};

// TODO: Need to reduce the complexity of TAU!
// TODO: Need to reduce the complexity of Z_poly!

#[derive(Serialize, Deserialize, Debug)]
pub struct R1CSProof {
  comm_vars: PolyCommitment_PQX,
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
  comm_vars_at_ry: CompressedGroup,
  proof_eval_vars_at_ry: PolyEvalProof_PQX,
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
  gens_sc: R1CSSumcheckGens,
  gens_pc: PolyCommitmentGens,
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
    evals_tau: &mut DensePolynomial_PQX,
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
        evals_tau,
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

  pub fn prove(
    max_num_proofs: usize,
    num_proofs: &Vec<usize>,
    inst: &R1CSInstance,
    vars_mat: Vec<Vec<Vec<Scalar>>>,
    input_mat: &Vec<Vec<Vec<Scalar>>>,
    gens: &R1CSGens,
    transcript: &mut Transcript,
    random_tape: &mut RandomTape,
  ) -> (R1CSProof, Vec<Scalar>, Vec<Scalar>, Vec<Scalar>, Vec<Scalar>) { 
    let timer_prove = Timer::new("R1CSProof::prove");
    transcript.append_protocol_name(R1CSProof::protocol_name());

    let num_instances = vars_mat.len();
    assert_eq!(num_instances.next_power_of_two(), num_instances);
    assert!(input_mat.len() == num_instances);

    assert_eq!(max_num_proofs.next_power_of_two(), max_num_proofs);
    for i in 0..num_instances {
      assert!(input_mat[i].len() <= max_num_proofs);
      assert!(input_mat[i].len() == input_mat[i].len().next_power_of_two());
      assert!(vars_mat[i].len() == input_mat[i].len());
    }

    let num_cons = inst.get_num_cons();

    // we currently require the number of |inputs| + 1 to be at most number of vars
    for i in 0..num_instances {
      for j in 0..input_mat[i].len() {
        assert!(input_mat[i][j].len() < vars_mat[i][j].len());
      }
    }

    for input_list in input_mat {
      for input in input_list {
        input.append_to_transcript(b"input", transcript);
      }
    }

    let timer_commit = Timer::new("polycommit");
    let (poly_vars, comm_vars, blinds_vars) = {
      // create a multilinear polynomial using the supplied assignment for variables
      let poly_vars = DensePolynomial_PQX::new_rev(&vars_mat, num_proofs, max_num_proofs);

      // produce a commitment to the satisfying assignment
      let (comm_vars, blinds_vars) = poly_vars.commit(&gens.gens_pc, Some(random_tape));

      // add the commitment to the prover's transcript
      comm_vars.append_to_transcript(b"poly_commitment", transcript);
      (poly_vars, comm_vars, blinds_vars)
    };
    timer_commit.stop();

    let timer_sc_proof_phase1 = Timer::new("prove_sc_phase_one");

    // append input to variables to create a single vector z
    let mut z_mat = Vec::new();
    for i in 0..num_instances {
      z_mat.push(Vec::new());
      for j in 0..input_mat[i].len() {
        let z = {
          let input = input_mat[i][j].clone();
          let vars = vars_mat[i][j].clone();
          let num_inputs = input.len();
          let num_vars = vars.len();
          let mut z = vars;
          z.extend(&vec![Scalar::one()]); // add constant term in z
          z.extend(input);
          z.extend(&vec![Scalar::zero(); num_vars - num_inputs - 1]); // we will pad with zeros
          z
        };
        z_mat[i].push(z);
      }
    }
    let z_len = z_mat[0][0].len();

    // derive the verifier's challenge \tau
    let (num_rounds_p, num_rounds_q, num_rounds_x, num_rounds_y) = 
      (num_instances.log_2(), max_num_proofs.log_2(), num_cons.log_2(), z_len.log_2());
    let tau = transcript.challenge_vector(b"challenge_tau", num_rounds_x + num_rounds_q + num_rounds_p);

    // compute the initial evaluation table for R(\tau, x)
    // let mut poly_tau = DensePolynomial::new(EqPolynomial::new(tau).evals_disjoint_rounds(num_rounds_x, num_rounds_q, num_rounds_p, &num_proofs));
    let mut poly_tau = DensePolynomial_PQX::new(
      &EqPolynomial::new(tau).evals_PQX(num_rounds_p, num_rounds_q, num_rounds_x), 
      &vec![max_num_proofs; num_instances], 
      max_num_proofs);
    let (mut poly_Az, mut poly_Bz, mut poly_Cz) =
      inst.multiply_vec_bunched(num_instances, num_proofs, max_num_proofs, num_cons, z_len, &z_mat);

    // Sumcheck 1: (Az * Bz - Cz) * eq(x, q, p) = 0
    let (sc_proof_phase1, rx, _claims_phase1, blind_claim_postsc1) = R1CSProof::prove_phase_one(
      num_rounds_x + num_rounds_q + num_rounds_p,
      num_rounds_x,
      num_rounds_q,
      num_rounds_p,
      &num_proofs,
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
      (&poly_tau.index(0, 0, 0), &poly_Az.index(0, 0, 0), &poly_Bz.index(0, 0, 0), &poly_Cz.index(0, 0, 0));

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
    let rp = rp.to_vec();

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
        inst.compute_eval_table_sparse(inst.get_num_cons(), z_len, &evals_rx);

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

    let timer_polyeval = Timer::new("polyeval");
    let eval_vars_at_ry = poly_vars.evaluate(&rp, &rq_rev.to_vec(), &ry[1..].to_vec());

    let blind_eval = random_tape.random_scalar(b"blind_eval");

    let (proof_eval_vars_at_ry, comm_vars_at_ry) = PolyEvalProof_PQX::prove(
      poly_vars,
      &num_proofs,
      Some(&blinds_vars),
      &rp,
      &rq_rev,
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
    let blind_expected_claim_postsc2 = claims_phase2[1] * blind_eval_Z_at_ry * claims_phase2[2];
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
      rp,
      rq_rev,
      rx,
      ry,
    )
  }

  pub fn verify(
    &self,
    num_vars: usize,
    num_cons: usize,
    num_instances: usize,
    max_num_proofs: usize,
    num_proofs: &Vec<usize>,
    input_mat: &Vec<Vec<Vec<Scalar>>>,
    evals: &(Scalar, Scalar, Scalar),
    transcript: &mut Transcript,
    gens: &R1CSGens,
  ) -> Result<(Vec<Scalar>, Vec<Scalar>, Vec<Scalar>, Vec<Scalar>), ProofVerifyError> {
    transcript.append_protocol_name(R1CSProof::protocol_name());

    for input_list in input_mat {
      for input in input_list {
        input.append_to_transcript(b"input", transcript);
      }
    }

    let n = num_vars;
    // add the commitment to the verifier's transcript
    self
      .comm_vars
      .append_to_transcript(b"poly_commitment", transcript);

    let (num_rounds_x, num_rounds_p, num_rounds_q, num_rounds_y) = (num_cons.log_2(), num_instances.log_2(), max_num_proofs.log_2(), (2 * num_vars).log_2());

    // derive the verifier's challenge tau
    let tau = transcript.challenge_vector(b"challenge_tau", num_rounds_x + num_rounds_q + num_rounds_p);

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

    // taus_bound_rx is really taus_bound_rx_rq_rp
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

    // Separate the result rx into rp_round1, rq, and rx
    let (rx, rq_rev) = rx.split_at(num_rounds_x);
    let (rq_rev, rp_round1) = rq_rev.split_at(num_rounds_q);
    let rx = rx.to_vec();
    let rq_rev = rq_rev.to_vec();
    let rq: Vec<Scalar> = rq_rev.clone().into_iter().rev().collect();
    let rp_round1 = rp_round1.to_vec();

    // Separate ry into rp and ry
    let (rp, ry) = ry.split_at(num_rounds_p);
    let rp = rp.to_vec();
    let ry = ry.to_vec();

    // An Eq function to match p with rp
    let p_rp_poly_bound_ry: Scalar = (0..rp.len())
      .map(|i| rp[i] * rp_round1[i] + (Scalar::one() - rp[i]) * (Scalar::one() - rp_round1[i]))
      .product();

    // verify Z(rp, rq, ry) proof against the initial commitment
    self.proof_eval_vars_at_ry.verify(
      &gens.gens_pc,
      transcript,
      num_proofs,
      &rp,
      &rq_rev,
      &ry[1..],
      &self.comm_vars_at_ry,
      &self.comm_vars,
    )?;

    let poly_input_eval = {
      let mut input_as_sparse_poly_entries = Vec::new();
      for i in 0..num_instances {
        for j in 0..input_mat[i].len() {
          // constant term
          input_as_sparse_poly_entries.extend([SparsePolyEntry::new((i * max_num_proofs + j) * n, Scalar::one())]);
          // remaining inputs
          input_as_sparse_poly_entries.extend(
            (0..input_mat[i][j].len())
              .map(|k| SparsePolyEntry::new((i * max_num_proofs + j) * n + k + 1, input_mat[i][j][k]))
              .collect::<Vec<SparsePolyEntry>>(),
          );
        }
      }
      SparsePolynomial::new(num_instances.log_2() + max_num_proofs.log_2() + n.log_2(), input_as_sparse_poly_entries).evaluate(&[rp.clone(), rq.clone(), ry[1..].to_vec()].concat())
    };

    // compute commitment to eval_Z_at_ry = (Scalar::one() - ry[0]) * self.eval_vars_at_ry + ry[0] * poly_input_eval
    let comm_eval_Z_at_ry = GroupElement::vartime_multiscalar_mul(
      iter::once(Scalar::one() - ry[0]).chain(iter::once(ry[0])),
      iter::once(&self.comm_vars_at_ry.decompress().unwrap()).chain(iter::once(
        &poly_input_eval.commit(&Scalar::zero(), &gens.gens_pc.gens.gens_1),
      )),
    );

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

    Ok((rp, rq_rev, rx, ry))
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
