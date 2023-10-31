//! An accumulator: s = 1 + 2 + 3 computed with loops
//! The pseudocode is:
//!   i = 0
//!   s = 0
//!   while i != 4:
//!     s = s + i
//!     i = i + 1
//! Which, when converted to blocks, is:
//! Block 1:                        Block 2:
//!   assert b == 0                   assert b == 1
//!   i = 0                           s = s + i
//!   s = 0                           i = i + 1
//!   if i != 4:                      if i != 4:
//!     b = 1                           b = 1
//!   else:                           else:
//!     b = 2                           b = 2
//!
//! Converting each block to constraints:
//! Block 1:                        Block 2:
//!   b0 = b_in                       b0 = b_in
//!   i0 = i_in                       i0 = i_in
//!   s0 = s_in                       s0 = s_in
//!   0 = b0                          1 = b0
//!   0 = i0                          i0 = s1 - s0
//!   0 = s0                          1 = i1 - i0
//!   Z1 = (i0 - 4) * Z0              Z1 = (i1 - 4) * Z0
//!   0 = B0 * (Z1 - 1)               0 = B0 * (Z1 - 1)
//!   0 = B0 * (b1 - 1)               0 = B0 * (b1 - 1)
//!   0 = (1 - B0) * (i0 - 4)         0 = (1 - B0) * (i1 - 4)
//!   0 = (1 - B0) * (b1 - 2)         0 = (1 - B0) * (b1 - 2)
//!   b_out = b1                      b_out = b1
//!   i_out = i0                      i_out = i1
//!   s_out = s0                      s_out = s1
//! 
//! Finally, consistency check:
//!   Permutation on (b_in, i_in, s_in, b_out, i_out, s_out)
//!   Consistency check on (b_in, i_in, s_in, b_out, i_out, s_out)
//!
#![allow(clippy::assertions_on_result_states)]
use std::ops::Neg;

use curve25519_dalek::scalar::Scalar;
use libspartan::{Instance, SNARKGens, VarsAssignment, SNARK, InputsAssignment};
use merlin::Transcript;

#[allow(non_snake_case)]
fn produce_r1cs() -> (
  usize,
  usize,
  usize,
  usize,
  usize,
  Vec<usize>,
  usize,
  Vec<usize>,
  Instance,
  usize,
  usize,
  usize,
  Instance,
  usize,
  usize,
  Instance,
  usize,
  usize,
  Instance,
  Vec<Vec<VarsAssignment>>,
  Vec<Vec<InputsAssignment>>,
  Vec<InputsAssignment>
) {
  // bad test cases for debugging
  // set them to unreachable values to prevent bad tests
  // let bad_instance = 3;
  // let bad_proof = 1;

  // Separate instances into three lists:
  // BLOCK: correctness within a block
  // CONSIS: consistency between blocks
  // PERM: permutation between two orderings
  //
  // Separate inputs into two lists:
  // BLOCK_ORDER
  // EXEC_ORDER
  //
  // Separate vars into three lists
  // BLOCK, CONSIS, PERM

  // num_vars should be consistent accross the instances
  // everything else is instance-specific
  // num_vars = num_inputs
  // Divide inputs into (1, input, 1, output)
  let num_vars = 16;

  let zero = Scalar::zero().to_bytes();
  let one = Scalar::one().to_bytes();
  let two = Scalar::from(2u32).to_bytes();
  let three = Scalar::from(3u32).to_bytes();
  let four = Scalar::from(4u32).to_bytes();
  let six = Scalar::from(6u32).to_bytes();

  // args are in (variable, constant) pairs
  fn gen_constr(
    mut A: Vec<(usize, usize, [u8; 32])>, mut B: Vec<(usize, usize, [u8; 32])>, mut C: Vec<(usize, usize, [u8; 32])>, V_cnst: usize,
    i: usize, args_A: Vec<(usize, isize)>, args_B: Vec<(usize, isize)>, args_C: Vec<(usize, isize)>) -> (
      Vec<(usize, usize, [u8; 32])>, Vec<(usize, usize, [u8; 32])>, Vec<(usize, usize, [u8; 32])>
    ) {
    let zero = Scalar::zero().to_bytes();
    let one = Scalar::one().to_bytes();
    let two = Scalar::from(2u32).to_bytes();
    let minus_one = Scalar::one().neg().to_bytes();
    let minus_two = Scalar::from(2u32).neg().to_bytes();
    let minus_four = Scalar::from(4u32).neg().to_bytes();
    let int_to_scalar = |i| {
      match i {
        0  => zero,
        1  => one,
        2  => two,
        -1 => minus_one,
        -2 => minus_two,
        -4 => minus_four,
        _  => panic!("Unsupported constant!")
      }
    };
    for vars in &args_A {
      let sc = int_to_scalar(vars.1);
      A.push((i, vars.0, sc));
    }
    if args_B.len() == 0 {
      B.push((i, V_cnst, one));
    }
    for vars in &args_B {
      let sc = int_to_scalar(vars.1);
      B.push((i, vars.0, sc));
    }
    for vars in &args_C {
      let sc = int_to_scalar(vars.1);
      C.push((i, vars.0, sc));
    }
    (A, B, C)
  }
  
  // --
  // BLOCK Instances
  // --

  //                    0    1    2    3    4    5    6    7    8
  // variable orders:  b0   i0   s0   b1   i1   s1   Z0   Z1   B0 
  // input orders:  valid  b_i  i_i  s_i    1  b_o  i_o  s_o
  let V_b0 = 0;
  let V_i0 = 1;
  let V_s0 = 2;
  let V_b1 = 3;
  let V_i1 = 4;
  let V_s1 = 5;
  let V_Z0 = 6;
  let V_Z1 = 7;
  let V_B0 = 8;
  // let V_valid = num_vars;
  let V_bi = num_vars + 1;
  let V_ii = num_vars + 2;
  let V_si = num_vars + 3;
  let V_cnst = num_vars + 4;
  let V_bo = num_vars + 5;
  let V_io = num_vars + 6;
  let V_so = num_vars + 7;

  // parameters of the BLOCK instance
  // maximum value among the R1CS instances
  let block_num_cons = 16;
  let block_num_non_zero_entries = 19;
  // Number of R1CS instances
  let block_num_instances = 2;
  // Number of proofs of each R1CS instance
  // OBTAINED DURING COMPILE TIME
  let block_max_num_proofs_bound = 8;
  let block_num_proofs_bound = vec![8, 1];
  // OBTAINED DURING RUNTIME
  let block_max_num_proofs = 4;
  let block_num_proofs = vec![4, 1];

  let block_inst = {
    let mut A_list = Vec::new();
    let mut B_list = Vec::new();
    let mut C_list = Vec::new();

    // Instance 0: block 1
    // Instances need to be sorted in reverse # of proofs order
    let (A, B, C) = {
      let mut A: Vec<(usize, usize, [u8; 32])> = Vec::new();
      let mut B: Vec<(usize, usize, [u8; 32])> = Vec::new();
      let mut C: Vec<(usize, usize, [u8; 32])> = Vec::new();

      // R1CS:
      // b0 = b_in
      (A, B, C) = gen_constr(A, B, C, V_cnst,
        0, vec![(V_b0, 1)], vec![], vec![(V_bi, 1)]);
      // i0 = i_in
      (A, B, C) = gen_constr(A, B, C, V_cnst,
        1, vec![(V_i0, 1)], vec![], vec![(V_ii, 1)]);
      // s0 = s_in
      (A, B, C) = gen_constr(A, B, C, V_cnst,
        2, vec![(V_s0, 1)], vec![], vec![(V_si, 1)]);
      // b0 = 1
      (A, B, C) = gen_constr(A, B, C, V_cnst,
        3, vec![(V_b0, 1)], vec![], vec![(V_cnst, 1)]);
      // s1 - s0 = i0
      (A, B, C) = gen_constr(A, B, C, V_cnst,
        4, vec![(V_s1, 1), (V_s0, -1)], vec![], vec![(V_i0, 1)]);
      // i1 - i0 = 1
      (A, B, C) = gen_constr(A, B, C, V_cnst,
        5, vec![(V_i1, 1), (V_i0, -1)], vec![], vec![(V_cnst, 1)]);
      // (i1 - 4) * Z0 = Z1
      (A, B, C) = gen_constr(A, B, C, V_cnst,
        6, vec![(V_i1, 1), (V_cnst, -4)], vec![(V_Z0, 1)], vec![(V_Z1, 1)]);
      // B0 * (Z1 - 1) = 0
      (A, B, C) = gen_constr(A, B, C, V_cnst,
        7, vec![(V_B0, 1)], vec![(V_Z1, 1), (V_cnst, -1)], vec![]);
      // B0 * (b1 - 1) = 0
      (A, B, C) = gen_constr(A, B, C, V_cnst,
        8, vec![(V_B0, 1)], vec![(V_b1, 1), (V_cnst, -1)], vec![]);
      // (1 - B0) * (i1 - 4) = 0
      (A, B, C) = gen_constr(A, B, C, V_cnst,
        9, vec![(V_cnst, 1), (V_B0, -1)], vec![(V_i1, 1), (V_cnst, -4)], vec![]);
      // (1 - B0) * (b1 - 2) = 0
      (A, B, C) = gen_constr(A, B, C, V_cnst,
        10, vec![(V_cnst, 1), (V_B0, -1)], vec![(V_b1, 1), (V_cnst, -2)], vec![]);
      // b_out = b1
      (A, B, C) = gen_constr(A, B, C, V_cnst,
        11, vec![(V_bo, 1)], vec![], vec![(V_b1, 1)]);
      // i_out = i1
      (A, B, C) = gen_constr(A, B, C, V_cnst,
        12, vec![(V_io, 1)], vec![], vec![(V_i1, 1)]);
      // s_out = s1
      (A, B, C) = gen_constr(A, B, C, V_cnst,
        13, vec![(V_so, 1)], vec![], vec![(V_s1, 1)]);

      (A, B, C)
    };
    A_list.push(A);
    B_list.push(B);
    C_list.push(C);
    
    // Instance 1: block 0
    let (A, B, C) = {
      let mut A: Vec<(usize, usize, [u8; 32])> = Vec::new();
      let mut B: Vec<(usize, usize, [u8; 32])> = Vec::new();
      let mut C: Vec<(usize, usize, [u8; 32])> = Vec::new();

      // R1CS:
      // b0 = b_in
      (A, B, C) = gen_constr(A, B, C, V_cnst,
        0, vec![(V_b0, 1)], vec![], vec![(V_bi, 1)]);
      // i0 = i_in
      (A, B, C) = gen_constr(A, B, C, V_cnst,
        1, vec![(V_i0, 1)], vec![], vec![(V_ii, 1)]);
      // s0 = s_in
      (A, B, C) = gen_constr(A, B, C, V_cnst,
        2, vec![(V_s0, 1)], vec![], vec![(V_si, 1)]);
      // b0 = 0
      (A, B, C) = gen_constr(A, B, C, V_cnst,
        3, vec![(V_b0, 1)], vec![], vec![]);
      // i0 = 0
      (A, B, C) = gen_constr(A, B, C, V_cnst,
        4, vec![(V_i0, 1)], vec![], vec![]);
      // s0 = 0
      (A, B, C) = gen_constr(A, B, C, V_cnst,
        5, vec![(V_s0, 1)], vec![], vec![]);
      // (i0 - 4) * Z0 = Z1
      (A, B, C) = gen_constr(A, B, C, V_cnst,
        6, vec![(V_i0, 1), (V_cnst, -4)], vec![(V_Z0, 1)], vec![(V_Z1, 1)]);
      // B0 * (Z1 - 1) = 0
      (A, B, C) = gen_constr(A, B, C, V_cnst,
        7, vec![(V_B0, 1)], vec![(V_Z1, 1), (V_cnst, -1)], vec![]);
      // B0 * (b1 - 1) = 0
      (A, B, C) = gen_constr(A, B, C, V_cnst,
        8, vec![(V_B0, 1)], vec![(V_b1, 1), (V_cnst, -1)], vec![]);
      // (1 - B0) * (i0 - 4) = 0
      (A, B, C) = gen_constr(A, B, C, V_cnst,
        9, vec![(V_cnst, 1), (V_B0, -1)], vec![(V_i0, 1), (V_cnst, -4)], vec![]);
      // (1 - B0) * (b1 - 2) = 0
      (A, B, C) = gen_constr(A, B, C, V_cnst,
        10, vec![(V_cnst, 1), (V_B0, -1)], vec![(V_b1, 1), (V_cnst, -2)], vec![]);
      // b_out = b1
      (A, B, C) = gen_constr(A, B, C, V_cnst,
        11, vec![(V_bo, 1)], vec![], vec![(V_b1, 1)]);
      // i_out = i0
      (A, B, C) = gen_constr(A, B, C, V_cnst,
        12, vec![(V_io, 1)], vec![], vec![(V_i0, 1)]);
      // s_out = s0
      (A, B, C) = gen_constr(A, B, C, V_cnst,
        13, vec![(V_so, 1)], vec![], vec![(V_s0, 1)]);

      (A, B, C)
    };
    A_list.push(A);
    B_list.push(B);
    C_list.push(C);

    let block_inst = Instance::new(block_num_instances, block_num_cons, 2 * num_vars, &A_list, &B_list, &C_list).unwrap();
    
    block_inst
  };

  // --
  // CONSIS Instances
  // --
  let input_output_cutoff = 4;

  // parameters of the CONSIS instance
  // maximum value among the R1CS instances
  // Each CONSIS proof takes in two input assignments and check their consistency
  let consis_num_cons = 16;
  let consis_num_non_zero_entries = 2 * input_output_cutoff;
  // Number of proofs of each R1CS instance
  let consis_num_proofs: usize = 8;

  let V_cnst = input_output_cutoff;
  let V_valid = num_vars;

  let consis_inst = {
    let mut A_list = Vec::new();
    let mut B_list = Vec::new();
    let mut C_list = Vec::new();
    
    // Check output of the last block is the input of the next block
    let (A, B, C) = {
      let mut A: Vec<(usize, usize, [u8; 32])> = Vec::new();
      let mut B: Vec<(usize, usize, [u8; 32])> = Vec::new();
      let mut C: Vec<(usize, usize, [u8; 32])> = Vec::new();

      // R1CS:
      // Consistency of the constant 1, only if the second part of the input is valid
      (A, B, C) = gen_constr(A, B, C, input_output_cutoff,
        0, vec![(V_cnst, 1), (num_vars + V_cnst, -1)], vec![(V_valid, 1)], vec![]);
      // Consistency of inputs, only if the second part of the input is valid
      for i in 1..input_output_cutoff {
        (A, B, C) = gen_constr(A, B, C, input_output_cutoff,
          i, vec![(input_output_cutoff + i, 1), (num_vars + i, -1)], vec![(V_valid, 1)], vec![]);
      }

      (A, B, C)
    };
    A_list.push(A);
    B_list.push(B);
    C_list.push(C);

    let consis_inst = Instance::new(1, consis_num_cons, 2 * num_vars, &A_list, &B_list, &C_list).unwrap();
    
    consis_inst
  };

  // --
  // PERM Instances
  // --
  // PERM is consisted of five instances
  // PERM_PRELIM checks the correctness of (r, r^2, ...)
  // PERM_BLOCK_ROOT and PERM_BLOCK_PROD compute the polynomial defined by block_inputs
  // PERM_EXEC_ROOT and PERM_EXEC_PROD compute the polynomial defined by exec_inputs
  // Finally, the verifier checks that the two products are the same
  // The product is defined by PROD = \prod(\tau - (\sum_i a_i * r^{i-1}))
  // There is only one proof
  
  // PERM_PRELIM
  let perm_prelim_num_cons = num_vars - 2;
  let perm_prelim_num_non_zero_entries = num_vars - 2;
  let perm_prelim_inst = {
    let mut A_list = Vec::new();
    let mut B_list = Vec::new();
    let mut C_list = Vec::new();

    let (A, B, C) = {
      let mut A: Vec<(usize, usize, [u8; 32])> = Vec::new();
      let mut B: Vec<(usize, usize, [u8; 32])> = Vec::new();
      let mut C: Vec<(usize, usize, [u8; 32])> = Vec::new();

      let V_r = 1;

      for i in 2..num_vars {
        (A, B, C) = gen_constr(A, B, C, V_cnst,
          i - 2, vec![(i - 1, 1)], vec![(V_r, 1)], vec![(i, 1)]);
      }
      (A, B, C)
    };

    A_list.push(A);
    B_list.push(B);
    C_list.push(C);

    let perm_block_inst = Instance::new(1, perm_prelim_num_cons, num_vars, &A_list, &B_list, &C_list).unwrap();
    perm_block_inst
  };

  let Z_section_size = block_num_instances * block_max_num_proofs_bound * num_vars;
  
  // PERM_BLOCK_ROOT
  let perm_block_root_num_cons = num_vars + 2;
  let perm_block_root_num_non_zero_entries = 2 * num_vars + 2;
  let perm_block_root_inst = {
    let mut A_list = Vec::new();
    let mut B_list = Vec::new();
    let mut C_list = Vec::new();

    let (A, B, C) = {
      let mut A: Vec<(usize, usize, [u8; 32])> = Vec::new();
      let mut B: Vec<(usize, usize, [u8; 32])> = Vec::new();
      let mut C: Vec<(usize, usize, [u8; 32])> = Vec::new();

      // Witnesses of PERM_BLOCK_ROOT is consisted of [w0, w1, w2, w3], each of size num_vars
      // w0: tau, r, r^2, ...
      // w1: one block_inputs entry: i0, i1, ...
      // w2: one block_inputs entry dot product <r>: i0, i1 * r, i2 * r^2, i3 * r^3, ...
      // w3[0]: valid bit, should match block_inputs[0]
      // w3[1]: one root of the polynomial: (tau - (i0 + i1 * r + i2 * r^2 - ...))
      let V_tau = 0;
      // The best way to find a CONSTANT ONE is to peak into the constant term of the first input, which is guaranteed to be valid
      let V_cnst = num_vars + input_output_cutoff;

      let mut constraint_count = 0;

      // correctness of w2
      (A, B, C) = gen_constr(A, B, C, V_cnst, // for i0
        constraint_count, vec![(num_vars, 1)], vec![], vec![(2 * num_vars, 1)]);
      constraint_count += 1;
      for i in 1..num_vars {
        (A, B, C) = gen_constr(A, B, C, V_cnst, // for i1..
          constraint_count, vec![(num_vars + i, 1)], vec![(i, 1)], vec![(2 * num_vars + i, 1)]);
        constraint_count += 1;
      }
      // correctness of w3[0]
      (A, B, C) = gen_constr(A, B, C, V_cnst, 
        constraint_count, vec![(num_vars, 1)], vec![], vec![(3 * num_vars, 1)]);
      constraint_count += 1;
      // correctness of w3[1]
      (A, B, C) = gen_constr(A, B, C, V_cnst, constraint_count,
          [vec![(V_tau, 1)], (0..num_vars).map(|i| (2 * num_vars + i, -1)).collect()].concat(), 
          vec![], 
          vec![(3 * num_vars + 1, 1)]);
      constraint_count += 1;

      (A, B, C)   
    };

    A_list.push(A);
    B_list.push(B);
    C_list.push(C);

    let perm_block_root_inst = Instance::new(1, perm_block_root_num_cons, 4 * num_vars, &A_list, &B_list, &C_list).unwrap();
    
    perm_block_root_inst
  };

  // PERM_BLOCK takes in a num_vars (V) * (4 * num_instances (P) * max_num_proofs (Qmax)) vector as Z, consisted of
  // Z[0]: \tau, r, r^2, ... r^{V-1}
  // Z[1..V]: Empty
  // Z[V..2*V]: block_inputs, in the order of instances. Some of them might be empty
  // Z[2*V..3*V]: entry i stores block_inputs[q][i] * r^i
  // Z[3*V..4*V]: entry 0 stores x_q = block_inputs[q][i] * r^i,
  //              entry 1 stores the CORRECT cumulative product (tau - x_0) * ... * (tau - x_q) for all VALID x_i
  //              Z[i][1] = valid ? (tau - Z[i][0]) * Z[prev][1] : Z[prev][1] = Z[prev][1] + (tau - Z[i][0] - 1) * valid * Z[prev][1]
  //              entry 2 stores (tau - Z[i][0] - 1) * valid
  //              entry 3 stores (tau - Z[i][0] - 1) * valid * Z[prev][1]
  //              all other entries are 0
  // Note: this means that num_vars >= 4, which is almost always the case

  // NOTE: During actual proving, only the constraints corresponding to valid inputs will be evaluated.
  // As a result, if front-end can provide the number of times each BLOCK INSTANCE will be executed, we can avoid adding unnecessary entries.
  // This value is captured by block_num_proofs_bound

  let (perm_block_num_vars, perm_block_inst, perm_block_num_cons, perm_block_num_non_zero_entries) = {
    let mut constraint_count = 0;

    let mut A_list = Vec::new();
    let mut B_list = Vec::new();
    let mut C_list = Vec::new();
    
    let (A, B, C) = {
      let mut A: Vec<(usize, usize, [u8; 32])> = Vec::new();
      let mut B: Vec<(usize, usize, [u8; 32])> = Vec::new();
      let mut C: Vec<(usize, usize, [u8; 32])> = Vec::new();

      // Where things are defined
      let V_tau = 0;
      let V_r = 1;
      // The best way to find a CONSTANT ONE is to peak into the constant term of the first input, which is guaranteed to be valid
      let V_cnst = Z_section_size + input_output_cutoff;

      // R1CS:
      // Z0: Correctness of r^2, r^3, ...
      for i in 2..num_vars {
        (A, B, C) = gen_constr(A, B, C, V_cnst,
          constraint_count, vec![(i - 1, 1)], vec![(V_r, 1)], vec![(i, 1)]);
        constraint_count += 1;
      }
      // Z1: Correctness of block_io * <r^0, r, r^2, ...>
      for p in 0..block_num_instances {
        // Only add the constraint if Z[i] might be valid
        for q in 0..block_num_proofs_bound[p] {
          let i = p * block_num_instances + q;
          (A, B, C) = gen_constr(A, B, C, V_cnst,
            //                                block_io[i][0]                                  1               block_io[i][0] * 1
            constraint_count, vec![(Z_section_size + i * num_vars, 1)], vec![], vec![(2 * Z_section_size + i * num_vars, 1)]);
          constraint_count += 1;
          for j in 1..num_vars {
            (A, B, C) = gen_constr(A, B, C, V_cnst,
              //                                block_io[i][j]                                       r^j                   block_io[i][j] * r^j
              constraint_count, vec![(Z_section_size + i * num_vars + j, 1)], vec![(j, 1)], vec![(2 * Z_section_size + i * num_vars + j, 1)]);
            constraint_count += 1;
          }
        }
      }
      // Z2: Correctness of x[i] = sum_j(block_io[i][j] * r^j)
      for p in 0..block_num_instances {
        // Only add the constraint if Z[i] might be valid
        for q in 0..block_num_proofs_bound[p] {
          let i = p * block_num_instances + q;
          (A, B, C) = gen_constr(A, B, C, V_cnst, constraint_count,
              (0..num_vars).map(|j| (2 * Z_section_size + i * num_vars + j, 1)).collect(), 
              vec![], 
              vec![(3 * Z_section_size + i * num_vars, 1)]);
          constraint_count += 1;
        }
      }
      // Z3: Correctness of cumulative product
      // x[0] and tau - x[0]
      (A, B, C) = gen_constr(A, B, C, V_cnst,
        constraint_count, vec![(V_tau, 1), (3 * Z_section_size, -1)], vec![], vec![(3 * Z_section_size + 1, 1)]);
      constraint_count += 1;
      // Note: we are not multiplying consecutive ones together, but rather consecutive VALID ones
      let mut i_last = 0;
      for p in 0..block_num_instances {
        // Only add the constraint if Z[i] might be valid
        for q in 0..block_num_proofs_bound[p] {
          let i = p * block_num_instances + q;
          // (tau - Z[i][0] - 1) * valid, in slot 2
          let V_valid = Z_section_size + i * num_vars;
          (A, B, C) = gen_constr(A, B, C, V_cnst, constraint_count, 
            vec![(V_tau, 1), (3 * Z_section_size + i * num_vars, -1), (V_cnst, -1)], 
            vec![(V_valid, 1)], 
            vec![(3 * Z_section_size + i * num_vars + 2, 1)]);
          constraint_count += 1;
          // (tau - Z[i][0] - 1) * valid * Z[prev][1] in slot 3
          (A, B, C) = gen_constr(A, B, C, V_cnst, constraint_count, 
            vec![(3 * Z_section_size + i * num_vars + 2, 1)], 
            vec![(3 * Z_section_size + i_last * num_vars + 1, 1)], 
            vec![(3 * Z_section_size + i * num_vars + 3, 1)]);
          constraint_count += 1;
          // Actual cumulative: Z[prev][1] + (tau - Z[i][0] - 1) * valid * Z[prev][1], in slot 1
          (A, B, C) = gen_constr(A, B, C, V_cnst, constraint_count, 
            vec![(3 * Z_section_size + i_last * num_vars + 1, 1), (3 * Z_section_size + i * num_vars + 3, 1)], 
            vec![], 
            vec![(3 * Z_section_size + i * num_vars + 1, 1)]);
          constraint_count += 1;
          i_last = i;
        }
      }

      (A, B, C)
    };

    let perm_block_num_vars = 4 * Z_section_size;
    let perm_block_num_cons = constraint_count;
    let perm_block_num_non_zero_entries = num_vars * constraint_count;

    A_list.push(A);
    B_list.push(B);
    C_list.push(C);

    let perm_block_inst = Instance::new(1, perm_block_num_cons, perm_block_num_vars, &A_list, &B_list, &C_list).unwrap();
    
    (perm_block_num_vars, perm_block_inst, perm_block_num_cons, perm_block_num_non_zero_entries)
  };

  // --
  // End Instances
  // Begin Assignments
  // --

  let (block_vars_matrix, block_inputs_matrix, exec_inputs) = {

    let mut block_vars_matrix = Vec::new();
    let mut block_inputs_matrix = Vec::new();
    let mut exec_inputs = Vec::new();

    // Block 1
    let (assignment_vars, assignment_inputs) = {
      let mut assignment_vars = Vec::new();
      let mut assignment_inputs = Vec::new();
      //                    0    1    2    3    4    5    6    7    8
      // variable orders:  b0   i0   s0   b1   i1   s1   Z0   Z1   B0 
      // input orders:  valid  b_i  i_i  s_i    1  b_o  i_o  s_o
      // Iteration i = 1
      let mut vars = vec![one, zero, zero, one, one, zero, Scalar::from(3u32).neg().invert().to_bytes(), one, one];
      let mut inputs = vec![one, one, zero, zero, one, one, one, zero];
      vars.extend(vec![zero; 7]);
      inputs.extend(vec![zero; 8]);
      let next_block_assignment_vars = VarsAssignment::new(&vars).unwrap();
      let next_block_assignment_inputs = InputsAssignment::new(&inputs).unwrap();
      assignment_vars.push(next_block_assignment_vars);
      assignment_inputs.push(next_block_assignment_inputs.clone());
      exec_inputs.push(next_block_assignment_inputs);
      // Iteration i = 2
      let mut vars = vec![one, one, zero, one, two, one, Scalar::from(2u32).neg().invert().to_bytes(), one, one];
      let mut inputs = vec![one, one, one, zero, one, one, two, one];
      vars.extend(vec![zero; 7]);
      inputs.extend(vec![zero; 8]);
      let next_block_assignment_vars = VarsAssignment::new(&vars).unwrap();
      let next_block_assignment_inputs = InputsAssignment::new(&inputs).unwrap();
      assignment_vars.push(next_block_assignment_vars);
      assignment_inputs.push(next_block_assignment_inputs.clone());
      exec_inputs.push(next_block_assignment_inputs);
      // Iteration i = 3
      let mut vars = vec![one, two, one, one, three, three, Scalar::from(1u32).neg().invert().to_bytes(), one, one];
      let mut inputs = vec![one, one, two, one, one, one, three, three];
      vars.extend(vec![zero; 7]);
      inputs.extend(vec![zero; 8]);
      let next_block_assignment_vars = VarsAssignment::new(&vars).unwrap();
      let next_block_assignment_inputs = InputsAssignment::new(&inputs).unwrap();
      assignment_vars.push(next_block_assignment_vars);
      assignment_inputs.push(next_block_assignment_inputs.clone());
      exec_inputs.push(next_block_assignment_inputs);
      let mut vars = vec![one, three, three, two, four, six, zero, zero, zero];
      let mut inputs = vec![one, one, three, three, one, two, four, six];
      vars.extend(vec![zero; 7]);
      inputs.extend(vec![zero; 8]);
      let next_block_assignment_vars = VarsAssignment::new(&vars).unwrap();
      let next_block_assignment_inputs = InputsAssignment::new(&inputs).unwrap();
      assignment_vars.push(next_block_assignment_vars);
      assignment_inputs.push(next_block_assignment_inputs.clone());
      exec_inputs.push(next_block_assignment_inputs);
      
      (assignment_vars, assignment_inputs)
    };
    block_vars_matrix.push(assignment_vars);
    block_inputs_matrix.push(assignment_inputs);

    // Block 0
    let (assignment_vars, assignment_inputs) = {
      let mut assignment_vars = Vec::new();
      let mut assignment_inputs = Vec::new();
      //                    0    1    2    3    4    5    6    7    8
      // variable orders:  b0   i0   s0   b1   i1   s1   Z0   Z1   B0 
      // input orders:  valid  b_i  i_i  s_i    1  b_o  i_o  s_o
      let mut vars = vec![zero, zero, zero, one, zero, zero, Scalar::from(4u32).neg().invert().to_bytes(), one, one];
      let mut inputs = vec![one, zero, zero, zero, one, one, zero, zero];
      vars.extend(vec![zero; 7]);
      inputs.extend(vec![zero; 8]);
      let next_block_assignment_vars = VarsAssignment::new(&vars).unwrap();
      let next_block_assignment_inputs = InputsAssignment::new(&inputs).unwrap();
      assignment_vars.push(next_block_assignment_vars);
      assignment_inputs.push(next_block_assignment_inputs.clone());
      exec_inputs.insert(0, next_block_assignment_inputs);

      (assignment_vars, assignment_inputs)
    };
    block_vars_matrix.push(assignment_vars);
    block_inputs_matrix.push(assignment_inputs);

    // Pad exec_inputs with 0
    assert!(consis_num_proofs >= exec_inputs.len());
    let pad_size = consis_num_proofs - exec_inputs.len();
    for _ in 0..pad_size {
      exec_inputs.push(VarsAssignment::new(&vec![zero; num_vars]).unwrap());
    }

    // Witnesses for permutation cannot be generated until tau and r are generated
    // Both can only be generated at proving time

    (block_vars_matrix, block_inputs_matrix, exec_inputs)
  };

  // --
  // End Assignments
  // --

  (
    num_vars,
    block_num_cons,
    block_num_non_zero_entries,
    block_num_instances,
    block_max_num_proofs_bound,
    block_num_proofs_bound,
    block_max_num_proofs,
    block_num_proofs,
    block_inst,
    consis_num_cons,
    consis_num_non_zero_entries,
    consis_num_proofs,
    consis_inst,
    perm_prelim_num_cons,
    perm_prelim_num_non_zero_entries,
    perm_prelim_inst,
    perm_block_root_num_cons,
    perm_block_root_num_non_zero_entries,
    perm_block_root_inst,
    block_vars_matrix,
    block_inputs_matrix,
    exec_inputs
  )
}

fn main() {
  // produce an R1CS instance
  let (
    // num_inputs == num_vars
    num_vars,
    block_num_cons,
    block_num_non_zero_entries,
    block_num_instances,
    block_max_num_proofs_bound,
    block_num_proofs_bound,
    block_max_num_proofs,
    block_num_proofs,
    block_inst,
    consis_num_cons,
    consis_num_non_zero_entries,
    consis_num_proofs,
    consis_inst,
    perm_prelim_num_cons,
    perm_prelim_num_non_zero_entries,
    perm_prelim_inst,
    perm_block_root_num_cons,
    perm_block_root_num_non_zero_entries,
    perm_block_root_inst,
    block_vars_matrix,
    block_inputs_matrix,
    exec_inputs
  ) = produce_r1cs();

  assert_eq!(block_num_instances, block_vars_matrix.len());
  assert_eq!(block_num_instances, block_inputs_matrix.len());
  for p in 0..block_num_instances {
    assert_eq!(block_vars_matrix[p].len(), block_inputs_matrix[p].len());
  }

  // produce public parameters
  let block_gens = SNARKGens::new(block_num_cons, num_vars, block_num_instances, block_num_non_zero_entries);
  let consis_gens = SNARKGens::new(consis_num_cons, num_vars, 1, consis_num_non_zero_entries);
  let perm_prelim_gens = SNARKGens::new(perm_prelim_num_cons, num_vars, 1, perm_prelim_num_non_zero_entries);
  let perm_block_root_gens = SNARKGens::new(perm_block_root_num_cons, 4 * num_vars, 1, perm_block_root_num_non_zero_entries);
  // Only use one version of gens_r1cs_sat
  let var_gens = SNARKGens::new(block_num_cons, num_vars, block_num_instances, block_num_non_zero_entries).gens_r1cs_sat;

  // create a commitment to the R1CS instance
  // TODO: change to encoding all r1cs instances
  let (block_comm, block_decomm) = SNARK::encode(&block_inst, &block_gens);
  let (consis_comm, consis_decomm) = SNARK::encode(&consis_inst, &consis_gens);
  let (perm_prelim_comm, perm_prelim_decomm) = SNARK::encode(&perm_prelim_inst, &perm_prelim_gens);
  let (perm_block_root_comm, perm_block_root_decomm) = SNARK::encode(&perm_block_root_inst, &perm_block_root_gens);

  // produce a proof of satisfiability
  let mut prover_transcript = Transcript::new(b"snark_example");
  let proof = SNARK::prove(
    num_vars,
    block_num_instances,
    block_max_num_proofs_bound,
    &block_num_proofs_bound,
    block_max_num_proofs,
    &block_num_proofs,
    &block_inst,
    &block_comm,
    &block_decomm,
    &block_gens,
    consis_num_proofs,
    &consis_inst,
    &consis_comm,
    &consis_decomm,
    &consis_gens,
    &perm_prelim_inst,
    &perm_prelim_comm,
    &perm_prelim_decomm,
    &perm_prelim_gens,
    &perm_block_root_inst,
    &perm_block_root_comm,
    &perm_block_root_decomm,
    &perm_block_root_gens,
    block_vars_matrix,
    block_inputs_matrix,
    exec_inputs,
    &var_gens,
    &mut prover_transcript,
  );

  // verify the proof of satisfiability
  let mut verifier_transcript = Transcript::new(b"snark_example");
  assert!(proof
    .verify(
      num_vars,
      block_num_instances, 
      block_max_num_proofs, 
      &block_num_proofs, 
      block_num_cons, 
      &block_comm,
      &block_gens,
      consis_num_proofs, 
      consis_num_cons, 
      &consis_comm,
      &consis_gens,
      perm_prelim_num_cons,
      &perm_prelim_comm,
      &perm_prelim_gens,
      perm_block_root_num_cons,
      &perm_block_root_comm,
      &perm_block_root_gens,
      &var_gens,
      &mut verifier_transcript)
    .is_ok());
  println!("proof verification successful!");
}
