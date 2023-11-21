//! An simple program with some memory operations
//! The pseudocode is:
//!   a[0] = 1
//!   a[1] = 2
//!   s = 0
//!   i = 0
//!   while i != 3:
//!     i = i + a[0]
//!     s = s + a[1]
//! Which, when converted to blocks, is:
//! Block 0:                        Block 1:
//!   assert v * v = v                assert v * v = v
//!   if (v == 1) {                   if (v == 1) {
//!     assert b == 0                   assert b == 1
//!     STORE(0, 1)                     LOAD(0, M0)
//!     STORE(1, 2)                     LOAD(1, M1)
//!     s = 0                           i = i + M0
//!     i = 1                           s = s + M1
//!     if i != 3:                      if i != 3:
//!       b = 1                           b = 1
//!     else:                           else:
//!       b = 2                           b = 2
//!   }                               }
//! Note: take caution when translating STORE(0, 1) into constraints. If an execution of the block is invalid, this could cause a problem!
//! 
//! Converting each block to constraints:
//! Block 0:                        Block 1:
//!   v = v * v                       v = v * v
//!   0 = b0                          0 = v * (b0 - 1)
//!   0 = i0                          0 = v * (i1 - i0 - M0)
//!   0 = s0                          0 = v * (s1 - s0 - M1)
//!   Z1 = (i0 - 3) * Z0              Z1 = (i1 - 3) * Z0
//!   T0 = v * B0                     T0 = v * B0
//!   0 = T0 * (Z1 - 1)               0 = T0 * (Z1 - 1)
//!   0 = T0 * (b1 - 1)               0 = T0 * (b1 - 1)
//!   T1 = v * (1 - B0)               T1 = v * (1 - B0)
//!   0 = T1 * (i0 - 3)               0 = T1 * (i1 - 3)
//!   0 = T1 * (b1 - 2)               0 = T1 * (b1 - 2)
//!   i1 = i0
//!   s1 = s0
//! 
//! Program States
//!        0    1   2   3   4    5   6   7    0   1   2   3   4   5   6   7
//! Exec:  v | b0  i0  s0 | _ | b1  i1  s1 | Z0  Z1  B0  T0  T1  M0  M1   _
//! 0      1    0   0   0   0    1   0   0  -3i   1   1   1   0   0   0   0
//! 1      1    1   0   0   0    1   1   2  -2i   1   1   1   0   1   2   0
//! 2      1    1   1   2   0    1   2   4  -1i   1   1   1   0   1   2   0
//! 3      1    1   2   4   0    2   3   6    0   0   0   0   1   1   2   0
//! 4      0    0   0   0   0    0   0   0    0   0   0   0   0   0   0   0 
//!
#![allow(clippy::assertions_on_result_states)]
use std::ops::Neg;

use curve25519_dalek::scalar::Scalar;
use libspartan::{Instance, SNARKGens, VarsAssignment, SNARK, InputsAssignment, MemsAssignment};
use merlin::Transcript;

#[allow(non_snake_case)]
fn produce_r1cs() -> (
  usize,
  usize,
  Vec<[u8; 32]>,
  Vec<[u8; 32]>,
  usize,

  usize,
  usize,
  usize,
  usize,
  usize,
  usize,
  usize,
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
  usize,
  usize,
  Instance,
  usize,
  usize,
  Instance,
  Vec<usize>,
  usize,
  usize,
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
  Vec<InputsAssignment>,
  Vec<Vec<MemsAssignment>>,
  Vec<MemsAssignment>,
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
    let minus_three = Scalar::from(3u32).neg().to_bytes();
    let int_to_scalar = |i| {
      match i {
        0  => zero,
        1  => one,
        2  => two,
        -1 => minus_one,
        -2 => minus_two,
        -3 => minus_three,
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
  // COMPILE TIME KNOWLEDGE
  // --
  
  // num_vars should be consistent accross the instances
  // everything else is instance-specific
  // Divide inputs into (1, input, 1, output)
  // So num_inputs = num_outputs = input_output_cutoff - 1
  let num_vars = 8;
  let input_output_cutoff = 4;

  // Number of proofs of each R1CS instance
  // Total for all blocks and one block
  // OBTAINED DURING COMPILE TIME
  let total_num_proofs_bound = 16;
  // Bound on total number of memory accesses
  let total_num_mem_accesses_bound = 16;

  // What is the input and output block?
  // Note: the assumption is that during a normal execution, the input block and the output block will only be reached once
  let input_block_num = 0;
  let output_block_num = 2;

  // --
  // BLOCK Instances
  // --

  // parameters of the BLOCK instance
  // maximum value among the R1CS instances
  let block_num_cons = 16;
  let block_num_non_zero_entries = 21;
  // Number of R1CS instances
  let block_num_instances = 2;

  // Program States
  //        0    1   2   3   4    5   6   7    0   1   2   3   4   5   6   7
  // Exec:  v | b0  i0  s0 | _ | b1  i1  s1 | Z0  Z1  B0  T0  T1  M0  M1   _
  let V_valid = num_vars;
  let V_cnst = V_valid;
  let V_b0 = num_vars + 1;
  let V_i0 = num_vars + 2;
  let V_s0 = num_vars + 3;
  let V_b1 = num_vars + 5;
  let V_i1 = num_vars + 6;
  let V_s1 = num_vars + 7;
  let V_Z0 = 0;
  let V_Z1 = 1;
  let V_B0 = 2;
  let V_T0 = 3;
  let V_T1 = 4;
  let V_M0 = 5;
  let V_M1 = 6;

  let block_inst = {
    let mut A_list = Vec::new();
    let mut B_list = Vec::new();
    let mut C_list = Vec::new();

    // Instance 0: block 1
    // Instances need to be sorted form highest # of execution -> lowest
    let (A, B, C) = {
      let mut A: Vec<(usize, usize, [u8; 32])> = Vec::new();
      let mut B: Vec<(usize, usize, [u8; 32])> = Vec::new();
      let mut C: Vec<(usize, usize, [u8; 32])> = Vec::new();

      let mut i = 0;
      // v * v = v
      (A, B, C) = gen_constr(A, B, C, V_cnst,
        i, vec![(V_valid, 1)], vec![(V_valid, 1)], vec![(V_valid, 1)]);
      i += 1;
      // v * (b0 - 1) = 0
      (A, B, C) = gen_constr(A, B, C, V_cnst,
        i, vec![(V_valid, 1)], vec![(V_b0, 1), (V_cnst, -1)], vec![]);
      i += 1;
      // v * (i1 - i0 - M0) = 0
      (A, B, C) = gen_constr(A, B, C, V_cnst,
        i, vec![(V_valid, 1)], vec![(V_i1, 1), (V_i0, -1), (V_M0, -1)], vec![]);
      i += 1;
      // v * (s1 - s0 - M1) = 0
      (A, B, C) = gen_constr(A, B, C, V_cnst,
        i, vec![(V_valid, 1)], vec![(V_s1, 1), (V_s0, -1), (V_M1, -1)], vec![]);
      i += 1;
      // (i1 - 3) * Z0 = Z1
      (A, B, C) = gen_constr(A, B, C, V_cnst,
        i, vec![(V_i1, 1), (V_cnst, -3)], vec![(V_Z0, 1)], vec![(V_Z1, 1)]);
      i += 1;
      // v * B0 = T0
      (A, B, C) = gen_constr(A, B, C, V_cnst,
        i, vec![(V_valid, 1)], vec![(V_B0, 1)], vec![(V_T0, 1)]);
      i += 1;
      // T0 * (Z1 - 1) = 0
      (A, B, C) = gen_constr(A, B, C, V_cnst,
        i, vec![(V_T0, 1)], vec![(V_Z1, 1), (V_cnst, -1)], vec![]);
      i += 1;
      // T0 * (b1 - 1) = 0
      (A, B, C) = gen_constr(A, B, C, V_cnst,
        i, vec![(V_T0, 1)], vec![(V_b1, 1), (V_cnst, -1)], vec![]);
      i += 1;
      // v * (1 - B0) = T1
      (A, B, C) = gen_constr(A, B, C, V_cnst,
        i, vec![(V_valid, 1)], vec![(V_cnst, 1), (V_B0, -1)], vec![(V_T1, 1)]);
      i += 1;
      // T1 * (i1 - 3) = 0
      (A, B, C) = gen_constr(A, B, C, V_cnst,
        i, vec![(V_T1, 1)], vec![(V_i1, 1), (V_cnst, -3)], vec![]);
      i += 1;
      // T1 * (b1 - 2) = 0
      (A, B, C) = gen_constr(A, B, C, V_cnst,
        i, vec![(V_T1, 1)], vec![(V_b1, 1), (V_cnst, -2)], vec![]);

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

      let mut i = 0;
      // v * v = v
      (A, B, C) = gen_constr(A, B, C, V_cnst,
        i, vec![(V_valid, 1)], vec![(V_valid, 1)], vec![(V_valid, 1)]);
      i += 1;
      // b0 = 0
      (A, B, C) = gen_constr(A, B, C, V_cnst,
        i, vec![(V_b0, 1)], vec![], vec![]);
      i += 1;
      // i0 = 0
      (A, B, C) = gen_constr(A, B, C, V_cnst,
        i, vec![(V_i0, 1)], vec![], vec![]);
      i += 1;
      // s0 = 0
      (A, B, C) = gen_constr(A, B, C, V_cnst,
        i, vec![(V_s0, 1)], vec![], vec![]);
      i += 1;
      // (i0 - 3) * Z0 = Z1
      (A, B, C) = gen_constr(A, B, C, V_cnst,
        i, vec![(V_i0, 1), (V_cnst, -3)], vec![(V_Z0, 1)], vec![(V_Z1, 1)]);
      i += 1;
      // v * B0 = T0
      (A, B, C) = gen_constr(A, B, C, V_cnst,
        i, vec![(V_valid, 1)], vec![(V_B0, 1)], vec![(V_T0, 1)]);
      i += 1;
      // T0 * (Z1 - 1) = 0
      (A, B, C) = gen_constr(A, B, C, V_cnst,
        i, vec![(V_T0, 1)], vec![(V_Z1, 1), (V_cnst, -1)], vec![]);
      i += 1;
      // T0 * (b1 - 1) = 0
      (A, B, C) = gen_constr(A, B, C, V_cnst,
        i, vec![(V_T0, 1)], vec![(V_b1, 1), (V_cnst, -1)], vec![]);
      i += 1;
      // v * (1 - B0) = T1
      (A, B, C) = gen_constr(A, B, C, V_cnst,
        i, vec![(V_valid, 1)], vec![(V_cnst, 1), (V_B0, -1)], vec![(V_T1, 1)]);
      i += 1;
      // T1 * (i0 - 3) = 0
      (A, B, C) = gen_constr(A, B, C, V_cnst,
        i, vec![(V_T1, 1)], vec![(V_i0, 1), (V_cnst, -3)], vec![]);
      i += 1;
      // T1 * (b1 - 2) = 0
      (A, B, C) = gen_constr(A, B, C, V_cnst,
        i, vec![(V_T1, 1)], vec![(V_b1, 1), (V_cnst, -2)], vec![]);

      (A, B, C)
    };
    A_list.push(A);
    B_list.push(B);
    C_list.push(C);

    let block_inst = Instance::new(block_num_instances, block_num_cons, 2 * num_vars, &A_list, &B_list, &C_list).unwrap();
    
    block_inst
  };

  // --
  // CONSIS INSTANCES
  // --
  // CONSIS is consisted of two instances
  // CONSIS_COMB performs random linear combination on inputs and outputs to a single value
  // It is parallelized for consis_num_proofs copies
  // CONSIS_CHECK checks that these values indeed matches
  // There is only one copy for CONSIS_CHECK

  // CONSIS_COMB
  // CONSIS_COMB takes in 4 witness lists as inputs:
  // - perm_w0: <tau, r, r^2, r^3, ...>, see PERM_PRELIM below
  // - exec_inputs: <v, i0, i1, i2, ..., cnst, o0, o1, o2, ...>
  // - consis_w2: <0, i0 * r, i1 * r^2, ..., 0, o0 * r, o1 * r^2, ...>
  // - consis_w3: <v, v * (cnst + i0 * r + i1 * r^2 + i2 * r^3 + ...), v * (cnst + o0 * r + o1 * r^2 + o2 * r^3 + ...), 0, 0, ...>
  // Note: if v is 1, it is almost impossible to have consis_w3[1] = 0
  let consis_comb_num_cons = 2 * input_output_cutoff + 1;
  let consis_comb_num_non_zero_entries = 4 * input_output_cutoff - 1;

  let V_valid = num_vars;
  let V_cnst = V_valid;

  let consis_comb_inst = {
    let mut A_list = Vec::new();
    let mut B_list = Vec::new();
    let mut C_list = Vec::new();
    
    let (A, B, C) = {
      let mut A: Vec<(usize, usize, [u8; 32])> = Vec::new();
      let mut B: Vec<(usize, usize, [u8; 32])> = Vec::new();
      let mut C: Vec<(usize, usize, [u8; 32])> = Vec::new();

      let mut constraint_count = 0;

      // R1CS:
      // For w2
      for i in 1..input_output_cutoff {
        // Dot product for inputs
        (A, B, C) = gen_constr(A, B, C, V_cnst,
          constraint_count, vec![(i, 1)], vec![(num_vars + i, 1)], vec![(2 * num_vars + i, 1)]);
        constraint_count += 1;
        // Dot product for outputs
        (A, B, C) = gen_constr(A, B, C, V_cnst,
          constraint_count, vec![(i, 1)], vec![(num_vars + input_output_cutoff + i, 1)], vec![(2 * num_vars + input_output_cutoff + i, 1)]);
        constraint_count += 1;
      }
      // For w3
      (A, B, C) = gen_constr(A, B, C, V_cnst, // w3[0]
        constraint_count, vec![(V_valid, 1)], vec![], vec![(3 * num_vars, 1)]);
      constraint_count += 1;
      (A, B, C) = gen_constr(A, B, C, V_cnst, // w3[1]
        constraint_count, 
        vec![(V_valid, 1)], 
        [vec![(V_cnst, 1)], (1..input_output_cutoff).map(|i| (2 * num_vars + i, 1)).collect()].concat(),
        vec![(3 * num_vars + 1, 1)]
      );
      constraint_count += 1;
      (A, B, C) = gen_constr(A, B, C, V_cnst, // w3[2]
        constraint_count, 
        vec![(V_valid, 1)], 
        [vec![(V_cnst, 1)], (1..input_output_cutoff).map(|i| (2 * num_vars + input_output_cutoff + i, 1)).collect()].concat(),
        vec![(3 * num_vars + 2, 1)]
      );

      (A, B, C)
    };
    A_list.push(A);
    B_list.push(B);
    C_list.push(C);

    let consis_comb_inst = Instance::new(1, consis_comb_num_cons, 4 * num_vars, &A_list, &B_list, &C_list).unwrap();
    
    consis_comb_inst
  };

  // CONSIS_CHECK
  // CONSIS_CHECK takes in consis_w3 = <v, i, o, 0, 0, ...>
  // and verifies (o[k] - i[k + 1]) * v[k + 1] = 0 for all k
  let consis_check_num_cons_base = 1;
  let consis_check_num_non_zero_entries = 2 * total_num_proofs_bound;
  let consis_check_num_cons = consis_check_num_cons_base * total_num_proofs_bound;

  let V_valid = 0;
  let V_i = 1;
  let V_o = 2;
  let consis_check_inst = {
    let mut A_list = Vec::new();
    let mut B_list = Vec::new();
    let mut C_list = Vec::new();
    
    // Check output of the last block is the input of the next block
    let (A, B, C) = {
      let mut A: Vec<(usize, usize, [u8; 32])> = Vec::new();
      let mut B: Vec<(usize, usize, [u8; 32])> = Vec::new();
      let mut C: Vec<(usize, usize, [u8; 32])> = Vec::new();

      // R1CS:
      for i in 0..total_num_proofs_bound - 1 {
        // Output matches input
        (A, B, C) = gen_constr(A, B, C, 0,
          i, vec![(i * num_vars + V_o, 1), ((i + 1) * num_vars + V_i, -1)], vec![((i + 1) * num_vars + V_valid, 1)], vec![]);
      }
      (A, B, C)
    };
    A_list.push(A);
    B_list.push(B);
    C_list.push(C);

    let consis_check_inst = Instance::new(1, consis_check_num_cons, total_num_proofs_bound * num_vars, &A_list, &B_list, &C_list).unwrap();
    
    consis_check_inst
  };

  // --
  // PERM Instances
  // --
  // PERM is consisted of four instances
  // PERM_PRELIM checks the correctness of (r, r^2, ...)
  // PERM_ROOT and PERM_BLOCK_POLY compute the polynomial defined by block_inputs
  // PERM_ROOT and PERM_EXEC_POLY compute the polynomial defined by exec_inputs
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

  // PERM_ROOT
  let perm_root_num_cons = num_vars + 2;
  let perm_root_num_non_zero_entries = 2 * num_vars + 2;
  let perm_root_inst = {
    let (A, B, C) = {
      let mut A: Vec<(usize, usize, [u8; 32])> = Vec::new();
      let mut B: Vec<(usize, usize, [u8; 32])> = Vec::new();
      let mut C: Vec<(usize, usize, [u8; 32])> = Vec::new();

      // Witnesses of PERM_ROOT is consisted of [w0, w1, w2, w3], each of size num_vars
      // w0: tau, r, r^2, ...
      // w1: one block_inputs entry: i0, i1, ...
      // w2: one block_inputs entry dot product <r>: i0, i1 * r, i2 * r^2, i3 * r^3, ...
      // w3[0]: valid bit, should match block_inputs[0]
      // w3[1]: one root of the polynomial: (tau - (i0 + i1 * r + i2 * r^2 - ...)), 0 if invalid
      let V_tau = 0;
      // The best way to find a CONSTANT ONE is to peak into the constant term of the first input, which is guaranteed to be valid
      let V_cnst = num_vars;

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
          vec![(num_vars, 1)], 
          vec![(3 * num_vars + 1, 1)]);

      (A, B, C)   
    };

    let A_list = vec![A.clone()];
    let B_list = vec![B.clone()];
    let C_list = vec![C.clone()];

    let perm_root_inst = Instance::new(1, perm_root_num_cons, 4 * num_vars, &A_list, &B_list, &C_list).unwrap();
    
    perm_root_inst
  };

  // PERM_POLY (for PERM_BLOCK_POLY, PERM_EXEC_POLY, MEM_BLOCK_POLY), MEM_ADDR_POLY
  // The strategy is to compute the local polynomials (evaluated on tau) for each block instance
  // Each w3[p][2] (i.e. w3[p][0][2]) stores the product pi for instance P. The verifier obtains all P of them and multiply them together.
  // The correct formular is pi = v[k] * x[k] * (pi[k+1] + (1 - v[k+1])))
  // To do this, think of each entry of w3[k] (w3[p][k]) as a tuple (v, x, pi, D)
  // v[k]  <- whether the entry is valid
  // x[k]  <- \tau - (\sum_i a_i * r^{i-1})
  // pi[k] <- v[k] * D[k]
  // D[k] <- x[k] * (pi[k + 1] + (1 - v[k + 1]))
  // number of variables is total_num_proofs_bound * num_vars
  let perm_poly_num_cons_base = 2;
  let perm_size_bound = total_num_proofs_bound;
  let perm_poly_num_cons = perm_size_bound * perm_poly_num_cons_base;
  let perm_poly_num_non_zero_entries = perm_size_bound * 4;
  
  let perm_poly_inst = {
    let (A, B, C) = {
      let mut A: Vec<(usize, usize, [u8; 32])> = Vec::new();
      let mut B: Vec<(usize, usize, [u8; 32])> = Vec::new();
      let mut C: Vec<(usize, usize, [u8; 32])> = Vec::new();

      let V_valid = 0;
      let V_cnst = V_valid;
      let V_x = 1;
      let V_pi = 2;
      let V_d = 3;

      let mut constraint_count = 0;

      // Need to order the constraints so that they solve the inputs in the front first
      // This way Az, Bz, Cz will have all non-zero entries concentrated in the front
      for i in 0..perm_size_bound - 1 {
        // D[k] = x[k] * (pi[k + 1] + (1 - v[k + 1]))
        (A, B, C) = gen_constr(A, B, C, i * num_vars + V_cnst,
          constraint_count, 
          vec![(i * num_vars + V_x, 1)], 
          vec![((i + 1) * num_vars + V_pi, 1), (i * num_vars + V_cnst, 1), ((i + 1) * num_vars + V_valid, -1)], 
          vec![(i * num_vars + V_d, 1)]);
        constraint_count += 1;
        // pi[k] = v[k] * D[k]
        (A, B, C) = gen_constr(A, B, C, i * num_vars + V_cnst,
          constraint_count, vec![(i * num_vars + V_valid, 1)], vec![(i * num_vars + V_d, 1)], vec![(i * num_vars + V_pi, 1)]);
        // Pad base constraint size to 2
        constraint_count += 1;
      }
      // Last Entry
      let i = perm_size_bound - 1;
      // last D is x[k] * 1
      (A, B, C) = gen_constr(A, B, C, i * num_vars + V_cnst,
        constraint_count, vec![(i * num_vars + V_x, 1)], vec![], vec![(i * num_vars + V_d, 1)]);
      constraint_count += 1;
      // last pi is just usual
      (A, B, C) = gen_constr(A, B, C, i * num_vars + V_cnst,
        constraint_count, vec![(i * num_vars + V_valid, 1)], vec![(i * num_vars + V_d, 1)], vec![(i * num_vars + V_pi, 1)]);

      (A, B, C)   
    };

    let A_list = vec![A.clone()];
    let B_list = vec![B.clone()];
    let C_list = vec![C.clone()];

    let perm_poly_inst = Instance::new(1, perm_poly_num_cons, perm_size_bound * num_vars, &A_list, &B_list, &C_list).unwrap();
    
    perm_poly_inst
  };

  // --
  // MEM Instances
  // --

  // MEM_EXTRACT
  // How many memory accesses are in each block?
  let block_num_mem_accesses = vec![2, 2];
  // parameters of the MEM_EXTRACT instance
  // maximum value among the R1CS instances
  let mem_extract_num_cons = 8;
  let mem_extract_num_non_zero_entries = 9;

  // !!!NOTE: we assume that there are fewer memory accesses than witnesses, need to double check whether that is true!!!

  let mem_extract_inst = {
    let mut A_list = Vec::new();
    let mut B_list = Vec::new();
    let mut C_list = Vec::new();

    // MR is r * val for each (addr, val)
    // MC is the cumulative product of v * (tau - addr - MR)
    // The final product is stored in x
    // 0   1   2   3   4   5   6   7    0   1   2   3     4   5   6   7
    // tau r   _   _   _   _   _   _ |  v   x  pi   D  | MR  MC  MR  MC |
    // 0   1   2   3   4   5   6   7    0    1   2   3   4    5   6   7
    // Z0  Z1  B0  T0  T1  M0  M1   _ | v | b0  i0  s0 | _ | b1  i1  s1 |
    // The prover still needs (addr, val) in block order to evaluate MR and MC
    let V_tau = 0;
    let V_r = 1;
    let V_v = num_vars;
    let V_x = num_vars + 1;
    let V_MR = |i: usize| num_vars + 4 + 2 * i;
    let V_MC = |i: usize| num_vars + 5 + 2 * i;
    let V_M0 = 2 * num_vars + 5;
    let V_M1 = 2 * num_vars + 6;
    let V_valid = 3 * num_vars;
    let V_cnst = V_valid;

    // Instance 0: block 1
    // Instances need to be sorted form highest # of execution -> lowest
    let (A, B, C) = {
      let mut A: Vec<(usize, usize, [u8; 32])> = Vec::new();
      let mut B: Vec<(usize, usize, [u8; 32])> = Vec::new();
      let mut C: Vec<(usize, usize, [u8; 32])> = Vec::new();

      let mut i = 0;
      // addr = 0, val = M0
      (A, B, C) = gen_constr(A, B, C, V_cnst,
        i, vec![(V_r, 1)], vec![(V_M0, 1)], vec![(V_MR(0), 1)]);
      i += 1;
      (A, B, C) = gen_constr(A, B, C, V_cnst,
        i, vec![(V_valid, 1)], vec![(V_tau, 1), (V_MR(0), -1)], vec![(V_MC(0), 1)]);
      i += 1;
      // addr = 1, val = M1
      (A, B, C) = gen_constr(A, B, C, V_cnst,
        i, vec![(V_r, 1)], vec![(V_M1, 1)], vec![(V_MR(1), 1)]);
      i += 1;
      (A, B, C) = gen_constr(A, B, C, V_cnst,
        i, vec![(V_MC(0), 1)], vec![(V_tau, 1), (V_cnst, -1), (V_MR(1), -1)], vec![(V_MC(1), 1)]);
      i += 1;
      // w3[0]
      (A, B, C) = gen_constr(A, B, C, V_cnst,
        i, vec![(V_valid, 1)], vec![], vec![(V_v, 1)]);
      i += 1;
      // w3[1]
      (A, B, C) = gen_constr(A, B, C, V_cnst,
        i, vec![(V_x, 1)], vec![], vec![(V_MC(1), 1)]); 

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

      let mut i = 0;
      // addr = 0, val = 1
      (A, B, C) = gen_constr(A, B, C, V_cnst,
        i, vec![(V_r, 1)], vec![(V_cnst, 1)], vec![(V_MR(0), 1)]);
      i += 1;
      (A, B, C) = gen_constr(A, B, C, V_cnst,
        i, vec![(V_valid, 1)], vec![(V_tau, 1), (V_MR(0), -1)], vec![(V_MC(0), 1)]);
      i += 1;
      // addr = 1, val = 2
      (A, B, C) = gen_constr(A, B, C, V_cnst,
        i, vec![(V_r, 1)], vec![(V_cnst, 2)], vec![(V_MR(1), 1)]);
      i += 1;
      (A, B, C) = gen_constr(A, B, C, V_cnst,
        i, vec![(V_MC(0), 1)], vec![(V_tau, 1), (V_cnst, -1), (V_MR(1), -1)], vec![(V_MC(1), 1)]);
      i += 1;
      // w3[0]
      (A, B, C) = gen_constr(A, B, C, V_cnst,
        i, vec![(V_valid, 1)], vec![], vec![(V_v, 1)]);
      i += 1;
      // w3[1]
      (A, B, C) = gen_constr(A, B, C, V_cnst,
        i, vec![(V_x, 1)], vec![], vec![(V_MC(1), 1)]); 

      (A, B, C)
    };
    A_list.push(A);
    B_list.push(B);
    C_list.push(C);

    let mem_extract_inst = Instance::new(block_num_instances, mem_extract_num_cons, 4 * num_vars, &A_list, &B_list, &C_list).unwrap();
    
    mem_extract_inst
  };

  // MEM_COHERE
  // MEM_CONHERE takes in addr_mem = <v, addr, val, D>
  // and verifies that
  // 1. (v[k] - 1) * v[k + 1] = 0: if the current entry is invalid, the next entry is also invalid
  // 2. v[k + 1] * (addr[k + 1] - addr[k] - 1) * (addr[k + 1] - addr[k]) = 0: address difference is 0 or 1, unless the next entry is invalid
  // 3. v[k + 1] * (addr[k + 1] - addr[k] - 1) * (val[k + 1] - val[k]) = 0: either address difference is 1, or value are the same, unless the next entry is invalid
  // So we set D = v[k + 1] * (addr[k + 1] - addr[k] - 1)
  let mem_cohere_num_cons_base = 4;
  let mem_cohere_num_non_zero_entries = 8 * total_num_mem_accesses_bound;
  let mem_cohere_num_cons = mem_cohere_num_cons_base * total_num_mem_accesses_bound;

  let mem_cohere_inst = {
    let V_valid = 0;
    let V_cnst = V_valid;
    let V_addr = 1;
    let V_val = 2;
    let V_D = 3;
    let width = 4;

    let mut A_list = Vec::new();
    let mut B_list = Vec::new();
    let mut C_list = Vec::new();
    
    let (A, B, C) = {
      let mut A: Vec<(usize, usize, [u8; 32])> = Vec::new();
      let mut B: Vec<(usize, usize, [u8; 32])> = Vec::new();
      let mut C: Vec<(usize, usize, [u8; 32])> = Vec::new();

      let mut num_cons = 0;
      for i in 0..total_num_mem_accesses_bound - 1 {
        // (v[k] - 1) * v[k + 1] = 0
        (A, B, C) = gen_constr(A, B, C, V_cnst,
          num_cons, vec![(i * width + V_valid, 1), (V_cnst, -1)], vec![((i + 1) * width + V_valid, 1)], vec![]);
        num_cons += 1;
        // v[k + 1] * (addr[k + 1] - addr[k] - 1) = D[k]
        (A, B, C) = gen_constr(A, B, C, V_cnst,
          num_cons, vec![((i + 1) * width + V_valid, 1)], vec![((i + 1) * width + V_addr, 1), (i * width + V_addr, -1), (V_cnst, -1)], vec![(V_D, 1)]);
        num_cons += 1;
        // D[k] * (addr[k + 1] - addr[k]) = 0
        (A, B, C) = gen_constr(A, B, C, V_cnst,
          num_cons, vec![(i * width + V_D, 1)], vec![((i + 1) * width + V_addr, 1), (i * width + V_addr, -1)], vec![]);
        num_cons += 1;
        // D[k] * (val[k + 1] - val[k]) = 0
        (A, B, C) = gen_constr(A, B, C, V_cnst,
          num_cons, vec![(i * width + V_D, 1)], vec![((i + 1) * width + V_val, 1), (i * width + V_val, -1)], vec![]);
        num_cons += 1;
      }
      (A, B, C)
    };
    A_list.push(A);
    B_list.push(B);
    C_list.push(C);

    let mem_cohere_inst = Instance::new(1, mem_cohere_num_cons, total_num_mem_accesses_bound * width, &A_list, &B_list, &C_list).unwrap();
    
    mem_cohere_inst
  };

  // MEM_BLOCK_POLY is PERM_BLOCK_POLY

  // MEM_ADDR_COMB converts (v, addr, val, _) to (v, x, pi, D)
  let mem_addr_comb_num_cons = 3;
  let mem_addr_comb_num_non_zero_entries = 5;
  
  let mem_addr_comb_inst = {
    let mut A_list = Vec::new();
    let mut B_list = Vec::new();
    let mut C_list = Vec::new();

    // Input width is 4!
    let width = 4;
    // 0   1   2   3 | 0   1   2   3 | 0   1   2   3 | 0   1   2   3
    // tau r   _   _ | v   x  pi   D | v addr val  _ | MR  _   _   _
    let V_tau = 0;
    let V_r = 1;
    let V_v = width;
    let V_x = width + 1;
    let V_valid = 2 * width;
    let V_addr = 2 * width + 1;
    let V_val = 2 * width + 2;
    let V_MR = 3 * width;

    let (A, B, C) = {
      let mut A: Vec<(usize, usize, [u8; 32])> = Vec::new();
      let mut B: Vec<(usize, usize, [u8; 32])> = Vec::new();
      let mut C: Vec<(usize, usize, [u8; 32])> = Vec::new();

      // MR = r * val
      (A, B, C) = gen_constr(A, B, C, V_cnst,
        0, vec![(V_r, 1)], vec![(V_val, 1)], vec![(V_MR, 1)]);
      // w1[0] = v
      (A, B, C) = gen_constr(A, B, C, V_cnst,
        1, vec![(V_v, 1)], vec![], vec![(V_valid, 1)]);
      // w1[1] = x = v * (tau - addr - MR)
      (A, B, C) = gen_constr(A, B, C, V_cnst,
        2, vec![(V_v, 1)], vec![(V_tau, 1), (V_addr, -1), (V_MR, -1)], vec![(V_x, 1)]);
      (A, B, C)
    };

    A_list.push(A);
    B_list.push(B);
    C_list.push(C);

    let mem_addr_comb_inst = Instance::new(1, mem_addr_comb_num_cons, 4 * width, &A_list, &B_list, &C_list).unwrap();
    mem_addr_comb_inst
  };

  // MEM_ADDR_POLY is like PERM_POLY except number of variables is total_num_mem_accesses_bound and gap is 4
  let mem_addr_poly_num_cons_base = 2;
  let mem_addr_poly_num_cons = total_num_mem_accesses_bound * perm_poly_num_cons_base;
  let mem_addr_poly_num_non_zero_entries = total_num_mem_accesses_bound * 4;
  
  let mem_addr_poly_inst = {
    let width = 4;

    let (A, B, C) = {
      let mut A: Vec<(usize, usize, [u8; 32])> = Vec::new();
      let mut B: Vec<(usize, usize, [u8; 32])> = Vec::new();
      let mut C: Vec<(usize, usize, [u8; 32])> = Vec::new();

      let V_valid = 0;
      let V_cnst = V_valid;
      let V_x = 1;
      let V_pi = 2;
      let V_d = 3;

      let mut constraint_count = 0;

      // Need to order the constraints so that they solve the inputs in the front first
      // This way Az, Bz, Cz will have all non-zero entries concentrated in the front
      for i in 0..total_num_mem_accesses_bound - 1 {
        // D[k] = x[k] * (pi[k + 1] + (1 - v[k + 1]))
        (A, B, C) = gen_constr(A, B, C, i * width + V_cnst,
          constraint_count, 
          vec![(i * width + V_x, 1)], 
          vec![((i + 1) * width + V_pi, 1), (i * width + V_cnst, 1), ((i + 1) * width + V_valid, -1)], 
          vec![(i * width + V_d, 1)]);
        constraint_count += 1;
        // pi[k] = v[k] * D[k]
        (A, B, C) = gen_constr(A, B, C, i * width + V_cnst,
          constraint_count, vec![(i * width + V_valid, 1)], vec![(i * width + V_d, 1)], vec![(i * width + V_pi, 1)]);
        // Pad base constraint size to 2
        constraint_count += 1;
      }
      // Last Entry
      let i = total_num_mem_accesses_bound - 1;
      // last D is x[k] * 1
      (A, B, C) = gen_constr(A, B, C, i * width + V_cnst,
        constraint_count, vec![(i * width + V_x, 1)], vec![], vec![(i * width + V_d, 1)]);
      constraint_count += 1;
      // last pi is just usual
      (A, B, C) = gen_constr(A, B, C, i * width + V_cnst,
        constraint_count, vec![(i * width + V_valid, 1)], vec![(i * width + V_d, 1)], vec![(i * width + V_pi, 1)]);

      (A, B, C)   
    };

    let A_list = vec![A.clone()];
    let B_list = vec![B.clone()];
    let C_list = vec![C.clone()];

    let mem_addr_poly_inst = Instance::new(1, mem_addr_poly_num_cons, total_num_mem_accesses_bound * width, &A_list, &B_list, &C_list).unwrap();
    
    mem_addr_poly_inst
  };

  // --
  // End Instances
  // --

  // --
  // RUNTIME KNOWLEDGE
  // --
  let block_max_num_proofs = 4;
  let block_num_proofs = vec![4, 1];
  let consis_num_proofs: usize = 8;
  // What is the input and the output?
  let input = vec![zero, zero];
  let output = vec![three, six];
  // Which block in the execution order is the output block?
  let output_block_index = 3;
  // How many memory executions are there?
  let total_num_mem_accesses = 8;

  // --
  // Begin Assignments
  // --

  let (
    block_vars_matrix, 
    block_inputs_matrix, 
    exec_inputs,
    block_mems_matrix,
    addr_mems_list
  ) = {

    let mut block_vars_matrix = Vec::new();
    let mut block_inputs_matrix = Vec::new();
    let mut exec_inputs = Vec::new();
    // Mems matrix is of the form (0, 0, 0, 0, addr, val, addr, val, ...)
    // Skip the first four entries
    let mut block_mems_matrix = Vec::new();
    let mut addr_mems_list = Vec::new();

    // Block 1
    //        0    1   2   3   4    5   6   7    0   1   2   3   4   5   6   7
    // Exec:  v | b0  i0  s0 | _ | b1  i1  s1 | Z0  Z1  B0  T0  T1  M0  M1   _
    // 0      1    1   0   0   0    1   1   2  -2i   1   1   1   0   1   2   0
    // 1      1    1   1   2   0    1   2   4  -1i   1   1   1   0   1   2   0
    // 2      1    1   2   4   0    2   3   6    0   0   0   0   1   1   2   0
    // 3      0    0   0   0   0    0   0   0    0   0   0   0   0   0   0   0 
    let (assignment_vars, assignment_inputs, assignment_mems) = {
      let mut assignment_vars = Vec::new();
      let mut assignment_inputs = Vec::new();
      let mut assignment_mems = Vec::new();
      // Iteration i = 1
      let vars = vec![Scalar::from(2u32).neg().invert().to_bytes(), one, one, one, zero, one, two, zero];
      let inputs = vec![one, one, zero, zero, zero, one, one, two];
      let mems = vec![zero, zero, zero, zero, zero, one, one, two];
      let next_block_assignment_vars = VarsAssignment::new(&vars).unwrap();
      let next_block_assignment_inputs = InputsAssignment::new(&inputs).unwrap();
      let next_block_assignment_mems = MemsAssignment::new(&mems).unwrap();
      assignment_vars.push(next_block_assignment_vars);
      assignment_inputs.push(next_block_assignment_inputs.clone());
      assignment_mems.push(next_block_assignment_mems);
      exec_inputs.push(next_block_assignment_inputs);
      // Iteration i = 2
      let vars = vec![Scalar::from(1u32).neg().invert().to_bytes(), one, one, one, zero, one, two, zero];
      let inputs = vec![one, one, one, two, zero, one, two, four];
      let mems = vec![zero, zero, zero, zero, zero, one, one, two];
      let next_block_assignment_vars = VarsAssignment::new(&vars).unwrap();
      let next_block_assignment_inputs = InputsAssignment::new(&inputs).unwrap();
      let next_block_assignment_mems = MemsAssignment::new(&mems).unwrap();
      assignment_vars.push(next_block_assignment_vars);
      assignment_inputs.push(next_block_assignment_inputs.clone());
      assignment_mems.push(next_block_assignment_mems);
      exec_inputs.push(next_block_assignment_inputs);
      // Iteration i = 3
      let vars = vec![zero, zero, zero, zero, one, one, two, zero];
      let inputs = vec![one, one, two, four, zero, two, three, six];
      let mems = vec![zero, zero, zero, zero, zero, one, one, two];
      let next_block_assignment_vars = VarsAssignment::new(&vars).unwrap();
      let next_block_assignment_inputs = InputsAssignment::new(&inputs).unwrap();
      let next_block_assignment_mems = MemsAssignment::new(&mems).unwrap();
      assignment_vars.push(next_block_assignment_vars);
      assignment_inputs.push(next_block_assignment_inputs.clone());
      assignment_mems.push(next_block_assignment_mems);
      exec_inputs.push(next_block_assignment_inputs);
      // Iteration i = 4
      let vars = vec![zero; 8];
      let inputs = vec![zero; 8];
      let mems = vec![zero; 8];
      let next_block_assignment_vars = VarsAssignment::new(&vars).unwrap();
      let next_block_assignment_inputs = InputsAssignment::new(&inputs).unwrap();
      let next_block_assignment_mems = MemsAssignment::new(&mems).unwrap();
      assignment_vars.push(next_block_assignment_vars);
      assignment_inputs.push(next_block_assignment_inputs.clone());
      assignment_mems.push(next_block_assignment_mems);
      exec_inputs.push(next_block_assignment_inputs);
      
      (assignment_vars, assignment_inputs, assignment_mems)
    };
    block_vars_matrix.push(assignment_vars);
    block_inputs_matrix.push(assignment_inputs);
    block_mems_matrix.push(assignment_mems);

    // Block 0
    //        0    1   2   3   4    5   6   7    0   1   2   3   4   5   6   7
    // Exec:  v | b0  i0  s0 | _ | b1  i1  s1 | Z0  Z1  B0  T0  T1  M0  M1   _
    // 0      1    0   0   0   0    1   0   0  -3i   1   1   1   0   0   0   0
    let (assignment_vars, assignment_inputs, assignment_mems) = {
      let mut assignment_vars = Vec::new();
      let mut assignment_inputs = Vec::new();
      let mut assignment_mems = Vec::new();
      let vars = vec![Scalar::from(3u32).neg().invert().to_bytes(), one, one, one, zero, zero, zero, zero];
      let inputs = vec![one, zero, zero, zero, zero, one, zero, zero];
      let mems = vec![zero, zero, zero, zero, zero, one, one, two];
      let next_block_assignment_vars = VarsAssignment::new(&vars).unwrap();
      let next_block_assignment_inputs = InputsAssignment::new(&inputs).unwrap();
      let next_block_assignment_mems = MemsAssignment::new(&mems).unwrap();
      assignment_vars.push(next_block_assignment_vars);
      assignment_inputs.push(next_block_assignment_inputs.clone());
      assignment_mems.push(next_block_assignment_mems);
      exec_inputs.insert(0, next_block_assignment_inputs);

      (assignment_vars, assignment_inputs, assignment_mems)
    };
    block_vars_matrix.push(assignment_vars);
    block_inputs_matrix.push(assignment_inputs);
    block_mems_matrix.push(assignment_mems);

    // Pad exec_inputs with 0
    assert!(consis_num_proofs >= exec_inputs.len());
    let pad_size = consis_num_proofs - exec_inputs.len();
    for _ in 0..pad_size {
      exec_inputs.push(VarsAssignment::new(&vec![zero; num_vars]).unwrap());
    }

    // Witnesses for permutation cannot be generated until tau and r are generated
    // Both can only be generated at proving time

    // Memory accesses in address order: (v, addr, val, _)
    for _ in 0..4 {
      addr_mems_list.push(VarsAssignment::new(&vec![one, zero, one, zero]).unwrap());
    }
    for _ in 0..4 {
      addr_mems_list.push(VarsAssignment::new(&vec![one, one, two, zero]).unwrap());
    }

    (block_vars_matrix, block_inputs_matrix, exec_inputs, block_mems_matrix, addr_mems_list)
  };

  // --
  // End Assignments
  // --

  (
    input_block_num,
    output_block_num,
    input,
    output,
    output_block_index,

    num_vars,
    input_output_cutoff,
    total_num_proofs_bound,
    total_num_mem_accesses_bound,
    
    block_num_cons,
    block_num_non_zero_entries,
    block_num_instances,
    block_max_num_proofs,
    block_num_proofs,
    block_inst,

    consis_comb_num_cons,
    consis_comb_num_non_zero_entries,
    consis_num_proofs,
    consis_comb_inst,

    consis_check_num_cons_base,
    consis_check_num_non_zero_entries,
    consis_check_inst,
    
    perm_prelim_num_cons,
    perm_prelim_num_non_zero_entries,
    perm_prelim_inst,
    
    perm_root_num_cons,
    perm_root_num_non_zero_entries,
    perm_root_inst,
    
    perm_poly_num_cons_base,
    perm_poly_num_non_zero_entries,
    perm_poly_inst,

    block_num_mem_accesses,
    mem_extract_num_cons,
    mem_extract_num_non_zero_entries,
    mem_extract_inst,

    total_num_mem_accesses,
    mem_cohere_num_cons_base,
    mem_cohere_num_non_zero_entries,
    mem_cohere_inst,

    mem_addr_comb_num_cons,
    mem_addr_comb_num_non_zero_entries,
    mem_addr_comb_inst,

    mem_addr_poly_num_cons_base,
    mem_addr_poly_num_non_zero_entries,
    mem_addr_poly_inst,

    block_vars_matrix,
    block_inputs_matrix,
    exec_inputs,
    block_mems_matrix,
    addr_mems_list,
  )
}

fn main() {
  // produce an R1CS instance
  let (
    input_block_num,
    output_block_num,
    input,
    output,
    output_block_index,

    num_vars,
    input_output_cutoff,
    total_num_proofs_bound,
    total_num_mem_accesses_bound,

    block_num_cons,
    block_num_non_zero_entries,
    block_num_instances,
    block_max_num_proofs,
    block_num_proofs,
    block_inst,

    consis_comb_num_cons,
    consis_comb_num_non_zero_entries,
    consis_num_proofs,
    consis_comb_inst,

    consis_check_num_cons_base,
    consis_check_num_non_zero_entries,
    consis_check_inst,
    
    perm_prelim_num_cons,
    perm_prelim_num_non_zero_entries,
    perm_prelim_inst,
    
    perm_root_num_cons,
    perm_root_num_non_zero_entries,
    perm_root_inst,
    
    perm_poly_num_cons_base,
    perm_poly_num_non_zero_entries,
    perm_poly_inst,
    
    block_num_mem_accesses,
    mem_extract_num_cons,
    mem_extract_num_non_zero_entries,
    mem_extract_inst,

    total_num_mem_accesses,
    mem_cohere_num_cons_base,
    mem_cohere_num_non_zero_entries,
    mem_cohere_inst,

    mem_addr_comb_num_cons,
    mem_addr_comb_num_non_zero_entries,
    mem_addr_comb_inst,

    mem_addr_poly_num_cons_base,
    mem_addr_poly_num_non_zero_entries,
    mem_addr_poly_inst,

    block_vars_matrix,
    block_inputs_matrix,
    exec_inputs,
    block_mems_matrix,
    addr_mems_list,
  ) = produce_r1cs();

  let consis_check_num_cons = consis_check_num_cons_base * total_num_proofs_bound;
  let perm_size_bound = total_num_proofs_bound;
  let perm_poly_num_cons = perm_poly_num_cons_base * perm_size_bound;
  let mem_cohere_num_cons = mem_cohere_num_cons_base * total_num_mem_accesses_bound;
  let mem_addr_poly_num_cons = mem_addr_poly_num_cons_base * total_num_mem_accesses_bound;

  assert_eq!(block_num_instances, block_vars_matrix.len());
  assert_eq!(block_num_instances, block_inputs_matrix.len());
  for p in 0..block_num_instances {
    assert_eq!(block_vars_matrix[p].len(), block_inputs_matrix[p].len());
  }

  // produce public parameters
  let block_gens = SNARKGens::new(block_num_cons, num_vars, block_num_instances, block_num_non_zero_entries);
  let consis_comb_gens = SNARKGens::new(consis_comb_num_cons, 4 * num_vars, 1, consis_comb_num_non_zero_entries);
  let consis_check_gens = SNARKGens::new(consis_check_num_cons, total_num_proofs_bound * num_vars, 1, consis_check_num_non_zero_entries);
  let perm_prelim_gens = SNARKGens::new(perm_prelim_num_cons, num_vars, 1, perm_prelim_num_non_zero_entries);
  let perm_root_gens = SNARKGens::new(perm_root_num_cons, 4 * num_vars, 1, perm_root_num_non_zero_entries);
  let perm_poly_gens = SNARKGens::new(perm_poly_num_cons, perm_size_bound * num_vars, 1, perm_poly_num_non_zero_entries);
  let mem_extract_gens = SNARKGens::new(mem_extract_num_cons, 4 * num_vars, block_num_instances, mem_extract_num_non_zero_entries);
  let mem_cohere_gens = SNARKGens::new(mem_cohere_num_cons, total_num_mem_accesses_bound * 4, 1, mem_cohere_num_non_zero_entries);
  let mem_addr_comb_gens = SNARKGens::new(mem_addr_comb_num_cons, 4 * 4, 1, mem_addr_comb_num_non_zero_entries);
  let mem_addr_poly_gens = SNARKGens::new(mem_addr_poly_num_cons, total_num_mem_accesses_bound * 4, 1, mem_addr_poly_num_non_zero_entries);
  // Only use one version of gens_r1cs_sat
  // for size VAR
  let vars_gens = SNARKGens::new(block_num_cons, num_vars, block_num_instances, block_num_non_zero_entries).gens_r1cs_sat;
  // for size PROOF * VAR
  let proofs_times_vars_gens = SNARKGens::new(block_num_cons, perm_size_bound * num_vars, 1, block_num_non_zero_entries).gens_r1cs_sat;

  // create a commitment to the R1CS instance
  // TODO: change to encoding all r1cs instances
  let (block_comm, block_decomm) = SNARK::encode(&block_inst, &block_gens);
  let (consis_comb_comm, consis_comb_decomm) = SNARK::encode(&consis_comb_inst, &consis_comb_gens);
  let (consis_check_comm, consis_check_decomm) = SNARK::encode(&consis_check_inst, &consis_check_gens);
  let (perm_prelim_comm, perm_prelim_decomm) = SNARK::encode(&perm_prelim_inst, &perm_prelim_gens);
  let (perm_root_comm, perm_root_decomm) = SNARK::encode(&perm_root_inst, &perm_root_gens);
  let (perm_poly_comm, perm_poly_decomm) = SNARK::encode(&perm_poly_inst, &perm_poly_gens);
  let (mem_extract_comm, mem_extract_decomm) = SNARK::encode(&mem_extract_inst, &mem_extract_gens);
  let (mem_cohere_comm, mem_cohere_decomm) = SNARK::encode(&mem_cohere_inst, &mem_cohere_gens);
  let (mem_addr_comb_comm, mem_addr_comb_decomm) = SNARK::encode(&mem_addr_comb_inst, &mem_addr_comb_gens);
  let (mem_addr_poly_comm, mem_addr_poly_decomm) = SNARK::encode(&mem_addr_poly_inst, &mem_addr_poly_gens);

  // produce a proof of satisfiability
  let mut prover_transcript = Transcript::new(b"snark_example");
  let proof = SNARK::prove(
    input_block_num,
    output_block_num,
    &input,
    &output,
    output_block_index,
    
    num_vars,
    input_output_cutoff,
    total_num_proofs_bound,
    block_num_instances,
    block_max_num_proofs,
    &block_num_proofs,
    &block_inst,
    &block_comm,
    &block_decomm,
    &block_gens,
    
    consis_num_proofs,
    &consis_comb_inst,
    &consis_comb_comm,
    &consis_comb_decomm,
    &consis_comb_gens,
    consis_check_num_cons_base,
    &consis_check_inst,
    &consis_check_comm,
    &consis_check_decomm,
    &consis_check_gens,

    &perm_prelim_inst,
    &perm_prelim_comm,
    &perm_prelim_decomm,
    &perm_prelim_gens,
    &perm_root_inst,
    &perm_root_comm,
    &perm_root_decomm,
    &perm_root_gens,
    perm_poly_num_cons_base,
    &perm_poly_inst,
    &perm_poly_comm,
    &perm_poly_decomm,
    &perm_poly_gens,

    block_num_mem_accesses,
    &mem_extract_inst,
    &mem_extract_comm,
    &mem_extract_decomm,
    &mem_extract_gens,

    total_num_mem_accesses_bound,
    total_num_mem_accesses,
    mem_cohere_num_cons_base,
    &mem_cohere_inst,
    &mem_cohere_comm,
    &mem_cohere_decomm,
    &mem_cohere_gens,

    &mem_addr_comb_inst,
    &mem_addr_comb_comm,
    &mem_addr_comb_decomm,
    &mem_addr_comb_gens,

    mem_addr_poly_num_cons_base,
    &mem_addr_poly_inst,
    &mem_addr_poly_comm,
    &mem_addr_poly_decomm,
    &mem_addr_poly_gens,

    block_vars_matrix,
    block_inputs_matrix,
    exec_inputs,
    block_mems_matrix,
    addr_mems_list,

    &vars_gens,
    &proofs_times_vars_gens,
    &mut prover_transcript,
  );

  // verify the proof of satisfiability
  let mut verifier_transcript = Transcript::new(b"snark_example");
  assert!(proof
    .verify::<false>(
      input_block_num,
      output_block_num,
      &input,
      &output,
      output_block_index,

      num_vars,
      input_output_cutoff,
      total_num_proofs_bound,
      block_num_instances, 
      block_max_num_proofs, 
      &block_num_proofs, 
      block_num_cons, 
      &block_comm,
      &block_gens,

      consis_num_proofs, 
      consis_comb_num_cons, 
      &consis_comb_comm,
      &consis_comb_gens,
      consis_check_num_cons_base, 
      &consis_check_comm,
      &consis_check_gens,

      perm_prelim_num_cons,
      &perm_prelim_comm,
      &perm_prelim_gens,
      perm_root_num_cons,
      &perm_root_comm,
      &perm_root_gens,
      perm_poly_num_cons_base,
      &perm_poly_comm,
      &perm_poly_gens,

      mem_extract_num_cons,
      &mem_extract_comm,
      &mem_extract_gens,
      total_num_mem_accesses_bound,
      total_num_mem_accesses,
      mem_cohere_num_cons_base,
      &mem_cohere_comm,
      &mem_cohere_gens,
      mem_addr_comb_num_cons,
      &mem_addr_comb_comm,
      &mem_addr_comb_gens,
      mem_addr_poly_num_cons_base,
      &mem_addr_poly_comm,
      &mem_addr_poly_gens,

      &vars_gens,
      &proofs_times_vars_gens,
      &mut verifier_transcript
    ).is_ok());
  println!("proof verification successful!");
}
