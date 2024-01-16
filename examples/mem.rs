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
//!     assert A0 == 0                  assert A0 == 0
//!     assert V0 == 1                  LOAD(A0, V0)
//!     STORE(A0, V0)                   assert A1 == 1
//!     assert A1 == 1                  LOAD(A1, V1)
//!     assert V1 == 2                  i = i + V0
//!     STORE(A1, V1)                   s = s + V1
//!     s = 0                           if i != 3:
//!     i = 1                             b = 1
//!     if i != 3:                      else:
//!       b = 1                           b = 2
//!     else:                           }
//!       b = 2                           
//!   }
//! Note: take caution when translating STORE(0, 1) into constraints. If an execution of the block is invalid, this could cause a problem!
//! 
//! Converting each block to constraints:
//!    Block 0:                        Block 1:
//!  0   v = v * v                       v = v * v
//!  1   0 = w - v                       0 = w - v
//!  2   0 = b0                          0 = b0 - 1
//!  3   0 = i0                          0 = A0
//!  4   0 = s0                          0 = A1 - 1
//!  5   Z1 = (i0 - 3) * Z0              0 = i1 - i0 - V0
//!  6   0 = A0                          0 = s1 - s0 - V1
//!  7   0 = V0 - 1                      Z1 = (i1 - 3) * Z0
//!  8   0 = A1 - 1                      0 = B0 * (Z1 - 1)
//!  9   0 = V1 - 2                      0 = B0 * (b1 - 1)
//! 10   0 = B0 * (Z1 - 1)               0 = (1 - B0) * (i1 - 3)
//! 11   0 = B0 * (b1 - 1)               0 = (1 - B0) * (b1 - 2)
//! 12   0 = (1 - B0) * (i0 - 3)                         
//! 13   0 = (1 - B0) * (b1 - 2)               
//! 14   i1 = i0
//! 15   s1 = s0
//! 
//! Program States
//! The first entry of the witness is a copy of the valid bit, followed by a list of addresses and then a list of values
//! Put all memory states at the front of the witnesses
//!        0    1   2   3    4    5   6   7     0   1   2   3   4   5   6   7
//! Exec:  v | b0  i0  s0  | _ | b1  i1  s1  |  w  A0  A1  V0  V1  Z0  Z1  B0
//! 0      1    0   0   0    0    1   0   0     1   0   1   1   2 -3i   1   1
//! 1      1    1   0   0    0    1   1   2     1   0   1   1   2 -2i   1   1
//! 2      1    1   1   2    0    1   2   4     1   0   1   1   2 -1i   1   1
//! 3      1    1   2   4    0    2   3   6     1   0   1   1   2   0   0   0
//! 4      0    0   0   0    0    0   0   0     0   0   0   0   0   0   0   0
//!
#![allow(clippy::assertions_on_result_states)]
use std::{ops::Neg, cmp::max};

use curve25519_dalek::scalar::Scalar;
use libspartan::{instance::Instance, SNARKGens, VarsAssignment, SNARK, InputsAssignment, MemsAssignment};
use merlin::Transcript;

// Everything provided by the frontend
struct CompileTimeKnowledge {
  block_num_instances: usize,
  num_vars: usize,
  total_num_proofs_bound: usize,
  block_num_mem_accesses: Vec<usize>,
  total_num_mem_accesses_bound: usize,

  args: Vec<Vec<(Vec<(usize, isize)>, Vec<(usize, isize)>, Vec<(usize, isize)>)>>,

  input_block_num: usize,
  output_block_num: usize
}

// Everything provided by the prover
struct RunTimeKnowledge {
  block_max_num_proofs: usize,
  block_num_proofs: Vec<usize>,
  consis_num_proofs: usize,
  total_num_mem_accesses: usize,

  block_vars_matrix: Vec<Vec<VarsAssignment>>,
  block_inputs_matrix: Vec<Vec<InputsAssignment>>,
  exec_inputs: Vec<InputsAssignment>,
  addr_mems_list: Vec<MemsAssignment>,

  input: Vec<[u8; 32]>,
  output: Vec<[u8; 32]>,
  output_exec_num: usize
}

#[allow(non_snake_case)]
fn produce_r1cs() -> (
  CompileTimeKnowledge,
  RunTimeKnowledge
) {
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

  let minus_one = Scalar::from(1u32).neg().to_bytes();
  let zero = Scalar::zero().to_bytes();
  let one = Scalar::one().to_bytes();
  let two = Scalar::from(2u32).to_bytes();
  let three = Scalar::from(3u32).to_bytes();
  let four = Scalar::from(4u32).to_bytes();
  let six = Scalar::from(6u32).to_bytes();

  // --
  // COMPILE TIME KNOWLEDGE
  // --
  
  // num_vars should be consistent accross the instances
  // everything else is instance-specific
  // Divide inputs into (1, input, 1, output)
  // So num_inputs = num_outputs = num_vars / 2 - 1
  let num_vars = 8;

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

  // Number of R1CS instances
  let block_num_instances = 2;

  // Program States
  // Put all memory states at the front of the witnesses
  //        0    1   2   3    4    5   6   7     0   1   2   3   4   5   6   7
  // Exec:  v | b0  i0  s0  | _ | b1  i1  s1  |  w  A0  A1  V0  V1  Z0  Z1  B0
  let args = {
    let num_inputs = num_vars / 2;

    let V_valid = 0;
    let V_cnst = V_valid;
    let V_b0 = 1;
    let V_i0 = 2;
    let V_s0 = 3;
    let V_b1 = num_inputs + 1;
    let V_i1 = num_inputs + 2;
    let V_s1 = num_inputs + 3;
    let V_w = num_vars;
    let V_A0 = num_vars + 1;
    let V_A1 = num_vars + 2;
    let V_V0 = num_vars + 3;
    let V_V1 = num_vars + 4;
    let V_Z0 = num_vars + 5;
    let V_Z1 = num_vars + 6;
    let V_B0 = num_vars + 7;

    let mut args = Vec::new();
    // Instance 0: block 1
    // Instances need to be sorted form highest # of execution -> lowest
    let arg = vec![
      // 0: v * v = v
      (vec![(V_valid, 1)], vec![(V_valid, 1)], vec![(V_valid, 1)]),
      // 1: 0 = w - v
      (vec![], vec![], vec![(V_w, 1), (V_valid, -1)]),
      // 2: 0 = b0 - 1
      (vec![], vec![], vec![(V_b0, 1), (V_cnst, -1)]),
      // 3: 0 = A0
      (vec![], vec![], vec![(V_A0, 1)]),
      // 4: 0 = A1 - 1
      (vec![], vec![], vec![(V_A1, 1), (V_cnst, -1)]),
      // 5: 0 = i1 - i0 - V0
      (vec![], vec![], vec![(V_i1, 1), (V_i0, -1), (V_V0, -1)]),
      // 6: 0 = s1 - s0 - V1
      (vec![], vec![], vec![(V_s1, 1), (V_s0, -1), (V_V1, -1)]),
      // 7: (i1 - 3) * Z0 = Z1
      (vec![(V_i1, 1), (V_cnst, -3)], vec![(V_Z0, 1)], vec![(V_Z1, 1)]),
      // 8: B0 * (Z1 - 1) = 0
      (vec![(V_B0, 1)], vec![(V_Z1, 1), (V_cnst, -1)], vec![]),
      // 9: B0 * (b1 - 1) = 0
      (vec![(V_B0, 1)], vec![(V_b1, 1), (V_cnst, -1)], vec![]),
      // 10: (1 - B0) * (i1 - 3) = 0
      (vec![(V_cnst, 1), (V_B0, -1)], vec![(V_i1, 1), (V_cnst, -3)], vec![]),
      // 11: (1 - B0) * (b1 - 2) = 0
      (vec![(V_cnst, 1), (V_B0, -1)], vec![(V_b1, 1), (V_cnst, -2)], vec![])
    ];
    args.push(arg);
      
    // Instance 1: block 0
    let arg = vec![
      // 0: v * v = v
      (vec![(V_valid, 1)], vec![(V_valid, 1)], vec![(V_valid, 1)]),
      // 1: 0 = w - v
      (vec![], vec![], vec![(V_w, 1), (V_valid, -1)]),
      // 2: 0 = b0
      (vec![], vec![], vec![(V_b0, 1)]),
      // 3: 0 = i0
      (vec![], vec![], vec![(V_i0, 1)]),
      // 4: 0 = s0
      (vec![], vec![], vec![(V_s0, 1)]),
      // 5: (i0 - 3) * Z0 = Z1
      (vec![(V_i0, 1), (V_cnst, -3)], vec![(V_Z0, 1)], vec![(V_Z1, 1)]),
      // 6: 0 = A0
      (vec![], vec![], vec![(V_A0, 1)]),
      // 7: 0 = V0 - 1
      (vec![], vec![], vec![(V_V0, 1), (V_cnst, -1)]),
      // 8: 0 = A1 - 1
      (vec![], vec![], vec![(V_A1, 1), (V_cnst, -1)]),
      // 9: 0 = V1 - 2
      (vec![], vec![], vec![(V_V1, 1), (V_cnst, -2)]),
      // 10: B0 * (Z1 - 1) = 0
      (vec![(V_B0, 1)], vec![(V_Z1, 1), (V_cnst, -1)], vec![]),
      // 11: B0 * (b1 - 1) = 0
      (vec![(V_B0, 1)], vec![(V_b1, 1), (V_cnst, -1)], vec![]),
      // 12: (1 - B0) * (i1 - 3) = 0
      (vec![(V_cnst, 1), (V_B0, -1)], vec![(V_i1, 1), (V_cnst, -3)], vec![]),
      // 13: (1 - B0) * (b1 - 2) = 0
      (vec![(V_cnst, 1), (V_B0, -1)], vec![(V_b1, 1), (V_cnst, -2)], vec![]),
      // 14: 0 = i1 - i0
      (vec![], vec![], vec![(V_i1, 1), (V_i0, -1)]),
      // 15: 0 = s1 - s0
      (vec![], vec![], vec![(V_s1, 1), (V_s0, -1)]),
    ];
    args.push(arg);

    args
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
  let output_exec_num = 3;
  // How many memory accesses per block?
  let block_num_mem_accesses = vec![2, 2];
  // How many memory accesses are there?
  let total_num_mem_accesses = 8;

  // --
  // Begin Assignments
  // --

  let (
    block_vars_matrix, 
    block_inputs_matrix, 
    exec_inputs,
    addr_mems_list
  ) = {

    let mut block_vars_matrix = Vec::new();
    let mut block_inputs_matrix = Vec::new();
    let mut exec_inputs = Vec::new();
    let mut addr_mems_list = Vec::new();

    // Block 1
    // Exec:  v | b0  i0  s0  | _ | b1  i1  s1  |  w  A0  A1  V0  V1  Z0  Z1  B0
    // 0      1    1   0   0    0    1   1   2     1   0   1   1   2 -2i   1   1
    // 1      1    1   1   2    0    1   2   4     1   0   1   1   2 -1i   1   1
    // 2      1    1   2   4    0    2   3   6     1   0   1   1   2   0   0   0
    // 3      0    0   0   0    0    0   0   0     0   0   0   0   0   0   0   0
    let (assignment_vars, assignment_inputs) = {
      let mut assignment_vars = Vec::new();
      let mut assignment_inputs = Vec::new();
      // Iteration i = 1
      let inputs = vec![one, one, zero, zero, zero, one, one, two];
      let vars = vec![one, zero, one, one, two, Scalar::from(2u32).neg().invert().to_bytes(), one, one];
      let next_block_assignment_vars = VarsAssignment::new(&vars).unwrap();
      let next_block_assignment_inputs = InputsAssignment::new(&inputs).unwrap();
      assignment_vars.push(next_block_assignment_vars);
      assignment_inputs.push(next_block_assignment_inputs.clone());
      exec_inputs.push(next_block_assignment_inputs);
      // Iteration i = 2
      let inputs = vec![one, one, one, two, zero, one, two, four];
      let vars = vec![one, zero, one, one, two, Scalar::from(1u32).neg().invert().to_bytes(), one, one];
      let next_block_assignment_vars = VarsAssignment::new(&vars).unwrap();
      let next_block_assignment_inputs = InputsAssignment::new(&inputs).unwrap();
      assignment_vars.push(next_block_assignment_vars);
      assignment_inputs.push(next_block_assignment_inputs.clone());
      exec_inputs.push(next_block_assignment_inputs);
      // Iteration i = 3
      let inputs = vec![one, one, two, four, zero, two, three, six];
      let vars = vec![one, zero, one, one, two, zero, zero, zero];
      let next_block_assignment_vars = VarsAssignment::new(&vars).unwrap();
      let next_block_assignment_inputs = InputsAssignment::new(&inputs).unwrap();
      assignment_vars.push(next_block_assignment_vars);
      assignment_inputs.push(next_block_assignment_inputs.clone());
      exec_inputs.push(next_block_assignment_inputs);
      // Iteration i = 4
      let vars = vec![zero; 8];
      let inputs = vec![zero; 8];
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
    // Exec:  v | b0  i0  s0  | _ | b1  i1  s1  |  w  A0  A1  V0  V1  Z0  Z1  B0
    // 0      1    0   0   0    0    1   0   0     1   0   1   1   2 -3i   1   1
    let (assignment_vars, assignment_inputs) = {
      let mut assignment_vars = Vec::new();
      let mut assignment_inputs = Vec::new();
      let inputs = vec![one, zero, zero, zero, zero, one, zero, zero];
      let vars = vec![one, zero, one, one, two, Scalar::from(3u32).neg().invert().to_bytes(), one, one];
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

    // Memory accesses in address order: (v, addr, val, D)
    // where D[k] = v[k + 1] * (addr[k + 1] - addr[k] - 1)
    for _ in 0..3 {
      addr_mems_list.push(VarsAssignment::new(&vec![one, zero, one, minus_one]).unwrap());
    }
    addr_mems_list.push(VarsAssignment::new(&vec![one, zero, one, zero]).unwrap());
    for _ in 0..3 {
      addr_mems_list.push(VarsAssignment::new(&vec![one, one, two, minus_one]).unwrap());
    }
    addr_mems_list.push(VarsAssignment::new(&vec![one, one, two, zero]).unwrap());

    (block_vars_matrix, block_inputs_matrix, exec_inputs, addr_mems_list)
  };

  // --
  // End Assignments
  // --

  (
    // COMPILE TIME KNOWLEDGE
    CompileTimeKnowledge {
      block_num_instances,
      num_vars,
      total_num_proofs_bound,
      block_num_mem_accesses,
      total_num_mem_accesses_bound,

      args,
      
      input_block_num,
      output_block_num
    },

    // RUNTIME KNOWLEDGE
    RunTimeKnowledge {
      block_max_num_proofs,
      block_num_proofs,
      consis_num_proofs,
      total_num_mem_accesses,

      block_vars_matrix,
      block_inputs_matrix,
      exec_inputs,
      addr_mems_list,

      input,
      output,
      output_exec_num
    }
  )
}

fn main() {
  // produce an R1CS instance
  let (ctk, rtk) = produce_r1cs();
  let block_num_instances = ctk.block_num_instances;
  let num_vars = ctk.num_vars;
  let total_num_proofs_bound = ctk.total_num_proofs_bound;
  let block_num_mem_accesses = ctk.block_num_mem_accesses;
  let total_num_mem_accesses_bound = ctk.total_num_mem_accesses_bound;

  let block_vars_matrix = rtk.block_vars_matrix;
  let block_inputs_matrix = rtk.block_inputs_matrix;

  // Generate all remaining instances

  // BLOCK INSTANCES
  let (block_num_cons, block_num_non_zero_entries, block_inst) = Instance::gen_block_inst(block_num_instances, num_vars, &ctk.args);

  // CONSIS INSTANCES
  // CONSIS is consisted of two instances
  // CONSIS_COMB performs random linear combination on inputs and outputs to a single value
  // It is parallelized for consis_num_proofs copies
  // CONSIS_CHECK checks that these values indeed matches
  // There is only one copy for CONSIS_CHECK
  // CONSIS_COMB
  let (consis_comb_num_cons, consis_comb_num_non_zero_entries, consis_comb_inst) = Instance::gen_consis_comb_inst(num_vars);
  // CONSIS_CHECK
  let (consis_check_num_cons_base, consis_check_num_non_zero_entries, consis_check_inst) = Instance::gen_consis_check_inst(num_vars, total_num_proofs_bound);

  // PERM INSTANCES
  // PERM is consisted of four instances
  // PERM_PRELIM checks the correctness of (r, r^2, ...)
  // PERM_ROOT and PERM_BLOCK_POLY compute the polynomial defined by block_inputs
  // PERM_ROOT and PERM_EXEC_POLY compute the polynomial defined by exec_inputs
  // Finally, the verifier checks that the two products are the same
  // The product is defined by PROD = \prod(\tau - (\sum_i a_i * r^{i-1}))
  // There is only one proof
  // PERM_PRELIM
  let (perm_prelim_num_cons, perm_prelim_num_non_zero_entries, perm_prelim_inst) = Instance::gen_perm_prelim_inst(num_vars);
  // PERM_ROOT
  let (perm_root_num_cons, perm_root_num_non_zero_entries, perm_root_inst) = Instance::gen_perm_root_inst(num_vars);
  // PERM_POLY (for PERM_BLOCK_POLY, PERM_EXEC_POLY, MEM_BLOCK_POLY), MEM_ADDR_POLY
  let (perm_poly_num_cons_base, perm_poly_num_non_zero_entries, perm_poly_inst) = Instance::gen_perm_poly_inst(num_vars, total_num_proofs_bound);

  // MEM INSTANCES
  // MEM_EXTRACT
  let (mem_extract_num_cons, mem_extract_num_non_zero_entries, mem_extract_inst) = Instance::gen_mem_extract_inst(block_num_instances, num_vars, &block_num_mem_accesses);
  // MEM_COHERE
  let (mem_cohere_num_cons_base, mem_cohere_num_non_zero_entries, mem_cohere_inst) = Instance::gen_mem_cohere_inst(total_num_mem_accesses_bound);
  // MEM_BLOCK_POLY is PERM_BLOCK_POLY
  // MEM_ADDR_COMB
  let (mem_addr_comb_num_cons, mem_addr_comb_num_non_zero_entries, mem_addr_comb_inst) = Instance::gen_mem_addr_comb_inst();
  // MEM_ADDR_POLY
  let (mem_addr_poly_num_cons_base, mem_addr_poly_num_non_zero_entries, mem_addr_poly_inst) = Instance::gen_mem_addr_poly_inst(total_num_mem_accesses_bound);

  // --
  // INSTANCE PREPROCESSING
  // --
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
  let proofs_times_vars_gens = SNARKGens::new(block_num_cons, max(total_num_proofs_bound, total_num_mem_accesses_bound) * num_vars, 1, block_num_non_zero_entries).gens_r1cs_sat;

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
    ctk.input_block_num,
    ctk.output_block_num,
    &rtk.input,
    &rtk.output,
    rtk.output_exec_num,
    
    num_vars,
    total_num_proofs_bound,
    block_num_instances,
    rtk.block_max_num_proofs,
    rtk.block_num_proofs.clone(),
    &block_inst,
    &block_comm,
    &block_decomm,
    &block_gens,
    
    rtk.consis_num_proofs,
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

    &block_num_mem_accesses,
    &mem_extract_inst,
    &mem_extract_comm,
    &mem_extract_decomm,
    &mem_extract_gens,

    total_num_mem_accesses_bound,
    rtk.total_num_mem_accesses,
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
    rtk.exec_inputs,
    rtk.addr_mems_list,

    &vars_gens,
    &proofs_times_vars_gens,
    &mut prover_transcript,
  );

  // verify the proof of satisfiability
  let mut verifier_transcript = Transcript::new(b"snark_example");
  assert!(proof.verify::<false>(
    ctk.input_block_num,
    ctk.output_block_num,
    &rtk.input,
    &rtk.output,
    rtk.output_exec_num,

    num_vars,
    total_num_proofs_bound,
    block_num_instances, 
    rtk.block_max_num_proofs, 
    rtk.block_num_proofs, 
    block_num_cons, 
    &block_comm,
    &block_gens,

    rtk.consis_num_proofs, 
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
    rtk.total_num_mem_accesses,
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
