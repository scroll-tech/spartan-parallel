use std::cmp::max;

use crate::dense_mlpoly::{PolyCommitment, DensePolynomial};
use crate::math::Math;
use crate::r1csproof::R1CSGens;
use crate::R1CSInstance;
use crate::errors::R1CSError;
use crate::scalar::Scalar;

/// `Instance` holds the description of R1CS matrices and a hash of the matrices
#[derive(Clone)]
pub struct Instance {
  /// Matrix of Instance
  pub inst: crate::R1CSInstance,
  /// Digest of Instance
  pub digest: Vec<u8>,
}

impl Instance {
  /// Constructs a new `Instance` and an associated satisfying assignment
  pub fn new(
    num_instances: usize,
    num_cons: usize,
    num_vars: usize,
    A: &Vec<Vec<(usize, usize, [u8; 32])>>,
    B: &Vec<Vec<(usize, usize, [u8; 32])>>,
    C: &Vec<Vec<(usize, usize, [u8; 32])>>,
  ) -> Result<Instance, R1CSError> {
    let (num_vars_padded, num_cons_padded) = {
      let num_vars_padded = {
        let mut num_vars_padded = num_vars;

        // ensure that num_vars_padded a power of two
        if num_vars_padded.next_power_of_two() != num_vars_padded {
          num_vars_padded = num_vars_padded.next_power_of_two();
        }
        num_vars_padded
      };

      let num_cons_padded = {
        let mut num_cons_padded = num_cons;

        // ensure that num_cons_padded is at least 2
        if num_cons_padded == 0 || num_cons_padded == 1 {
          num_cons_padded = 2;
        }

        // ensure that num_cons_padded is power of 2
        if num_cons.next_power_of_two() != num_cons {
          num_cons_padded = num_cons.next_power_of_two();
        }
        num_cons_padded
      };

      (num_vars_padded, num_cons_padded)
    };

    let bytes_to_scalar =
      |tups: &[(usize, usize, [u8; 32])]| -> Result<Vec<(usize, usize, Scalar)>, R1CSError> {
        let mut mat: Vec<(usize, usize, Scalar)> = Vec::new();
        for &(row, col, val_bytes) in tups {
          // row must be smaller than num_cons
          if row >= num_cons {
            println!("ROW: {}, NUM_CONS: {}", row, num_cons);
            return Err(R1CSError::InvalidIndex);
          }

          // col must be smaller than num_vars
          if col >= num_vars {
            println!("COL: {}, NUM_VARS: {}", col, num_vars);
            return Err(R1CSError::InvalidIndex);
          }

          let val = Scalar::from_bytes(&val_bytes);
          if val.is_some().unwrap_u8() == 1 {
            // if col >= num_vars, it means that it is referencing a 1 or input in the satisfying
            // assignment
            if col >= num_vars {
              mat.push((row, col + num_vars_padded - num_vars, val.unwrap()));
            } else {
              mat.push((row, col, val.unwrap()));
            }
          } else {
            return Err(R1CSError::InvalidScalar);
          }
        }

        // pad with additional constraints up until num_cons_padded if the original constraints were 0 or 1
        // we do not need to pad otherwise because the dummy constraints are implicit in the sum-check protocol
        if num_cons == 0 || num_cons == 1 {
          for i in tups.len()..num_cons_padded {
            mat.push((i, num_vars, Scalar::zero()));
          }
        }

        Ok(mat)
      };

    let mut A_scalar_list = Vec::new();
    let mut B_scalar_list = Vec::new();
    let mut C_scalar_list = Vec::new();

    for i in 0..num_instances {
      let A_scalar = bytes_to_scalar(&A[i]);
      if A_scalar.is_err() {
        return Err(A_scalar.err().unwrap());
      }
      A_scalar_list.push(A_scalar.unwrap());

      let B_scalar = bytes_to_scalar(&B[i]);
      if B_scalar.is_err() {
        return Err(B_scalar.err().unwrap());
      }
      B_scalar_list.push(B_scalar.unwrap());

      let C_scalar = bytes_to_scalar(&C[i]);
      if C_scalar.is_err() {
        return Err(C_scalar.err().unwrap());
      }
      C_scalar_list.push(C_scalar.unwrap());
    }

    let inst = R1CSInstance::new(
      num_instances,
      num_cons_padded,
      num_vars_padded,
      &A_scalar_list,
      &B_scalar_list,
      &C_scalar_list,
    );

    let digest = inst.get_digest();

    Ok(Instance { inst, digest })
  }

  /// Sort the instances based on index
  // index[i] = j => the original jth entry should now be at the ith position
  pub fn sort(&mut self, num_instances: usize, index: &Vec<usize>) {
    self.inst.sort(num_instances, index);
    self.digest = self.inst.get_digest();
  }

  // Generates a constraints based on supplied (variable, constant) pairs
  fn gen_constr(
    mut A: Vec<(usize, usize, [u8; 32])>, 
    mut B: Vec<(usize, usize, [u8; 32])>, 
    mut C: Vec<(usize, usize, [u8; 32])>,
    i: usize, 
    args_A: Vec<(usize, isize)>, 
    args_B: Vec<(usize, isize)>, 
    args_C: Vec<(usize, isize)>
  ) -> (
      Vec<(usize, usize, [u8; 32])>, 
      Vec<(usize, usize, [u8; 32])>, 
      Vec<(usize, usize, [u8; 32])>
  ) {
    let int_to_scalar = |i: isize| {
      let abs_scalar = Scalar::from(i.abs() as u64);
      if i < 0 {
        abs_scalar.neg().to_bytes()
      } else {
        abs_scalar.to_bytes()
      }
    };
    for vars in &args_A {
      let sc = int_to_scalar(vars.1);
      A.push((i, vars.0, sc));
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

  // gen_constr from byte lists
  fn gen_constr_bytes(
    mut A: Vec<(usize, usize, [u8; 32])>, 
    mut B: Vec<(usize, usize, [u8; 32])>, 
    mut C: Vec<(usize, usize, [u8; 32])>,
    i: usize, 
    args_A: Vec<(usize, [u8; 32])>, 
    args_B: Vec<(usize, [u8; 32])>, 
    args_C: Vec<(usize, [u8; 32])>
  ) -> (
      Vec<(usize, usize, [u8; 32])>, 
      Vec<(usize, usize, [u8; 32])>, 
      Vec<(usize, usize, [u8; 32])>
  ) {
    for vars in &args_A {
      A.push((i, vars.0, vars.1));
    }
    for vars in &args_B {
      B.push((i, vars.0, vars.1));
    }
    for vars in &args_C {
      C.push((i, vars.0, vars.1));
    }
    (A, B, C)
  }
  
  /// Generates BLOCK instances based on inputs
  pub fn gen_block_inst(
    num_instances: usize, 
    num_vars: usize, 
    args: &Vec<Vec<(Vec<(usize, [u8; 32])>, Vec<(usize, [u8; 32])>, Vec<(usize, [u8; 32])>)>>,
  ) -> (usize, usize, Instance) {
    assert_eq!(num_instances, args.len());

    let mut block_num_cons = 0;
    let mut block_num_non_zero_entries = 0;

    let mut A_list = Vec::new();
    let mut B_list = Vec::new();
    let mut C_list = Vec::new();
    for arg in args {
      // Check if num_cons > block_num_cons
      block_num_cons = max(block_num_cons, arg.len());
      let mut tmp_nnz_A = 0;
      let mut tmp_nnz_B = 0;
      let mut tmp_nnz_C = 0;
      let (A, B, C) = {
        let mut A: Vec<(usize, usize, [u8; 32])> = Vec::new();
        let mut B: Vec<(usize, usize, [u8; 32])> = Vec::new();
        let mut C: Vec<(usize, usize, [u8; 32])> = Vec::new();
  
        for i in 0..arg.len() {
          tmp_nnz_A += arg[i].0.len();
          tmp_nnz_B += arg[i].1.len();
          tmp_nnz_C += arg[i].2.len();
          (A, B, C) = Instance::gen_constr_bytes(A, B, C,
            i, arg[i].0.clone(), arg[i].1.clone(), arg[i].2.clone());
        }
        (A, B, C)
      };
      // Recalculate num_non_zero_entries
      block_num_non_zero_entries = max(max(max(block_num_non_zero_entries, tmp_nnz_A), tmp_nnz_B), tmp_nnz_C);
      A_list.push(A);
      B_list.push(B);
      C_list.push(C);
    }
    block_num_cons = block_num_cons.next_power_of_two();
    
    let block_inst = Instance::new(num_instances, block_num_cons, 2 * num_vars, &A_list, &B_list, &C_list).unwrap();
    (block_num_cons, block_num_non_zero_entries, block_inst)
  }

  /// Generates CONSIS_CHECK instance based on parameters
  /// CONSIS_CHECK takes in consis_w2 = <_, _, _, _, i, o, _, _>
  /// where i = v * (v + i0 * r + i1 * r^2 + i2 * r^3 + ...) and o = v * (v + o0 * r + o1 * r^2 + o2 * r^3 + ...)
  /// See perm_root
  /// and verifies (o[k] - i[k + 1]) * i[k + 1] = 0 for all k
  pub fn gen_consis_check_inst() -> (usize, usize, Instance) {
    let consis_check_num_cons = 2;
    let consis_check_num_non_zero_entries = 2;
  
    let V_i = 4;
    let V_o = 5;
    let width = 8;
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
        // Output matches input
        (A, B, C) = Instance::gen_constr(A, B, C,
          0, vec![(V_o, 1), (width + V_i, -1)], vec![(width + V_i, 1)], vec![]);
        (A, B, C)
      };
      A_list.push(A);
      B_list.push(B);
      C_list.push(C);
  
      let consis_check_inst = Instance::new(1, consis_check_num_cons, 2 * width, &A_list, &B_list, &C_list).unwrap();
      
      consis_check_inst
    };
    (consis_check_num_cons, consis_check_num_non_zero_entries, consis_check_inst)
  }

  /// Generates PERM_ROOT instance based on parameters
  /// Witnesses of PERM_ROOT is consisted of [w0, w1, w2, w3], each of size num_vars
  /// w0: tau, r, r^2, ...
  /// w1: one block_inputs entry: v, _, i0, i1, ..., o0, o1, ...
  /// w2: one block_inputs entry dot product <r>: _, _, ZO, r * i1, r^2 * i2, r^3 * i3, ...
  /// w3: one root of the polynomial: v, x, pi, D, I, O, _, _
  /// where I = v * (v + i0 + r * i1 + r^2 * i2 + ...),
  ///       O = v * (v + ZO)
  ///       ZO * r^n = r^n * o0 + r^(n + 1) * o1, ...,
  /// are used by the consistency check, AND
  /// w3[0]: valid bit, should match block_inputs[0]
  /// w3[1]: one root of the polynomial: v * (tau - i0 - r * i1 - r^2 * i2 - ...)
  /// are used by permutation
  /// Note: Only process the first num_inputs_unpadded inputs since the rest are unused
  pub fn gen_perm_root_inst(num_inputs_unpadded: usize, num_vars: usize) -> (usize, usize, Instance) {

    let perm_root_num_cons = 2 * num_inputs_unpadded + 2;
    let perm_root_num_non_zero_entries = 4 * num_inputs_unpadded + 1;
    let perm_root_inst = {
      let (A, B, C) = {
        let mut A: Vec<(usize, usize, [u8; 32])> = Vec::new();
        let mut B: Vec<(usize, usize, [u8; 32])> = Vec::new();
        let mut C: Vec<(usize, usize, [u8; 32])> = Vec::new();
  
        let V_tau = 0;
        // V_r(0) == tau and should be skipped!
        let V_r = |i: usize| i;
        let V_valid = num_vars;
        let V_cnst = V_valid;
        let V_input = |i: usize| num_vars + 2 + i;
        let V_output = |i: usize| num_vars + 2 + (num_inputs_unpadded - 1) + i;
        let V_ZO = 2 * num_vars + 2;
        let V_input_dot_prod = |i: usize| if i == 0 { V_input(0) } else { 2 * num_vars + 2 + i };
        let V_output_dot_prod = |i: usize| 2 * num_vars + 2 + (num_inputs_unpadded - 1) + i;
        let V_I = 3 * num_vars + 4;
        let V_O = 3 * num_vars + 5;

        let mut constraint_count = 0;

        // correctness of w2
        // for i1..
        for i in 1..num_inputs_unpadded - 1 {
          (A, B, C) = Instance::gen_constr(A, B, C,
            constraint_count, vec![(V_input(i), 1)], vec![(V_r(i), 1)], vec![(V_input_dot_prod(i), 1)]);
          constraint_count += 1;
        }
        // for o0, o1..
        for i in 0..num_inputs_unpadded - 1 {
          (A, B, C) = Instance::gen_constr(A, B, C,
            constraint_count, vec![(V_output(i), 1)], vec![(V_r(i + num_inputs_unpadded - 1), 1)], vec![(V_output_dot_prod(i), 1)]);
          constraint_count += 1;
        }
        // ZO * r^n = r^n * o0 + r^(n + 1) * o1, ...
        (A, B, C) = Instance::gen_constr(A, B, C,
          constraint_count, 
          vec![(V_ZO, 1)], 
          vec![(V_r(num_inputs_unpadded - 1), 1)],
          (0..num_inputs_unpadded - 1).map(|i| (V_output_dot_prod(i), 1)).collect()
        );
        constraint_count += 1;
        // I = v * (v + i0 + r * i1 + r^2 * i2 + ...)
        (A, B, C) = Instance::gen_constr(A, B, C,
          constraint_count, 
          vec![(V_valid, 1)], 
          [vec![(V_cnst, 1)], (0..num_inputs_unpadded - 1).map(|i| (V_input_dot_prod(i), 1)).collect()].concat(),
          vec![(V_I, 1)]
        );
        constraint_count += 1;
        // O = v * (v + ZO)
        (A, B, C) = Instance::gen_constr(A, B, C,
          constraint_count, 
          vec![(V_valid, 1)], 
          vec![(V_valid, 1), (V_ZO, 1)],
          vec![(V_O, 1)]
        );
        constraint_count += 1;
        // correctness of w3[0]
        (A, B, C) = Instance::gen_constr(A, B, C, 
          constraint_count, vec![], vec![], vec![(V_cnst, 1), (3 * num_vars, -1)]);
        constraint_count += 1;
        // correctness of w3[1]
        (A, B, C) = Instance::gen_constr(A, B, C, constraint_count,
            [vec![(V_tau, 1)], (0..2 * num_inputs_unpadded - 2).map(|i| (V_input_dot_prod(i), -1)).collect()].concat(), 
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
    (perm_root_num_cons, perm_root_num_non_zero_entries, perm_root_inst)
  }

  /// Generates PERM_POLY instance based on parameters
  /// The strategy is to compute the local polynomials (evaluated on tau) for each block instance
  /// Each w3[p][2] (i.e. w3[p][0][2]) stores the product pi for instance P. The verifier obtains all P of them and multiply them together.
  /// The correct formular is pi[k] = v[k] * x[k] * (pi[k+1] + (1 - v[k+1])))
  /// To do this, think of each entry of w3[k] (w3[p][k]) as a tuple (v, x, pi, D)
  /// v[k]  <- whether the entry is valid
  /// x[k]  <- \tau - (\sum_i a_i * r^{i-1})
  /// pi[k] <- v[k] * D[k]
  /// D[k] <- x[k] * (pi[k + 1] + (1 - v[k + 1]))
  pub fn gen_perm_poly_inst() -> (usize, usize, Instance) {
    let perm_poly_num_cons = 2;
    let perm_poly_num_non_zero_entries = 4;
    
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
        let width = 4;

        let mut constraint_count = 0;
        // D[k] = x[k] * (pi[k + 1] + (1 - v[k + 1]))
        (A, B, C) = Instance::gen_constr(A, B, C,
          constraint_count, 
          vec![(V_x, 1)], 
          vec![(width + V_pi, 1), (V_cnst, 1), (width + V_valid, -1)], 
          vec![(V_d, 1)]);
        constraint_count += 1;
        // pi[k] = v[k] * D[k]
        (A, B, C) = Instance::gen_constr(A, B, C,
          constraint_count, vec![(V_valid, 1)], vec![(V_d, 1)], vec![(V_pi, 1)]);
        (A, B, C)   
      };

      let A_list = vec![A.clone()];
      let B_list = vec![B.clone()];
      let C_list = vec![C.clone()];

      let perm_poly_inst = Instance::new(1, perm_poly_num_cons, 2 * 4, &A_list, &B_list, &C_list).unwrap();
      
      perm_poly_inst
    };
    (perm_poly_num_cons, perm_poly_num_non_zero_entries, perm_poly_inst)
  }

  /// Generates a num_instances x num_vars INPUT MATRIX
  /// For row i, the first num_mems_accesses[i] entries is 1 and the rest is 0
  /// Used for gen_mem_extract_inst
  pub fn gen_mem_extract_mask(
    num_instances: usize,
    num_vars: usize, 
    num_mems_accesses: &Vec<usize>, 
    vars_gens: &R1CSGens
  ) -> (
    Vec<Vec<Vec<Scalar>>>,
    Vec<DensePolynomial>,
    Vec<PolyCommitment>
  ) {
    // Generate Mask
    let zero = Scalar::zero();
    let one = Scalar::one();
    let mem_block_mask: Vec<Vec<Vec<Scalar>>> = num_mems_accesses.iter().map(|i| vec![[vec![one; *i], vec![zero; num_vars - i]].concat()]).collect();

    // commit the witnesses and inputs separately instance-by-instance
    let mut mem_block_poly_mask_list = Vec::new();
    let mut mem_block_comm_mask_list = Vec::new();

    for p in 0..num_instances {
      let (mem_block_poly_mask, mem_block_comm_mask) = {
        // create a multilinear polynomial using the supplied assignment for variables
        let mem_block_poly_mask = DensePolynomial::new(mem_block_mask[p][0].clone());
        // produce a commitment to the satisfying assignment
        let (mem_block_comm_mask, _blinds_vars) = mem_block_poly_mask.commit(&vars_gens.gens_pc, None);

        (mem_block_poly_mask, mem_block_comm_mask)
      };
      mem_block_poly_mask_list.push(mem_block_poly_mask);
      mem_block_comm_mask_list.push(mem_block_comm_mask);
    }

    (
      mem_block_mask,
      mem_block_poly_mask_list,
      mem_block_comm_mask_list,
    )
  }

  /// Generates MEM_EXTRACT instance based on parameters
  /// We want to combine all memory accesses in the witness list to a single polynomial root, given by the formula
  ///                           PI(mask * (tau - addr - r * val) + 1 - mask)
  /// Which is then divided into three intermediate variables for each (addr, val)
  /// - MR = r * val
  /// - MD = mask * (tau - addr - MR)
  /// - MC = (1 or MC[i-1]) * (MD + 1 - mask)
  /// The final product is stored in x = MC[max_num_mems_accesses - 1]
  ///
  /// Input composition: 
  ///           Challenges                            Masks                              Vars                                   W3
  /// 0   1   2   3   4   5   6   7   |   0   1   2   3   4   5   6   7   |   0   1   2   3   4   5   6   7    |  0   1   2   3     4   5   6   7
  /// tau r  r^2  _   _   _   _   _   |   1   1   0   0   _   _   _   _   |   w   A0  V0  A1  V1  Z0  Z1 ...   |  v   x  pi   D  | MR  MD  MC  MR ...
  ///
  /// All memory accesses should be in the form (A0, V0, A1, V1, ...) at the front of the witnesses
  /// Mask is the unary representation of L
  /// There can be at most max_num_mems_accesses memory accesses
  pub fn gen_mem_extract_inst(num_vars: usize, max_num_mems_accesses: usize) -> (usize, usize, Instance) {
    let mem_extract_num_cons = 3 * max_num_mems_accesses + 2;
    let mem_extract_num_non_zero_entries = 7 * max_num_mems_accesses + 4;
  
    let mem_extract_inst = {
      let mut A_list = Vec::new();
      let mut B_list = Vec::new();
      let mut C_list = Vec::new();
  
      let V_tau = 0;
      let V_r = 1;
      let V_mask = |i: usize| num_vars + i;
      // Valid is now w
      let V_valid = 2 * num_vars;
      let V_cnst = V_valid;
      let V_addr = |i: usize| 2 * num_vars + 1 + 2 * i;
      let V_val = |i: usize| 2 * num_vars + 2 + 2 * i;
      let V_v = 3 * num_vars;
      let V_x = 3 * num_vars + 1;
      let V_MR = |i: usize| 3 * num_vars + 4 + 3 * i;
      let V_MD = |i: usize| 3 * num_vars + 5 + 3 * i;
      let V_MC = |i: usize| 3 * num_vars + 6 + 3 * i;

      let (A, B, C) = {
        let mut A: Vec<(usize, usize, [u8; 32])> = Vec::new();
        let mut B: Vec<(usize, usize, [u8; 32])> = Vec::new();
        let mut C: Vec<(usize, usize, [u8; 32])> = Vec::new();
  
        let mut counter = 0;
        // v
        (A, B, C) = Instance::gen_constr(A, B, C,
          counter, vec![], vec![], vec![(V_valid, 1), (V_v, -1)]);
        counter += 1;
        // x
        (A, B, C) = Instance::gen_constr(A, B, C,
          counter, vec![], vec![], vec![(V_x, 1), (V_MC(max_num_mems_accesses - 1), -1)]);
        counter += 1;
        // MR, MD, MC
        for i in 0..max_num_mems_accesses {
          // MR = r * val
          (A, B, C) = Instance::gen_constr(A, B, C,
            counter, vec![(V_r, 1)], vec![(V_val(i), 1)], vec![(V_MR(i), 1)]);
          counter += 1;
          // MD = mask * (tau - addr - MR)
          (A, B, C) = Instance::gen_constr(A, B, C,
            counter, vec![(V_mask(i), 1)], vec![(V_tau, 1), (V_addr(i), -1), (V_MR(i), -1)], vec![(V_MD(i), 1)]);
          counter += 1;  
          // MC = (1 or MC[i-1]) * (MD + 1 - mask)
          if i == 0 {
            (A, B, C) = Instance::gen_constr(A, B, C,
              counter, vec![(V_valid, 1)], vec![(V_MD(i), 1), (V_cnst, 1), (V_mask(i), -1)], vec![(V_MC(i), 1)]);
          } else {
            (A, B, C) = Instance::gen_constr(A, B, C,
              counter, vec![(V_MC(i - 1), 1)], vec![(V_MD(i), 1), (V_cnst, 1), (V_mask(i), -1)], vec![(V_MC(i), 1)]);
          }
          counter += 1;
        }
        (A, B, C)
      };
      A_list.push(A);
      B_list.push(B);
      C_list.push(C);
  
      let mem_extract_inst = Instance::new(1, mem_extract_num_cons, 4 * num_vars, &A_list, &B_list, &C_list).unwrap();
      
      mem_extract_inst
    };
    (mem_extract_num_cons, mem_extract_num_non_zero_entries, mem_extract_inst)
  }

  /// Generates PHY_MEM_COHERE instance based on parameters
  /// PHY_MEM_COHERE takes in addr_mem = <v, D, addr, val>
  /// and verifies that
  /// 1. (v[k] - 1) * v[k + 1] = 0: if the current entry is invalid, the next entry is also invalid
  /// 2. v[k + 1] * (1 - (addr[k + 1] - addr[k])) * (addr[k + 1] - addr[k]) = 0: address difference is 0 or 1, unless the next entry is invalid
  /// 3. v[k + 1] * (1 - (addr[k + 1] - addr[k])) * (val[k + 1] - val[k]) = 0: either address difference is 1, or value are the same, unless the next entry is invalid
  /// So we set D = v[k + 1] * (1 - addr[k + 1] + addr[k])
  /// 
  /// Input composition:
  ///     Op[k]           Op[k + 1]
  /// 0   1   2   3  |  4   5   6   7
  /// v   D addr val |  v   D addr val
  pub fn gen_phy_mem_cohere_inst() -> (usize, usize, Instance) {
    let phy_mem_cohere_num_cons = 4;
    let phy_mem_cohere_num_non_zero_entries = 8;
  
    let phy_mem_cohere_inst = {
      let V_valid = 0;
      let V_cnst = V_valid;
      let V_D = 1;
      let V_addr = 2;
      let V_val = 3;
      let width = 4;
  
      let mut A_list = Vec::new();
      let mut B_list = Vec::new();
      let mut C_list = Vec::new();
      
      let (A, B, C) = {
        let mut A: Vec<(usize, usize, [u8; 32])> = Vec::new();
        let mut B: Vec<(usize, usize, [u8; 32])> = Vec::new();
        let mut C: Vec<(usize, usize, [u8; 32])> = Vec::new();
  
        let mut num_cons = 0;
        // (v[k] - 1) * v[k + 1] = 0
        (A, B, C) = Instance::gen_constr(A, B, C,
          num_cons, vec![(V_valid, 1), (V_cnst, -1)], vec![(width + V_valid, 1)], vec![]);
        num_cons += 1;
        // v[k + 1] * (1 - addr[k + 1] + addr[k]) = D[k]
        (A, B, C) = Instance::gen_constr(A, B, C,
          num_cons, vec![(width + V_valid, 1)], vec![(V_cnst, 1), (width + V_addr, -1), (V_addr, 1)], vec![(V_D, 1)]);
        num_cons += 1;
        // D[k] * (addr[k + 1] - addr[k]) = 0
        (A, B, C) = Instance::gen_constr(A, B, C,
          num_cons, vec![(V_D, 1)], vec![(width + V_addr, 1), (V_addr, -1)], vec![]);
        num_cons += 1;
        // D[k] * (val[k + 1] - val[k]) = 0
        (A, B, C) = Instance::gen_constr(A, B, C,
          num_cons, vec![(V_D, 1)], vec![(width + V_val, 1), (V_val, -1)], vec![]);
        
        (A, B, C)
      };
      A_list.push(A);
      B_list.push(B);
      C_list.push(C);
  
      let phy_mem_cohere_inst = Instance::new(1, phy_mem_cohere_num_cons, 2 * width, &A_list, &B_list, &C_list).unwrap();
      
      phy_mem_cohere_inst
    };
    (phy_mem_cohere_num_cons, phy_mem_cohere_num_non_zero_entries, phy_mem_cohere_inst)
  }

  /// Generates VIR_MEM_COHERE instance based on parameters
  /// VIR_MEM_COHERE takes in addr_mem = <v, D1, phy_addr, vir_addr, data, ls, ts, _> (need to keep the last entry 0 for permutation)
  /// and verifies that
  /// 1. (v[k] - 1) * v[k + 1] = 0: if the current entry is invalid, the next entry is also invalid
  /// 2. v[k + 1] * (1 - (phy_addr[k + 1] - phy_addr[k])) * (phy_addr[k + 1] - phy_addr[k]) = 0: phy addr difference is 0 or 1, unless the next entry is invalid
  /// 3. v[k + 1] * (1 - (phy_addr[k + 1] - phy_addr[k])) * (vir_addr[k + 1] - vir_addr[k]) * vir_addr[k + 1] = 0: either phy addr difference is 1, or vir addr are the same, or next vir addr is 0
  /// 4. v[k + 1] * (1 - (phy_addr[k + 1] - phy_addr[k])) * (data[k + 1] - data[k]) = 0: either phy addr difference is 1, or data are the same
  /// 5. v[k + 1] * (1 - (phy_addr[k + 1] - phy_addr[k])) * C_>=(ts[k + 1], ts[k]) = 0: either phy addr difference is 1, or ts is increasing
  /// 6. v[k + 1] * (phy_addr[k + 1] - phy_addr[k]) * (1 - ls[k + 1]) = 0: either phy addr are the same, or next op is STORE
  /// So we set D1 = v[k + 1] * (1 - phy_addr[k + 1] + phy_addr[k])
  ///           D2 = v[k + 1] * (phy_addr[k + 1] - phy_addr[k])
  ///           D3 = D1 * (vir_addr[k + 1] - vir_addr[k])
  ///           D4 = D1 * (ts[k + 1] - ts[k])
  /// Input composition:
  ///             Op[k]                           Op[k + 1]              D2, D3, D4 & bits of ts[k + 1] - ts[k]
  /// 0   1   2   3   4   5   6   7  |  0   1   2   3   4   5   6   7  |  0   1   2   3   4   5
  /// v  D1  pa  va data ls  ts   _  |  v  D1  pa  va data ls  ts   _  | D2  D3  D4  EQ  B0  B1  ...
  pub fn gen_vir_mem_cohere_inst(max_ts_width: usize, mem_addr_ts_bits_size: usize) -> (usize, usize, usize, Instance) {
    let vir_mem_cohere_num_vars = max(2 * 8, mem_addr_ts_bits_size) / 2;
    let width = vir_mem_cohere_num_vars;
    let vir_mem_cohere_num_cons = max_ts_width + 11;
    let vir_mem_cohere_num_non_zero_entries = max(16 + max_ts_width, 6 + 2 * max_ts_width);
  
    let vir_mem_cohere_inst = {
      let V_valid = 0;
      let V_cnst = V_valid;
      let V_D1 = 1;
      let V_pa = 2;
      let V_va = 3;
      let V_data = 4;
      let V_ls = 5;
      let V_ts = 6;
      let V_D2 = 2 * width;
      let V_D3 = 2 * width + 1;
      let V_D4 = 2 * width + 2;
      let V_EQ = 2 * width + 3;
      let V_B = |i| 2 * width + 4 + i;
  
      let mut A_list = Vec::new();
      let mut B_list = Vec::new();
      let mut C_list = Vec::new();
      
      let (A, B, C) = {
        let mut A: Vec<(usize, usize, [u8; 32])> = Vec::new();
        let mut B: Vec<(usize, usize, [u8; 32])> = Vec::new();
        let mut C: Vec<(usize, usize, [u8; 32])> = Vec::new();
  
        let mut num_cons = 0;
        // (v[k] - 1) * v[k + 1] = 0
        (A, B, C) = Instance::gen_constr(A, B, C,
          num_cons, vec![(V_valid, 1), (V_cnst, -1)], vec![(width + V_valid, 1)], vec![]);
        num_cons += 1;
        // D1[k] = v[k + 1] * (1 - pa[k + 1] + pa[k])
        (A, B, C) = Instance::gen_constr(A, B, C,
          num_cons, vec![(width + V_valid, 1)], vec![(V_cnst, 1), (width + V_pa, -1), (V_pa, 1)], vec![(V_D1, 1)]);
        num_cons += 1;
        // D2[k] = v[k + 1] * (pa[k + 1] - pa[k])
        (A, B, C) = Instance::gen_constr(A, B, C,
          num_cons, vec![(width + V_valid, 1)], vec![(width + V_pa, 1), (V_pa, -1)], vec![(V_D2, 1)]);
        num_cons += 1;
        // D3[k] = D1[k] * (vir_addr[k + 1] - vir_addr[k])
        (A, B, C) = Instance::gen_constr(A, B, C,
          num_cons, vec![(V_D1, 1)], vec![(width + V_va, 1), (V_va, -1)], vec![(V_D3, 1)]);
        num_cons += 1;
        // D4[k] = D1[k] * (ts[k + 1] - ts[k])
        (A, B, C) = Instance::gen_constr(A, B, C,
          num_cons, vec![(V_D1, 1)], vec![(width + V_ts, 1), (V_ts, -1)], vec![(V_D4, 1)]);
        num_cons += 1;
        // D1[k] * (pa[k + 1] - pa[k]) = 0
        (A, B, C) = Instance::gen_constr(A, B, C,
          num_cons, vec![(V_D1, 1)], vec![(width + V_pa, 1), (V_pa, -1)], vec![]);
        num_cons += 1;
        // D3[k] * va[k + 1] = 0
        (A, B, C) = Instance::gen_constr(A, B, C,
          num_cons, vec![(V_D3, 1)], vec![(width + V_va, 1)], vec![]);
        num_cons += 1;
        // D1[k] * (data[k + 1] - data[k]) = 0
        (A, B, C) = Instance::gen_constr(A, B, C,
          num_cons, vec![(V_D1, 1)], vec![(width + V_data, 1), (V_data, -1)], vec![]);
        num_cons += 1;
        // D2[k] * (1 - ls[k + 1]) = 0
        (A, B, C) = Instance::gen_constr(A, B, C,
          num_cons, vec![(V_D2, 1)], vec![(V_cnst, 1), (width + V_ls, -1)], vec![]);
        num_cons += 1;
        // EQ
        (A, B, C) = Instance::gen_constr(A, B, C,
          num_cons, vec![(V_EQ, 1)], vec![(V_EQ, 1)], vec![(V_EQ, 1)]);
        num_cons += 1;
        // Bits of D4 - EQ
        for i in 0..max_ts_width {
          // Bi * Bi = Bi
          (A, B, C) = Instance::gen_constr(A, B, C,
            num_cons, vec![(V_B(i), 1)], vec![(V_B(i), 1)], vec![(V_B(i), 1)]);
          num_cons += 1;
        }
        // 0 = D4 - EQ - \Sum_i B_i
        (A, B, C) = Instance::gen_constr(A, B, C,
          num_cons, vec![], vec![], [vec![(V_D4, 1), (V_EQ, -1)], (0..max_ts_width).map(|i| (V_B(i), -1 * (i.pow2() as isize))).collect()].concat()
        );
        
        (A, B, C)
      };
      A_list.push(A);
      B_list.push(B);
      C_list.push(C);
  
      let vir_mem_cohere_inst = Instance::new(1, vir_mem_cohere_num_cons, 4 * vir_mem_cohere_num_vars, &A_list, &B_list, &C_list).unwrap();
      
      vir_mem_cohere_inst
    };
    (vir_mem_cohere_num_vars, vir_mem_cohere_num_cons, vir_mem_cohere_num_non_zero_entries, vir_mem_cohere_inst)
  }


  /*
  /// Checks if a given R1CSInstance is satisfiable with a given variables and inputs assignments
  pub fn is_sat(
    &self,
    vars: &VarsAssignment,
    inputs: &InputsAssignment,
  ) -> Result<bool, R1CSError> {
    if vars.assignment.len() > self.inst.get_num_vars() {
      return Err(R1CSError::InvalidNumberOfInputs);
    }

    if inputs.assignment.len() != self.inst.get_num_inputs() {
      return Err(R1CSError::InvalidNumberOfInputs);
    }

    // we might need to pad variables
    let padded_vars = {
      let num_padded_vars = self.inst.get_num_vars();
      let num_vars = vars.assignment.len();
      if num_padded_vars > num_vars {
        vars.pad(num_padded_vars)
      } else {
        vars.clone()
      }
    };

    Ok(
      self
        .inst
        .is_sat(&padded_vars.assignment, &inputs.assignment),
    )
  }
  */

  /*
  /// Constructs a new synthetic R1CS `Instance` and an associated satisfying assignment
  pub fn produce_synthetic_r1cs(
    num_cons: usize,
    num_vars: usize,
    num_inputs: usize,
  ) -> (Instance, VarsAssignment, InputsAssignment) {
    let (inst, vars, inputs) = R1CSInstance::produce_synthetic_r1cs(num_cons, num_vars, num_inputs);
    let digest = inst.get_digest();
    (
      Instance { inst, digest },
      VarsAssignment { assignment: vars },
      InputsAssignment { assignment: inputs },
    )
  }
  */
}
