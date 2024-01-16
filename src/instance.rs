use std::cmp::max;

use crate::R1CSInstance;
use crate::errors::R1CSError;
use crate::scalar::Scalar;

/// `Instance` holds the description of R1CS matrices and a hash of the matrices
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
    let num_instances_padded = num_instances.next_power_of_two();
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
      num_instances_padded,
      num_cons_padded,
      num_vars_padded,
      &A_scalar_list,
      &B_scalar_list,
      &C_scalar_list,
    );

    let digest = inst.get_digest();

    Ok(Instance { inst, digest })
  }

  /// Generates a constraints based on supplied (variable, constant) pairs
  pub fn gen_constr(
    mut A: Vec<(usize, usize, [u8; 32])>, mut B: Vec<(usize, usize, [u8; 32])>, mut C: Vec<(usize, usize, [u8; 32])>,
    i: usize, args_A: Vec<(usize, isize)>, args_B: Vec<(usize, isize)>, args_C: Vec<(usize, isize)>) -> (
      Vec<(usize, usize, [u8; 32])>, Vec<(usize, usize, [u8; 32])>, Vec<(usize, usize, [u8; 32])>
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
  
  /// Generates BLOCK instances based on inputs
  pub fn gen_block_inst(
    num_instances: usize, 
    num_vars: usize, 
    args: &Vec<Vec<(Vec<(usize, isize)>, Vec<(usize, isize)>, Vec<(usize, isize)>)>>,
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
          (A, B, C) = Instance::gen_constr(A, B, C,
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

  /// Generates CONSIS_COMB instance based on parameters
  /// CONSIS_COMB takes in 4 witness lists as inputs:
  /// - perm_w0: <tau, r, r^2, r^3, ...>, see PERM_PRELIM below
  /// - exec_inputs: <v, i0, i1, i2, ..., cnst, o0, o1, o2, ...>
  /// - consis_w2: <0, i0 * r, i1 * r^2, ..., 0, o0 * r, o1 * r^2, ...>
  /// - consis_w3: <v, v * (cnst + i0 * r + i1 * r^2 + i2 * r^3 + ...), v * (cnst + o0 * r + o1 * r^2 + o2 * r^3 + ...), 0, 0, ...>
  /// Note: if v is 1, it is almost impossible to have consis_w3[1] = 0
  pub fn gen_consis_comb_inst(num_vars: usize) -> (usize, usize, Instance) {
    assert_eq!(num_vars, num_vars.next_power_of_two());
    let num_inputs = num_vars / 2;

    let consis_comb_num_cons = num_vars + 1;
    let consis_comb_num_non_zero_entries = 2 * num_vars - 1;
  
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
        for i in 1..num_inputs {
          // Dot product for inputs
          (A, B, C) = Instance::gen_constr(A, B, C,
            constraint_count, vec![(i, 1)], vec![(num_vars + i, 1)], vec![(2 * num_vars + i, 1)]);
          constraint_count += 1;
          // Dot product for outputs
          (A, B, C) = Instance::gen_constr(A, B, C,
            constraint_count, vec![(i, 1)], vec![(num_vars + num_inputs + i, 1)], vec![(2 * num_vars + num_inputs + i, 1)]);
          constraint_count += 1;
        }
        // For w3
        (A, B, C) = Instance::gen_constr(A, B, C, // w3[0]
          constraint_count, vec![], vec![], vec![(V_valid, 1), (3 * num_vars, -1)]);
        constraint_count += 1;
        (A, B, C) = Instance::gen_constr(A, B, C, // w3[1]
          constraint_count, 
          vec![(V_valid, 1)], 
          [vec![(V_cnst, 1)], (1..num_inputs).map(|i| (2 * num_vars + i, 1)).collect()].concat(),
          vec![(3 * num_vars + 1, 1)]
        );
        constraint_count += 1;
        (A, B, C) = Instance::gen_constr(A, B, C, // w3[2]
          constraint_count, 
          vec![(V_valid, 1)], 
          [vec![(V_cnst, 1)], (1..num_inputs).map(|i| (2 * num_vars + num_inputs + i, 1)).collect()].concat(),
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
    (consis_comb_num_cons, consis_comb_num_non_zero_entries, consis_comb_inst)
  }

  /// Generates CONSIS_CHECK instance based on parameters
  /// CONSIS_CHECK takes in consis_w3 = <v, i, o, 0, 0, ...>
  /// and verifies (o[k] - i[k + 1]) * v[k + 1] = 0 for all k
  pub fn gen_consis_check_inst(num_vars: usize, total_num_proofs_bound: usize) -> (usize, usize, Instance) {
    let consis_check_num_cons_base = 1;
    let consis_check_num_non_zero_entries = 2 * total_num_proofs_bound;
    let consis_check_num_cons = consis_check_num_cons_base * total_num_proofs_bound;
  
    let V_valid = 0;
    let V_cnst = V_valid;
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
          (A, B, C) = Instance::gen_constr(A, B, C,
            i, vec![(i * num_vars + V_o, 1), ((i + 1) * num_vars + V_i, -1)], vec![((i + 1) * num_vars + V_valid, 1)], vec![]);
        }
        // Pad A, B, C with dummy entries so their size is multiple of total_num_proofs_bound
        (A, B, C) = Instance::gen_constr(A, B, C,
          total_num_proofs_bound - 1, vec![(V_cnst, 0); 2], vec![(V_cnst, 0)], vec![]);
        (A, B, C)
      };
      A_list.push(A);
      B_list.push(B);
      C_list.push(C);
  
      let consis_check_inst = Instance::new(1, consis_check_num_cons, total_num_proofs_bound * num_vars, &A_list, &B_list, &C_list).unwrap();
      
      consis_check_inst
    };
    (consis_check_num_cons_base, consis_check_num_non_zero_entries, consis_check_inst)
  }

  /// Generates PERM_PRELIM instance based on parameters
  /// PERM_PRELIM checks the correctness of (r, r^2, ...)
  pub fn gen_perm_prelim_inst(num_vars: usize) -> (usize, usize, Instance) {
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
          (A, B, C) = Instance::gen_constr(A, B, C,
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
    (perm_prelim_num_cons, perm_prelim_num_non_zero_entries, perm_prelim_inst)
  }

  /// Generates PERM_ROOT instance based on parameters
  /// Witnesses of PERM_ROOT is consisted of [w0, w1, w2, w3], each of size num_vars
  /// w0: tau, r, r^2, ...
  /// w1: one block_inputs entry: i0, i1, ...
  /// w2: one block_inputs entry dot product <r>: i0, i1 * r, i2 * r^2, i3 * r^3, ...
  /// w3[0]: valid bit, should match block_inputs[0]
  /// w3[1]: one root of the polynomial: (tau - (i0 + i1 * r + i2 * r^2 - ...)), 0 if invalid
  pub fn gen_perm_root_inst(num_vars: usize) -> (usize, usize, Instance) {
    let perm_root_num_cons = num_vars + 2;
    let perm_root_num_non_zero_entries = 2 * num_vars + 2;
    let perm_root_inst = {
      let (A, B, C) = {
        let mut A: Vec<(usize, usize, [u8; 32])> = Vec::new();
        let mut B: Vec<(usize, usize, [u8; 32])> = Vec::new();
        let mut C: Vec<(usize, usize, [u8; 32])> = Vec::new();
  
        let V_tau = 0;
        let mut constraint_count = 0;
  
        // correctness of w2
        (A, B, C) = Instance::gen_constr(A, B, C, // for i0
          constraint_count, vec![], vec![], vec![(num_vars, 1), (2 * num_vars, -1)]);
        constraint_count += 1;
        for i in 1..num_vars {
          (A, B, C) = Instance::gen_constr(A, B, C, // for i1..
            constraint_count, vec![(num_vars + i, 1)], vec![(i, 1)], vec![(2 * num_vars + i, 1)]);
          constraint_count += 1;
        }
        // correctness of w3[0]
        (A, B, C) = Instance::gen_constr(A, B, C, 
          constraint_count, vec![], vec![], vec![(num_vars, 1), (3 * num_vars, -1)]);
        constraint_count += 1;
        // correctness of w3[1]
        (A, B, C) = Instance::gen_constr(A, B, C, constraint_count,
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
    (perm_root_num_cons, perm_root_num_non_zero_entries, perm_root_inst)
  }

  /// Generates PERM_POLY instance based on parameters
  /// The strategy is to compute the local polynomials (evaluated on tau) for each block instance
  /// Each w3[p][2] (i.e. w3[p][0][2]) stores the product pi for instance P. The verifier obtains all P of them and multiply them together.
  /// The correct formular is pi = v[k] * x[k] * (pi[k+1] + (1 - v[k+1])))
  /// To do this, think of each entry of w3[k] (w3[p][k]) as a tuple (v, x, pi, D)
  /// v[k]  <- whether the entry is valid
  /// x[k]  <- \tau - (\sum_i a_i * r^{i-1})
  /// pi[k] <- v[k] * D[k]
  /// D[k] <- x[k] * (pi[k + 1] + (1 - v[k + 1]))
  /// number of variables is total_num_proofs_bound * num_vars
  pub fn gen_perm_poly_inst(num_vars: usize, total_num_proofs_bound: usize) -> (usize, usize, Instance) {
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
          (A, B, C) = Instance::gen_constr(A, B, C,
            constraint_count, 
            vec![(i * num_vars + V_x, 1)], 
            vec![((i + 1) * num_vars + V_pi, 1), (i * num_vars + V_cnst, 1), ((i + 1) * num_vars + V_valid, -1)], 
            vec![(i * num_vars + V_d, 1)]);
          constraint_count += 1;
          // pi[k] = v[k] * D[k]
          (A, B, C) = Instance::gen_constr(A, B, C,
            constraint_count, vec![(i * num_vars + V_valid, 1)], vec![(i * num_vars + V_d, 1)], vec![(i * num_vars + V_pi, 1)]);
          // Pad base constraint size to 2
          constraint_count += 1;
        }
        // Last Entry
        // Pad A, B, C with dummy entries so their size is multiple of perm_size_bound
        let i = perm_size_bound - 1;
        // last D is x[k] * 1
        (A, B, C) = Instance::gen_constr(A, B, C,
          constraint_count, vec![(i * num_vars + V_x, 1)], vec![(V_cnst, 1), (V_cnst, 0), (V_cnst, 0)], vec![(i * num_vars + V_d, 1)]);
        constraint_count += 1;
        // last pi is just usual
        (A, B, C) = Instance::gen_constr(A, B, C,
          constraint_count, vec![(i * num_vars + V_valid, 1)], vec![(i * num_vars + V_d, 1)], vec![(i * num_vars + V_pi, 1)]);

        (A, B, C)   
      };

      let A_list = vec![A.clone()];
      let B_list = vec![B.clone()];
      let C_list = vec![C.clone()];

      let perm_poly_inst = Instance::new(1, perm_poly_num_cons, perm_size_bound * num_vars, &A_list, &B_list, &C_list).unwrap();
      
      perm_poly_inst
    };
    (perm_poly_num_cons_base, perm_poly_num_non_zero_entries, perm_poly_inst)
  }

  /// Generates MEM_EXTRACT instance based on parameters
  /// MR is r * val for each (addr, val)
  /// MC is the cumulative product of v * (tau - addr - MR)
  /// The final product is stored in x
  /// 0   1   2   3   4   5   6   7    0   1   2   3   4   5   6   7
  /// tau r   _   _   _   _   _   _ |  w  A0  A1  V0  V1  Z0  Z1  B0
  /// 0   1   2   3     4   5   6   7  |  _   _   _  
  /// v   x  pi   D  | MR  MC  MR  MC  |  _   _   _  ...
  /// All memory accesses should be in the form (A0, V0, A1, V1, ...) at the front of the witnesses
  /// Input `num_mems_accesses` indicates how many memory accesses are there for each block
  pub fn gen_mem_extract_inst(num_instances: usize, num_vars: usize, num_mems_accesses: &Vec<usize>) -> (usize, usize, Instance) {
    assert_eq!(num_instances, num_mems_accesses.len());
    
    let mut mem_extract_num_cons = 0;
    let mut mem_extract_num_non_zero_entries = 0;
  
    let mem_extract_inst = {
      let mut A_list = Vec::new();
      let mut B_list = Vec::new();
      let mut C_list = Vec::new();
  
      let V_tau = 0;
      let V_r = 1;
      // Valid is now w
      let V_valid = num_vars;
      let V_addr = |i: usize| num_vars + 1 + i;
      let V_val = |b: usize, i: usize| num_vars + 1 + num_mems_accesses[b] + i;
      let V_v = 2 * num_vars;
      let V_x = 2 * num_vars + 1;
      let V_MR = |i: usize| 2 * num_vars + 4 + 2 * i;
      let V_MC = |i: usize| 2 * num_vars + 5 + 2 * i;
  
      for b in 0..num_instances {
        mem_extract_num_cons = max(mem_extract_num_cons, 2 * num_mems_accesses[b] + 2);
        mem_extract_num_non_zero_entries = max(mem_extract_num_non_zero_entries, 4 * num_mems_accesses[b] + 4);

        let (A, B, C) = {
          let mut A: Vec<(usize, usize, [u8; 32])> = Vec::new();
          let mut B: Vec<(usize, usize, [u8; 32])> = Vec::new();
          let mut C: Vec<(usize, usize, [u8; 32])> = Vec::new();
    
          // w3[0]
          (A, B, C) = Instance::gen_constr(A, B, C,
            2 * num_mems_accesses[b], vec![], vec![], vec![(V_valid, 1), (V_v, -1)]);
          // w3[1]
          // If the block contains no memory accesses, then set V_x to 1
          if num_mems_accesses[b] == 0 {
            (A, B, C) = Instance::gen_constr(A, B, C,
              2 * num_mems_accesses[b] + 1, vec![], vec![], vec![(V_x, 1), (V_v, -1)]);
          } else {
            for i in 0..num_mems_accesses[b] {
              // addr = A0, val = V0
              (A, B, C) = Instance::gen_constr(A, B, C,
                2 * i, vec![(V_r, 1)], vec![(V_val(b, i), 1)], vec![(V_MR(i), 1)]);
              if i == 0 {
                (A, B, C) = Instance::gen_constr(A, B, C,
                  1, vec![(V_valid, 1)], vec![(V_tau, 1), (V_addr(i), -1), (V_MR(i), -1)], vec![(V_MC(i), 1)]);
              } else {
                (A, B, C) = Instance::gen_constr(A, B, C,
                  2 * i + 1, vec![(V_MC(i - 1), 1)], vec![(V_tau, 1), (V_addr(i), -1), (V_MR(i), -1)], vec![(V_MC(i), 1)]);
              }
            }
            // w3[1]
            (A, B, C) = Instance::gen_constr(A, B, C,
              2 * num_mems_accesses[b] + 1, vec![], vec![], vec![(V_x, 1), (V_MC(num_mems_accesses[b] - 1), -1)]);
            }
          (A, B, C)
        };
        A_list.push(A);
        B_list.push(B);
        C_list.push(C);
      }
  
      let mem_extract_inst = Instance::new(num_instances, mem_extract_num_cons, 4 * num_vars, &A_list, &B_list, &C_list).unwrap();
      
      mem_extract_inst
    };
    (mem_extract_num_cons, mem_extract_num_non_zero_entries, mem_extract_inst)
  }

  /// Generates MEM_COHERE instance based on parameters
  /// MEM_COHERE takes in addr_mem = <v, addr, val, D>
  /// and verifies that
  /// 1. (v[k] - 1) * v[k + 1] = 0: if the current entry is invalid, the next entry is also invalid
  /// 2. v[k + 1] * (addr[k + 1] - addr[k] - 1) * (addr[k + 1] - addr[k]) = 0: address difference is 0 or 1, unless the next entry is invalid
  /// 3. v[k + 1] * (addr[k + 1] - addr[k] - 1) * (val[k + 1] - val[k]) = 0: either address difference is 1, or value are the same, unless the next entry is invalid
  /// So we set D = v[k + 1] * (addr[k + 1] - addr[k] - 1)
  pub fn gen_mem_cohere_inst(total_num_mem_accesses_bound: usize) -> (usize, usize, Instance) {
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
          (A, B, C) = Instance::gen_constr(A, B, C,
            num_cons, vec![(i * width + V_valid, 1), (i * width + V_cnst, -1)], vec![((i + 1) * width + V_valid, 1)], vec![]);
          num_cons += 1;
          // v[k + 1] * (addr[k + 1] - addr[k] - 1) = D[k]
          (A, B, C) = Instance::gen_constr(A, B, C,
            num_cons, vec![((i + 1) * width + V_valid, 1)], vec![((i + 1) * width + V_addr, 1), (i * width + V_addr, -1), (i * width + V_cnst, -1)], vec![(i * width + V_D, 1)]);
          num_cons += 1;
          // D[k] * (addr[k + 1] - addr[k]) = 0
          (A, B, C) = Instance::gen_constr(A, B, C,
            num_cons, vec![(i * width + V_D, 1)], vec![((i + 1) * width + V_addr, 1), (i * width + V_addr, -1)], vec![]);
          num_cons += 1;
          // D[k] * (val[k + 1] - val[k]) = 0
          (A, B, C) = Instance::gen_constr(A, B, C,
            num_cons, vec![(i * width + V_D, 1)], vec![((i + 1) * width + V_val, 1), (i * width + V_val, -1)], vec![]);
          num_cons += 1;
        }
        // Pad A, B, C with dummy entries so their size is multiple of total_num_mem_accesses_bound
        (A, B, C) = Instance::gen_constr(A, B, C,
          num_cons, vec![(V_cnst, 0); 2], vec![(V_cnst, 0)], vec![]);
        num_cons += 1;
        (A, B, C) = Instance::gen_constr(A, B, C,
          num_cons, vec![(V_cnst, 0)], vec![(V_cnst, 0); 3], vec![(V_cnst, 0)]);
        num_cons += 1;
        (A, B, C) = Instance::gen_constr(A, B, C,
          num_cons, vec![(V_cnst, 0)], vec![(V_cnst, 0); 2], vec![(V_cnst, 0)]);
        num_cons += 1;
        (A, B, C) = Instance::gen_constr(A, B, C,
          num_cons, vec![(V_cnst, 0)], vec![(V_cnst, 0); 2], vec![(V_cnst, 0)]);
        (A, B, C)
      };
      A_list.push(A);
      B_list.push(B);
      C_list.push(C);
  
      let mem_cohere_inst = Instance::new(1, mem_cohere_num_cons, total_num_mem_accesses_bound * width, &A_list, &B_list, &C_list).unwrap();
      
      mem_cohere_inst
    };
    (mem_cohere_num_cons_base, mem_cohere_num_non_zero_entries, mem_cohere_inst)
  }

  /// Generates MEM_ADDR_COMB instance based on parameters
  /// MEM_ADDR_COMB converts (v, addr, val, _) to (v, x, pi, D)
  pub fn gen_mem_addr_comb_inst() -> (usize, usize, Instance) {
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
        (A, B, C) = Instance::gen_constr(A, B, C,
          0, vec![(V_r, 1)], vec![(V_val, 1)], vec![(V_MR, 1)]);
        // w1[0] = v
        (A, B, C) = Instance::gen_constr(A, B, C,
          1, vec![], vec![], vec![(V_v, 1), (V_valid, -1)]);
        // w1[1] = x = v * (tau - addr - MR)
        (A, B, C) = Instance::gen_constr(A, B, C,
          2, vec![(V_v, 1)], vec![(V_tau, 1), (V_addr, -1), (V_MR, -1)], vec![(V_x, 1)]);
        (A, B, C)
      };

      A_list.push(A);
      B_list.push(B);
      C_list.push(C);

      let mem_addr_comb_inst = Instance::new(1, mem_addr_comb_num_cons, 4 * width, &A_list, &B_list, &C_list).unwrap();
      mem_addr_comb_inst
    };
    (mem_addr_comb_num_cons, mem_addr_comb_num_non_zero_entries, mem_addr_comb_inst)
  }

  /// Generates MEM_ADDR_POLY instance based on parameters
  /// MEM_ADDR_POLY is like PERM_POLY except number of variables is total_num_mem_accesses_bound and gap is 4
  pub fn gen_mem_addr_poly_inst(total_num_mem_accesses_bound: usize) -> (usize, usize, Instance) {
    let mem_addr_poly_num_cons_base = 2;
    let mem_addr_poly_num_cons = total_num_mem_accesses_bound * mem_addr_poly_num_cons_base;
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
          (A, B, C) = Instance::gen_constr(A, B, C,
            constraint_count, 
            vec![(i * width + V_x, 1)], 
            vec![((i + 1) * width + V_pi, 1), (i * width + V_cnst, 1), ((i + 1) * width + V_valid, -1)], 
            vec![(i * width + V_d, 1)]);
          constraint_count += 1;
          // pi[k] = v[k] * D[k]
          (A, B, C) = Instance::gen_constr(A, B, C,
            constraint_count, vec![(i * width + V_valid, 1)], vec![(i * width + V_d, 1)], vec![(i * width + V_pi, 1)]);
          // Pad base constraint size to 2
          constraint_count += 1;
        }
        // Last Entry
        // Pad A, B, C with dummy entries so their size is multiple of total_num_mem_accesses_bound
        let i = total_num_mem_accesses_bound - 1;
        // last D is x[k] * 1
        (A, B, C) = Instance::gen_constr(A, B, C,
          constraint_count, vec![(i * width + V_x, 1)], vec![(V_cnst, 1), (V_cnst, 0), (V_cnst, 0)], vec![(i * width + V_d, 1)]);
        constraint_count += 1;
        // last pi is just usual
        (A, B, C) = Instance::gen_constr(A, B, C,
          constraint_count, vec![(i * width + V_valid, 1)], vec![(i * width + V_d, 1)], vec![(i * width + V_pi, 1)]);

        (A, B, C)   
      };

      let A_list = vec![A.clone()];
      let B_list = vec![B.clone()];
      let C_list = vec![C.clone()];

      let mem_addr_poly_inst = Instance::new(1, mem_addr_poly_num_cons, total_num_mem_accesses_bound * width, &A_list, &B_list, &C_list).unwrap();
      
      mem_addr_poly_inst
    };
    (mem_addr_poly_num_cons_base, mem_addr_poly_num_non_zero_entries, mem_addr_poly_inst)
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