//! Reads in constraints and inputs from zok_tests/constraints and zok_tests/inputs
//! Used as a temporary interface to / from CirC
#![allow(clippy::assertions_on_result_states)]
use std::{cmp::max, fs::File, io::BufReader};
use std::io::BufRead;

use libspartan::{instance::Instance, SNARKGens, VarsAssignment, SNARK, InputsAssignment, MemsAssignment};
use merlin::Transcript;

// Convert a string of numbers separated by spaces into a vector
fn string_to_vec(buffer: String) -> Vec<usize> {
  let split: Vec<String> = buffer.split(' ').map(|i| i.to_string().trim().to_string()).collect();
  let mut list = Vec::new();
  for s in split {
    if s != "" {
      list.push(s.parse::<usize>().unwrap());
    }
  }
  list
}

// Convert a string of bytes separated by spaces into a vector
fn string_to_bytes(buffer: String) -> [u8; 32] {
  let split: Vec<String> = buffer.split(' ').map(|i| i.to_string().trim().to_string()).collect();
  let mut list = [0; 32];
  for i in 0..32 {
    let s = &split[i];
    if s != "" {
      list[i] = s.parse::<u8>().unwrap();
    }
  }
  list
}

// Everything provided by the frontend
struct CompileTimeKnowledge {
  block_num_instances: usize,
  num_vars: usize,
  total_num_proofs_bound: usize,
  block_num_mem_accesses: Vec<usize>,
  total_num_mem_accesses_bound: usize,

  args: Vec<Vec<(Vec<(usize, isize)>, Vec<(usize, isize)>, Vec<(usize, isize)>)>>,

  func_input_width: usize,
  input_offset: usize,
  input_block_num: usize,
  output_offset: usize,
  output_block_num: usize
}

impl CompileTimeKnowledge {
  fn read_from_file(benchmark_name: String) -> std::io::Result<CompileTimeKnowledge> {
    let file_name = format!("../zok_tests/constraints/{}.ctk", benchmark_name);
    let f = File::open(file_name)?;
    let mut reader = BufReader::new(f);
    let mut buffer = String::new();

    let (block_num_instances, num_vars, total_num_proofs_bound, block_num_mem_accesses, total_num_mem_accesses_bound) = {
      reader.read_line(&mut buffer)?;
      let block_num_instances = buffer.trim().parse::<usize>().unwrap();
      buffer.clear();
      reader.read_line(&mut buffer)?;
      let num_vars = buffer.trim().parse::<usize>().unwrap();
      buffer.clear();
      reader.read_line(&mut buffer)?;
      let total_num_proofs_bound = buffer.trim().parse::<usize>().unwrap();
      buffer.clear();
      reader.read_line(&mut buffer)?;
      let block_num_mem_accesses: Vec<usize> = string_to_vec(buffer.clone());
      buffer.clear();
      reader.read_line(&mut buffer)?;
      let total_num_mem_accesses_bound = buffer.trim().parse::<usize>().unwrap();
      (block_num_instances, num_vars, total_num_proofs_bound, block_num_mem_accesses, total_num_mem_accesses_bound)
    };

    let mut args = vec![Vec::new(); block_num_instances];
    let mut inst_counter: usize = 0;
    let mut cons_counter: usize = 0;
    buffer.clear();
    reader.read_line(&mut buffer)?;
    assert_eq!(buffer, "INST 0\n".to_string());
    while buffer != format!("INST_END\n") {
      buffer.clear();
      reader.read_line(&mut buffer)?;
      if buffer == format!("INST {}\n", inst_counter + 1) {
        inst_counter += 1;
        cons_counter = 0;
      } else {
        let split: Vec<String> = buffer.split(' ').map(|i| i.to_string().trim().to_string()).collect();
        if split[0] == "A".to_string() {
          args[inst_counter].push((Vec::new(), Vec::new(), Vec::new()));
        }
        let mut var = 1;
        let mut val = 2;
        while val < split.len() {
          if split[0] == "A".to_string() {
            args[inst_counter][cons_counter].0.push((split[var].parse::<usize>().unwrap(), split[val].parse::<isize>().unwrap()));
          }
          if split[0] == "B".to_string() {
            args[inst_counter][cons_counter].1.push((split[var].parse::<usize>().unwrap(), split[val].parse::<isize>().unwrap()));
          }
          if split[0] == "C".to_string() {
            args[inst_counter][cons_counter].2.push((split[var].parse::<usize>().unwrap(), split[val].parse::<isize>().unwrap()));
          }
          var += 2;
          val += 2;
        }
        if split[0] == "C".to_string() {
          cons_counter += 1;
        }
      }
    }
    buffer.clear();
    reader.read_line(&mut buffer)?;
    let func_input_width = buffer.trim().parse::<usize>().unwrap();
    buffer.clear();
    reader.read_line(&mut buffer)?;
    let input_offset = buffer.trim().parse::<usize>().unwrap();
    buffer.clear();
    reader.read_line(&mut buffer)?;
    let input_block_num = buffer.trim().parse::<usize>().unwrap();
    buffer.clear();
    reader.read_line(&mut buffer)?;
    let output_offset = buffer.trim().parse::<usize>().unwrap();
    buffer.clear();
    reader.read_line(&mut buffer)?;
    let output_block_num = buffer.trim().parse::<usize>().unwrap();

    Ok(CompileTimeKnowledge {
      block_num_instances,
      num_vars,
      total_num_mem_accesses_bound,
      block_num_mem_accesses,
      total_num_proofs_bound,
      args,
      func_input_width,
      input_offset,
      input_block_num,
      output_offset,
      output_block_num
    })
  }
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
  output: [u8; 32],
  output_exec_num: usize
}

impl RunTimeKnowledge {
  fn read_from_file(benchmark_name: String) -> std::io::Result<RunTimeKnowledge> {
    let file_name = format!("../zok_tests/inputs/{}.rtk", benchmark_name);
    let f = File::open(file_name)?;
    let mut reader = BufReader::new(f);
    let mut buffer = String::new();

    let (block_max_num_proofs, block_num_proofs, consis_num_proofs, total_num_mem_accesses) = {
      reader.read_line(&mut buffer)?;
      let block_max_num_proofs = buffer.trim().parse::<usize>().unwrap();
      buffer.clear();
      reader.read_line(&mut buffer)?;
      let block_num_proofs = string_to_vec(buffer.clone());
      buffer.clear();
      reader.read_line(&mut buffer)?;
      let consis_num_proofs = buffer.trim().parse::<usize>().unwrap();
      buffer.clear();
      reader.read_line(&mut buffer)?;
      let total_num_mem_accesses = buffer.trim().parse::<usize>().unwrap();
      (block_max_num_proofs, block_num_proofs, consis_num_proofs, total_num_mem_accesses)
    };
    
    let block_vars_matrix: Vec<Vec<VarsAssignment>> = {
      let mut block_vars_matrix = vec![Vec::new()];
      buffer.clear();
      reader.read_line(&mut buffer)?;
      assert_eq!(buffer, "BLOCK_VARS\n".to_string());
      buffer.clear();
      reader.read_line(&mut buffer)?;
      assert_eq!(buffer, "BLOCK 0\n".to_string());

      let mut block_counter = 0;
      let mut exec_counter = 0;
      buffer.clear();
      reader.read_line(&mut buffer)?;
      while buffer != "BLOCK_INPUTS\n".to_string() {
        if buffer == format!("BLOCK {}\n", block_counter + 1) {
          block_counter += 1;
          exec_counter = 0;
          block_vars_matrix.push(Vec::new());
        } else if buffer == format!("EXEC 0\n") {
          block_vars_matrix[block_counter].push(Vec::new());
        } else if buffer == format!("EXEC {}\n", exec_counter + 1) {
          block_vars_matrix[block_counter].push(Vec::new());
          exec_counter += 1;
        } else {
          block_vars_matrix[block_counter][exec_counter].push(string_to_bytes(buffer.clone()));
        }
        buffer.clear();
        reader.read_line(&mut buffer)?;
      }
      block_vars_matrix.iter().map(|i| i.iter().map(|j| VarsAssignment::new(j).unwrap()).collect()).collect()
    };

    let block_inputs_matrix: Vec<Vec<InputsAssignment>> = {
      let mut block_inputs_matrix = vec![Vec::new()];
      buffer.clear();
      reader.read_line(&mut buffer)?;
      assert_eq!(buffer, "BLOCK 0\n".to_string());

      let mut block_counter = 0;
      let mut exec_counter = 0;
      buffer.clear();
      reader.read_line(&mut buffer)?;
      while buffer != "EXEC_INPUTS\n".to_string() {
        if buffer == format!("BLOCK {}\n", block_counter + 1) {
          block_counter += 1;
          exec_counter = 0;
          block_inputs_matrix.push(Vec::new());
        } else if buffer == format!("EXEC 0\n") {
          block_inputs_matrix[block_counter].push(Vec::new());
        } else if buffer == format!("EXEC {}\n", exec_counter + 1) {
          block_inputs_matrix[block_counter].push(Vec::new());
          exec_counter += 1;
        } else {
          block_inputs_matrix[block_counter][exec_counter].push(string_to_bytes(buffer.clone()));
        }
        buffer.clear();
        reader.read_line(&mut buffer)?;
      }
      block_inputs_matrix.iter().map(|i| i.iter().map(|j| InputsAssignment::new(j).unwrap()).collect()).collect()
    };

    let exec_inputs: Vec<InputsAssignment> = {
      let mut exec_inputs = vec![Vec::new()];
      buffer.clear();
      reader.read_line(&mut buffer)?;
      assert_eq!(buffer, "EXEC 0\n".to_string());

      let mut exec_counter = 0;
      buffer.clear();
      reader.read_line(&mut buffer)?;
      while buffer != "ADDR_MEMS\n".to_string() {
        if buffer == format!("EXEC {}\n", exec_counter + 1) {
          exec_inputs.push(Vec::new());
          exec_counter += 1;
        } else {
          exec_inputs[exec_counter].push(string_to_bytes(buffer.clone()));
        }
        buffer.clear();
        reader.read_line(&mut buffer)?;
      }

      exec_inputs.iter().map(|i| InputsAssignment::new(i).unwrap()).collect()
    };

    let addr_mems_list: Vec<MemsAssignment> = {
      let mut addr_mems_list = vec![Vec::new()];
      buffer.clear();
      reader.read_line(&mut buffer)?;
      
      let mut access_counter = 0;
      while buffer != "INPUTS\n".to_string() {
        if buffer == format!("ACCESS {}\n", access_counter + 1) {
          access_counter += 1;
          addr_mems_list.push(Vec::new());
        } else if buffer == format!("ACCESS 0\n") {
        } else {
          addr_mems_list[access_counter].push(string_to_bytes(buffer.clone()));
        }
        buffer.clear();
        reader.read_line(&mut buffer)?;
      }
      addr_mems_list.iter().map(|i| InputsAssignment::new(i).unwrap()).collect()
    };

    let func_inputs = {
      let mut func_inputs = Vec::new();
      buffer.clear();
      reader.read_line(&mut buffer)?;
      while buffer != "OUTPUTS\n".to_string() {
        func_inputs.push(string_to_bytes(buffer.clone()));
        buffer.clear();
        reader.read_line(&mut buffer)?;
      }
      func_inputs
    };

    let func_outputs = {
      let mut func_outputs = Vec::new();
      buffer.clear();
      reader.read_line(&mut buffer)?;
      while buffer != "OUTPUTS_END\n".to_string() {
        func_outputs.push(string_to_bytes(buffer.clone()));
        buffer.clear();
        reader.read_line(&mut buffer)?;
      }
      func_outputs
    };

    buffer.clear();
    reader.read_line(&mut buffer)?;
    let output_exec_num = buffer.trim().parse::<usize>().unwrap();

    Ok(RunTimeKnowledge {
      block_max_num_proofs,
      block_num_proofs,
      consis_num_proofs,
      total_num_mem_accesses,
    
      block_vars_matrix,
      block_inputs_matrix,
      exec_inputs,
      addr_mems_list,
    
      input: func_inputs,
      output: func_outputs[0],
      output_exec_num
    })
  }
}

fn main() {
  let mut ctk = CompileTimeKnowledge::read_from_file("2pc_demo".to_string()).unwrap();
  let rtk = RunTimeKnowledge::read_from_file("2pc_demo".to_string()).unwrap();

  let block_num_instances = ctk.block_num_instances.next_power_of_two();
  let num_vars = ctk.num_vars;
  assert_eq!(num_vars, num_vars.next_power_of_two());
  let total_num_proofs_bound = ctk.total_num_proofs_bound.next_power_of_two();
  let block_num_mem_accesses = ctk.block_num_mem_accesses;
  let total_num_mem_accesses_bound = ctk.total_num_mem_accesses_bound;

  let block_vars_matrix = rtk.block_vars_matrix;
  let block_inputs_matrix = rtk.block_inputs_matrix;

  // Pad entries in ctk
  ctk.args.extend(vec![Vec::new(); block_num_instances - ctk.args.len()]);

  // --
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
  let total_num_mem_accesses_bound_padded = if total_num_mem_accesses_bound == 0 {1} else {total_num_mem_accesses_bound};
  // MEM_EXTRACT
  let (mem_extract_num_cons, mem_extract_num_non_zero_entries, mem_extract_inst) = Instance::gen_mem_extract_inst(block_num_instances, num_vars, &block_num_mem_accesses);
  // MEM_COHERE
  let (mem_cohere_num_cons_base, mem_cohere_num_non_zero_entries, mem_cohere_inst) = Instance::gen_mem_cohere_inst(total_num_mem_accesses_bound_padded);
  // MEM_BLOCK_POLY is PERM_BLOCK_POLY
  // MEM_ADDR_COMB
  let (mem_addr_comb_num_cons, mem_addr_comb_num_non_zero_entries, mem_addr_comb_inst) = Instance::gen_mem_addr_comb_inst();
  // MEM_ADDR_POLY
  let (mem_addr_poly_num_cons_base, mem_addr_poly_num_non_zero_entries, mem_addr_poly_inst) = Instance::gen_mem_addr_poly_inst(total_num_mem_accesses_bound_padded);

  // --
  // INSTANCE PREPROCESSING
  // --
  let consis_check_num_cons = consis_check_num_cons_base * total_num_proofs_bound;
  let perm_size_bound = total_num_proofs_bound;
  let perm_poly_num_cons = perm_poly_num_cons_base * perm_size_bound;
  let mem_cohere_num_cons = mem_cohere_num_cons_base * total_num_mem_accesses_bound_padded;
  let mem_addr_poly_num_cons = mem_addr_poly_num_cons_base * total_num_mem_accesses_bound_padded;

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
  let mem_cohere_gens = SNARKGens::new(mem_cohere_num_cons, total_num_mem_accesses_bound_padded * 4, 1, mem_cohere_num_non_zero_entries);
  let mem_addr_comb_gens = SNARKGens::new(mem_addr_comb_num_cons, 4 * 4, 1, mem_addr_comb_num_non_zero_entries);
  let mem_addr_poly_gens = SNARKGens::new(mem_addr_poly_num_cons, total_num_mem_accesses_bound_padded * 4, 1, mem_addr_poly_num_non_zero_entries);
  // Only use one version of gens_r1cs_sat
  // for size VAR
  let vars_gens = SNARKGens::new(block_num_cons, num_vars, block_num_instances, block_num_non_zero_entries).gens_r1cs_sat;
  // for size PROOF * VAR
  let proofs_times_vars_gens = SNARKGens::new(block_num_cons, max(total_num_proofs_bound, total_num_mem_accesses_bound_padded) * num_vars, 1, block_num_non_zero_entries).gens_r1cs_sat;

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
    ctk.func_input_width,
    ctk.input_offset,
    ctk.output_offset,
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
    ctk.func_input_width,
    ctk.input_offset,
    ctk.output_offset,
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