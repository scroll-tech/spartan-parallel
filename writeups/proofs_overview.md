| Proofs | W0 | NI | W1 | NI | W2 | NI | w3 | NI |
|--------|----|---|----|---|----|---|----|---|
| BLOCK_CORRECTNESS | block_inputs | P | block_vars | P |
| CONSIS_CHECK | perm_root_w2 | 1 |
| PERM_PRELIM | perm_w0 | 1 |
| MEM_EXTRACT | mem_w0 | 1 | mem_mask | P | block_vars | P | mem_block_w3 | P |
| MEM_COHERE | addr_mems | 1 |
| PERM_ROOT | perm_w0 | 1 | perm_root_w1 | P + 2 | perm_root_w2 | P + 2 | perm_root_w3 | P + 2 |
| PERM_MEM | perm_mem_w3 | 2 * P + 2 |