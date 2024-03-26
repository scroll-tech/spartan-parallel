| Proofs | Single | W0 | NI | W1 | NI | W2 | NI | w3 | NI |
|--------|--------|----|---|----|---|----|---|----|---|
| BLOCK_CORRECTNESS | false | block_inputs | P | block_vars | P |
| CONSIS_CHECK | true | perm_root_w2 | 1 |
| MEM_EXTRACT | false | perm_w0 | 1 | mem_mask | P | block_vars | P | mem_block_w3 | P |
| MEM_COHERE | true | addr_mems | 1 |
| PERM_ROOT | false | perm_w0 | 1 | perm_root_w1 | P + 2 | perm_root_w2 | P + 2 | perm_root_w3 | P + 2 |
| PERM_MEM | true | perm_mem_w3 | 2 * P + 2 |