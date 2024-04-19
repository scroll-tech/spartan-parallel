| Proofs | Shift | W0 | NI | W1 | NI | W2 | NI | w3 | NI |
|--------|--------|----|---|----|---|----|---|----|---|
| BLOCK_CORRECTNESS | false | block_inputs | P | block_vars | P |
| CONSIS_CHECK | true | perm_root_w3 | 1 | perm_root_w3_shifted | 1 |
| MEM_EXTRACT | false | perm_w0 | 1 | mem_mask | P | block_vars | P | mem_block_w3 | P |
| PHY_MEM_COHERE | true | addr_phy_mems | 1 | addr_phy_mems_shifted | 1 |
| VIR_MEM_COHERE | true | addr_vir_mems | 1 | addr_vir_mems_shifted | 1 | addr_ts_bits | 1 |
| PERM_ROOT | false | perm_w0 | 1 | perm_root_w1 | P + 2 | perm_root_w2 | P + 2 | perm_root_w3 | P + 2 |
| PERM_POLY | true | perm_poly_w3 | 2 * P + 2 | perm_poly_w3_shifted | 2 * P + 2 |