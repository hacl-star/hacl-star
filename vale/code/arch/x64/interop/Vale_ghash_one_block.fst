module Vale_ghash_one_block

open X64.Machine_s
open X64.Memory
open X64.Vale.State
open X64.Vale.Decls
open X64.GHashstdcall

val va_code_ghash_one_block: bool -> va_code

let va_code_ghash_one_block = va_code_ghash_one_block

let va_pre (va_b0:va_code) (va_s0:va_state) (win:bool) (stack_b:buffer64)
(h_b:buffer128) (hash_b:buffer128) (input_b:buffer128) (offset:nat64)  = va_req_ghash_one_block va_b0 va_s0 win stack_b h_b hash_b input_b offset 

let va_post (va_b0:va_code) (va_s0:va_state) (va_sM:va_state) (va_fM:va_fuel) (win:bool)  (stack_b:buffer64)
(h_b:buffer128) (hash_b:buffer128) (input_b:buffer128) (offset:nat64)  = va_ens_ghash_one_block va_b0 va_s0 win stack_b h_b hash_b input_b offset va_sM va_fM

val va_lemma_ghash_one_block(va_b0:va_code) (va_s0:va_state) (win:bool) (stack_b:buffer64)
(h_b:buffer128) (hash_b:buffer128) (input_b:buffer128) (offset:nat64) : Ghost ((va_sM:va_state) * (va_fM:va_fuel))
  (requires va_pre va_b0 va_s0 win stack_b h_b hash_b input_b offset )
  (ensures (fun (va_sM, va_fM) -> va_post va_b0 va_s0 va_sM va_fM win stack_b h_b hash_b input_b offset ))

let va_lemma_ghash_one_block = va_lemma_ghash_one_block
