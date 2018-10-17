module Vale_ghash_extra_stdcall

open X64.Machine_s
open X64.Memory
open X64.Vale.State
open X64.Vale.Decls
open X64.GHashstdcall

val va_code_ghash_extra_stdcall: bool -> va_code

let va_code_ghash_extra_stdcall = va_code_ghash_extra_stdcall

let va_pre (va_b0:va_code) (va_s0:va_state) (win:bool) (stack_b:buffer64)
(in_b:buffer128) (hash_b:buffer128) (h_b:buffer128) (num_bytes:nat64) (orig_hash:(quad32))  = va_req_ghash_extra_stdcall va_b0 va_s0 win stack_b in_b hash_b h_b num_bytes orig_hash 

let va_post (va_b0:va_code) (va_s0:va_state) (va_sM:va_state) (va_fM:va_fuel) (win:bool)  (stack_b:buffer64)
(in_b:buffer128) (hash_b:buffer128) (h_b:buffer128) (num_bytes:nat64) (orig_hash:(quad32))  = va_ens_ghash_extra_stdcall va_b0 va_s0 win stack_b in_b hash_b h_b num_bytes orig_hash va_sM va_fM

val va_lemma_ghash_extra_stdcall(va_b0:va_code) (va_s0:va_state) (win:bool) (stack_b:buffer64)
(in_b:buffer128) (hash_b:buffer128) (h_b:buffer128) (num_bytes:nat64) (orig_hash:(quad32)) : Ghost ((va_sM:va_state) * (va_fM:va_fuel))
  (requires va_pre va_b0 va_s0 win stack_b in_b hash_b h_b num_bytes orig_hash )
  (ensures (fun (va_sM, va_fM) -> va_post va_b0 va_s0 va_sM va_fM win stack_b in_b hash_b h_b num_bytes orig_hash ))

let va_lemma_ghash_extra_stdcall = va_lemma_ghash_extra_stdcall
