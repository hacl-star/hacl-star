module Vale_gcm_make_length_stdcall

open X64.Machine_s
open X64.Memory
open X64.Vale.State
open X64.Vale.Decls
open X64.GCMencryptstdcall

val va_code_gcm_make_length_stdcall: bool -> va_code

let va_code_gcm_make_length_stdcall = va_code_gcm_make_length_stdcall

let va_pre (va_b0:va_code) (va_s0:va_state) (win:bool) (stack_b:buffer64)
(plain_num_bytes:nat64) (auth_num_bytes:nat64) (b:buffer128)  = va_req_gcm_make_length_stdcall va_b0 va_s0 win stack_b plain_num_bytes auth_num_bytes b 

let va_post (va_b0:va_code) (va_s0:va_state) (va_sM:va_state) (va_fM:va_fuel) (win:bool)  (stack_b:buffer64)
(plain_num_bytes:nat64) (auth_num_bytes:nat64) (b:buffer128)  = va_ens_gcm_make_length_stdcall va_b0 va_s0 win stack_b plain_num_bytes auth_num_bytes b va_sM va_fM

val va_lemma_gcm_make_length_stdcall(va_b0:va_code) (va_s0:va_state) (win:bool) (stack_b:buffer64)
(plain_num_bytes:nat64) (auth_num_bytes:nat64) (b:buffer128) : Ghost ((va_sM:va_state) * (va_fM:va_fuel))
  (requires va_pre va_b0 va_s0 win stack_b plain_num_bytes auth_num_bytes b )
  (ensures (fun (va_sM, va_fM) -> va_post va_b0 va_s0 va_sM va_fM win stack_b plain_num_bytes auth_num_bytes b ))

let va_lemma_gcm_make_length_stdcall = va_lemma_gcm_make_length_stdcall
