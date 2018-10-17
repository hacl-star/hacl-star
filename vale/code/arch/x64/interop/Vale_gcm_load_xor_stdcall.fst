module Vale_gcm_load_xor_stdcall

open X64.Machine_s
open X64.Memory
open X64.Vale.State
open X64.Vale.Decls
open X64.Util
open AES_s

val va_code_gcm_load_xor_stdcall: bool -> va_code

let va_code_gcm_load_xor_stdcall = va_code_gcm_load_xor_stdcall

let va_pre (va_b0:va_code) (va_s0:va_state) (win:bool) (stack_b:buffer64)
(plain_b:buffer128) (mask_b:buffer128) (cipher_b:buffer128) (offset:nat64) (num_blocks:(nat64)) (key:(aes_key_LE AES_128)) (iv:(quad32))  = va_req_gcm_load_xor_stdcall va_b0 va_s0 win stack_b plain_b mask_b cipher_b offset num_blocks key iv 

let va_post (va_b0:va_code) (va_s0:va_state) (va_sM:va_state) (va_fM:va_fuel) (win:bool)  (stack_b:buffer64)
(plain_b:buffer128) (mask_b:buffer128) (cipher_b:buffer128) (offset:nat64) (num_blocks:(nat64)) (key:(aes_key_LE AES_128)) (iv:(quad32))  = va_ens_gcm_load_xor_stdcall va_b0 va_s0 win stack_b plain_b mask_b cipher_b offset num_blocks key iv va_sM va_fM

val va_lemma_gcm_load_xor_stdcall(va_b0:va_code) (va_s0:va_state) (win:bool) (stack_b:buffer64)
(plain_b:buffer128) (mask_b:buffer128) (cipher_b:buffer128) (offset:nat64) (num_blocks:(nat64)) (key:(aes_key_LE AES_128)) (iv:(quad32)) : Ghost ((va_sM:va_state) * (va_fM:va_fuel))
  (requires va_pre va_b0 va_s0 win stack_b plain_b mask_b cipher_b offset num_blocks key iv )
  (ensures (fun (va_sM, va_fM) -> va_post va_b0 va_s0 va_sM va_fM win stack_b plain_b mask_b cipher_b offset num_blocks key iv ))

let va_lemma_gcm_load_xor_stdcall = va_lemma_gcm_load_xor_stdcall
