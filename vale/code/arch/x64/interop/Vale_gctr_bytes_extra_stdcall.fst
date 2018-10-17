module Vale_gctr_bytes_extra_stdcall

open X64.Machine_s
open X64.Memory
open X64.Vale.State
open X64.Vale.Decls
open X64.GCTRstdcall
open AES_s

val va_code_gctr_bytes_extra_stdcall: bool -> va_code

let va_code_gctr_bytes_extra_stdcall = va_code_gctr_bytes_extra_stdcall

let va_pre (va_b0:va_code) (va_s0:va_state) (win:bool) (stack_b:buffer64)
(plain_b:buffer128) (num_bytes:nat64) (iv_old:(quad32)) (iv_b:buffer128) (key:(aes_key_LE AES_128)) (keys_b:buffer128) (cipher_b:buffer128)  = va_req_gctr_bytes_extra_stdcall va_b0 va_s0 win stack_b plain_b num_bytes iv_old iv_b key keys_b cipher_b 

let va_post (va_b0:va_code) (va_s0:va_state) (va_sM:va_state) (va_fM:va_fuel) (win:bool)  (stack_b:buffer64)
(plain_b:buffer128) (num_bytes:nat64) (iv_old:(quad32)) (iv_b:buffer128) (key:(aes_key_LE AES_128)) (keys_b:buffer128) (cipher_b:buffer128)  = va_ens_gctr_bytes_extra_stdcall va_b0 va_s0 win stack_b plain_b num_bytes iv_old iv_b key keys_b cipher_b va_sM va_fM

val va_lemma_gctr_bytes_extra_stdcall(va_b0:va_code) (va_s0:va_state) (win:bool) (stack_b:buffer64)
(plain_b:buffer128) (num_bytes:nat64) (iv_old:(quad32)) (iv_b:buffer128) (key:(aes_key_LE AES_128)) (keys_b:buffer128) (cipher_b:buffer128) : Ghost ((va_sM:va_state) * (va_fM:va_fuel))
  (requires va_pre va_b0 va_s0 win stack_b plain_b num_bytes iv_old iv_b key keys_b cipher_b )
  (ensures (fun (va_sM, va_fM) -> va_post va_b0 va_s0 va_sM va_fM win stack_b plain_b num_bytes iv_old iv_b key keys_b cipher_b ))

let va_lemma_gctr_bytes_extra_stdcall = va_lemma_gctr_bytes_extra_stdcall
