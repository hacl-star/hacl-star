module Vale_aes_EncryptBlockBEStdcall

open X64.Machine_s
open X64.Memory
open X64.Vale.State
open X64.Vale.Decls
open X64.AESstdcall
open AES_s

val va_code_aes_EncryptBlockBEStdcall: bool -> va_code

let va_code_aes_EncryptBlockBEStdcall = va_code_aes_EncryptBlockBEStdcall

let va_pre (va_b0:va_code) (va_s0:va_state) (win:bool) (stack_b:buffer64)
(output_b:buffer128) (input_b:buffer128) (key:(aes_key_LE AES_128)) (keys_b:buffer128)  = va_req_aes_EncryptBlockBEStdcall va_b0 va_s0 win stack_b output_b input_b key keys_b 

let va_post (va_b0:va_code) (va_s0:va_state) (va_sM:va_state) (va_fM:va_fuel) (win:bool)  (stack_b:buffer64)
(output_b:buffer128) (input_b:buffer128) (key:(aes_key_LE AES_128)) (keys_b:buffer128)  = va_ens_aes_EncryptBlockBEStdcall va_b0 va_s0 win stack_b output_b input_b key keys_b va_sM va_fM

val va_lemma_aes_EncryptBlockBEStdcall(va_b0:va_code) (va_s0:va_state) (win:bool) (stack_b:buffer64)
(output_b:buffer128) (input_b:buffer128) (key:(aes_key_LE AES_128)) (keys_b:buffer128) : Ghost ((va_sM:va_state) * (va_fM:va_fuel))
  (requires va_pre va_b0 va_s0 win stack_b output_b input_b key keys_b )
  (ensures (fun (va_sM, va_fM) -> va_post va_b0 va_s0 va_sM va_fM win stack_b output_b input_b key keys_b ))

let va_lemma_aes_EncryptBlockBEStdcall = va_lemma_aes_EncryptBlockBEStdcall
