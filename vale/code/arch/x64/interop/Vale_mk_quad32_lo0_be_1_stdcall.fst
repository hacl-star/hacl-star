module Vale_mk_quad32_lo0_be_1_stdcall

open X64.Machine_s
open X64.Memory
open X64.Vale.State
open X64.Vale.Decls
open X64.Util

val va_code_mk_quad32_lo0_be_1_stdcall: bool -> va_code

let va_code_mk_quad32_lo0_be_1_stdcall = va_code_mk_quad32_lo0_be_1_stdcall

let va_pre (va_b0:va_code) (va_s0:va_state) (win:bool) (stack_b:buffer64)
(b:buffer128)  = va_req_mk_quad32_lo0_be_1_stdcall va_b0 va_s0 win stack_b b 

let va_post (va_b0:va_code) (va_s0:va_state) (va_sM:va_state) (va_fM:va_fuel) (win:bool)  (stack_b:buffer64)
(b:buffer128)  = va_ens_mk_quad32_lo0_be_1_stdcall va_b0 va_s0 win stack_b b va_sM va_fM

val va_lemma_mk_quad32_lo0_be_1_stdcall(va_b0:va_code) (va_s0:va_state) (win:bool) (stack_b:buffer64)
(b:buffer128) : Ghost ((va_sM:va_state) * (va_fM:va_fuel))
  (requires va_pre va_b0 va_s0 win stack_b b )
  (ensures (fun (va_sM, va_fM) -> va_post va_b0 va_s0 va_sM va_fM win stack_b b ))

let va_lemma_mk_quad32_lo0_be_1_stdcall = va_lemma_mk_quad32_lo0_be_1_stdcall
