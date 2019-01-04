module Vale_memcpy

open X64.Machine_s
open X64.Memory
open X64.Vale.State
open X64.Vale.Decls
open Test.Vale_memcpy

val va_code_memcpy: bool -> va_code

let va_code_memcpy = va_code_memcpy

unfold 
let va_pre (va_b0:va_code) (va_s0:va_state) (win:bool) (stack_b:buffer64)
(dst:buffer64) (src:buffer64)  = va_req_memcpy va_b0 va_s0 win stack_b dst src 

let va_post (va_b0:va_code) (va_s0:va_state) (va_sM:va_state) (va_fM:va_fuel) (win:bool)  (stack_b:buffer64)
(dst:buffer64) (src:buffer64)  = va_ens_memcpy va_b0 va_s0 win stack_b dst src va_sM va_fM

val va_lemma_memcpy(va_b0:va_code) (va_s0:va_state) (win:bool) (stack_b:buffer64)
(dst:buffer64) (src:buffer64) : Ghost ((va_sM:va_state) * (va_fM:va_fuel))
  (requires va_pre va_b0 va_s0 win stack_b dst src )
  (ensures (fun (va_sM, va_fM) -> va_post va_b0 va_s0 va_sM va_fM win stack_b dst src ))

let va_lemma_memcpy = va_lemma_memcpy
