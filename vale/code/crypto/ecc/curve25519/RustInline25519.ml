let _ = print_string "use std::arch::asm;\n\n"

let _ = Vale_Inline_X64_Fadd_inline.add1_code_rust_inline ()
let _ = Vale_Inline_X64_Fadd_inline.fadd_code_rust_inline ()
let _ = Vale_Inline_X64_Fadd_inline.fsub_code_rust_inline ()
let _ = Vale_Inline_X64_Fmul_inline.fmul_code_rust_inline ()
let _ = Vale_Inline_X64_Fmul_inline.fmul2_code_rust_inline ()
let _ = Vale_Inline_X64_Fmul_inline.fmul1_code_rust_inline ()
let _ = Vale_Inline_X64_Fswap_inline.cswap2_code_rust_inline ()
let _ = Vale_Inline_X64_Fsqr_inline.fsqr_code_rust_inline ()
let _ = Vale_Inline_X64_Fsqr_inline.fsqr2_code_rust_inline ()
