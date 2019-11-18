let _ =
  CmdLineParser.parse_cmdline [
    (*("mul", (fun win -> Vale_Curve25519_X64_FastMul.va_code_fast_mul_stdcall win));*)
    (*("mul2", (fun win -> Vale_Curve25519_X64_FastMul.va_code_fast_mul2_stdcall win));
      ("sqr",  (fun win -> Vale_Curve25519_X64_FastSqr.va_code_fast_sqr_stdcall win));
      ("sqr2", (fun win -> Vale_Curve25519_X64_FastSqr.va_code_sqr2_stdcall win));
      ("mul1", (fun win -> Vale_Curve25519_X64_FastUtil.va_code_fast_mul1_stdcall win));*)
    ("add1", (fun win -> Vale_Curve25519_X64_FastUtil.va_code_fast_add1_stdcall win, Vale_Curve25519_X64_FastUtil.va_codegen_success_fast_add1_stdcall win), 3, false);
    (*("add",  (fun win -> Vale_Curve25519_X64_FastUtil.va_code_fast_add_stdcall win));
      ("sub1", (fun win -> Vale_Curve25519_X64_FastUtil.va_code_fast_sub1_stdcall win));
      ("sub",  (fun win -> Vale_Curve25519_X64_FastUtil.va_code_fast_sub_stdcall win)); *)
    (* ("mul1_add", (fun win -> Vale_Curve25519_X64_FastHybrid.va_code_fast_mul1_add_stdcall win)); *)
    ("fadd_", (fun win -> Vale_Curve25519_X64_FastHybrid.va_code_fadd_stdcall win, Vale_Curve25519_X64_FastHybrid.va_codegen_success_fadd_stdcall win), 3, false);
    ("fsub_", (fun win -> Vale_Curve25519_X64_FastHybrid.va_code_fsub_stdcall win, Vale_Curve25519_X64_FastHybrid.va_codegen_success_fsub_stdcall win), 3, false);
    ("fmul1", (fun win -> Vale_Curve25519_X64_FastHybrid.va_code_fmul1_stdcall win, Vale_Curve25519_X64_FastHybrid.va_codegen_success_fmul1_stdcall win), 3, false);
    (*("carry_wide", (fun win -> Vale_Curve25519_X64_FastHybrid.va_code_carry_wide_stdcall win));*)
    ("fmul_",  (fun win -> Vale_Curve25519_X64_FastWide.va_code_fmul_stdcall win, Vale_Curve25519_X64_FastWide.va_codegen_success_fmul_stdcall win), 4, false);
    ("fmul2", (fun win -> Vale_Curve25519_X64_FastWide.va_code_fmul2_stdcall win, Vale_Curve25519_X64_FastWide.va_codegen_success_fmul2_stdcall win), 4, false);
    ("fsqr",  (fun win -> Vale_Curve25519_X64_FastWide.va_code_fsqr_stdcall win, Vale_Curve25519_X64_FastWide.va_codegen_success_fsqr_stdcall win), 3, false);
    ("fsqr2", (fun win -> Vale_Curve25519_X64_FastWide.va_code_fsqr2_stdcall win, Vale_Curve25519_X64_FastWide.va_codegen_success_fsqr2_stdcall win), 3, false);
    (* ("fast_sqr_loop", (fun win -> Vale_Curve25519_X64_FastSqr.va_code_fast_sqr_loop_stdcall win)); *)
    (*("fsqr_loop", (fun win -> Vale_Curve25519_X64_FastWide.va_code_fsqr_loop_stdcall win)); *)
    ("cswap2", (fun win -> Vale_Curve25519_X64_FastUtil.va_code_cswap2_stdcall win, Vale_Curve25519_X64_FastUtil.va_codegen_success_cswap2_stdcall win), 3, false);
  ]
