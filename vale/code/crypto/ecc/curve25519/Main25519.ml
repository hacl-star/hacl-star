let _ =
  CmdLineParser.parse_cmdline [
    (*("mul", (fun win -> Vale_Curve25519_X64_FastMul.va_code_Fast_mul_stdcall win));*)
    (*("mul2", (fun win -> Vale_Curve25519_X64_FastMul.va_code_Fast_mul2_stdcall win));
      ("sqr",  (fun win -> Vale_Curve25519_X64_FastSqr.va_code_Fast_sqr_stdcall win));
      ("sqr2", (fun win -> Vale_Curve25519_X64_FastSqr.va_code_Sqr2_stdcall win));
      ("mul1", (fun win -> Vale_Curve25519_X64_FastUtil.va_code_Fast_mul1_stdcall win));*)
    ("add_scalar_e", (fun win -> Vale_Curve25519_X64_FastUtil.va_code_Fast_add1_stdcall win, Vale_Curve25519_X64_FastUtil.va_codegen_success_Fast_add1_stdcall win), 3, false);
    (*("add",  (fun win -> Vale_Curve25519_X64_FastUtil.va_code_Fast_add_stdcall win));
      ("sub1", (fun win -> Vale_Curve25519_X64_FastUtil.va_code_Fast_sub1_stdcall win));
      ("sub",  (fun win -> Vale_Curve25519_X64_FastUtil.va_code_Fast_sub_stdcall win)); *)
    (* ("mul1_add", (fun win -> Vale_Curve25519_X64_FastHybrid.va_code_fast_mul1_add_stdcall win)); *)
    ("fadd_e", (fun win -> Vale_Curve25519_X64_FastHybrid.va_code_Fadd_stdcall win, Vale_Curve25519_X64_FastHybrid.va_codegen_success_Fadd_stdcall win), 3, false);
    ("fsub_e", (fun win -> Vale_Curve25519_X64_FastHybrid.va_code_Fsub_stdcall win, Vale_Curve25519_X64_FastHybrid.va_codegen_success_Fsub_stdcall win), 3, false);
    ("fmul_scalar_e", (fun win -> Vale_Curve25519_X64_FastHybrid.va_code_Fmul1_stdcall win, Vale_Curve25519_X64_FastHybrid.va_codegen_success_Fmul1_stdcall win), 3, false);
    (*("carry_wide", (fun win -> Vale_Curve25519_X64_FastHybrid.va_code_Carry_wide_stdcall win));*)
    ("fmul_e",  (fun win -> Vale_Curve25519_X64_FastWide.va_code_Fmul_stdcall win, Vale_Curve25519_X64_FastWide.va_codegen_success_Fmul_stdcall win), 4, false);
    ("fmul2_e", (fun win -> Vale_Curve25519_X64_FastWide.va_code_Fmul2_stdcall win, Vale_Curve25519_X64_FastWide.va_codegen_success_Fmul2_stdcall win), 4, false);
    ("fsqr_e",  (fun win -> Vale_Curve25519_X64_FastWide.va_code_Fsqr_stdcall win, Vale_Curve25519_X64_FastWide.va_codegen_success_Fsqr_stdcall win), 3, false);
    ("fsqr2_e", (fun win -> Vale_Curve25519_X64_FastWide.va_code_Fsqr2_stdcall win, Vale_Curve25519_X64_FastWide.va_codegen_success_Fsqr2_stdcall win), 3, false);
    (* ("fast_sqr_loop", (fun win -> Vale_Curve25519_X64_FastSqr.va_code_Fast_sqr_loop_stdcall win)); *)
    (*("fsqr_loop", (fun win -> Vale_Curve25519_X64_FastWide.va_code_Fsqr_loop_stdcall win)); *)
    ("cswap2_e", (fun win -> Vale_Curve25519_X64_FastUtil.va_code_Cswap2_stdcall win, Vale_Curve25519_X64_FastUtil.va_codegen_success_Cswap2_stdcall win), 3, false);
  ]
