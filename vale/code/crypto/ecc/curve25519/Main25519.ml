let _ =
  CmdLineParser.parse_cmdline [
      (*("mul", (fun win -> X64_FastMul.va_code_fast_mul_stdcall win));*)
      (*("mul2", (fun win -> X64_FastMul.va_code_fast_mul2_stdcall win));
      ("sqr",  (fun win -> X64_FastSqr.va_code_fast_sqr_stdcall win));
      ("sqr2", (fun win -> X64_FastSqr.va_code_sqr2_stdcall win));
      ("mul1", (fun win -> X64_FastUtil.va_code_fast_mul1_stdcall win));*)
      ("add1", (fun win -> X64_FastUtil.va_code_fast_add1_stdcall win));
      (*("add",  (fun win -> X64_FastUtil.va_code_fast_add_stdcall win));
      ("sub1", (fun win -> X64_FastUtil.va_code_fast_sub1_stdcall win));
      ("sub",  (fun win -> X64_FastUtil.va_code_fast_sub_stdcall win)); *)
      (* ("mul1_add", (fun win -> X64_FastHybrid.va_code_fast_mul1_add_stdcall win)); *)
      ("fadd_", (fun win -> X64_FastHybrid.va_code_fadd_stdcall win));
      ("fsub_", (fun win -> X64_FastHybrid.va_code_fsub_stdcall win));
      ("fmul1", (fun win -> X64_FastHybrid.va_code_fmul1_stdcall win));
      (*("carry_wide", (fun win -> X64_FastHybrid.va_code_carry_wide_stdcall win));*)
      ("fmul_",  (fun win -> X64_FastWide.va_code_fmul_stdcall win));
      ("fmul2", (fun win -> X64_FastWide.va_code_fmul2_stdcall win));
      ("fsqr",  (fun win -> X64_FastWide.va_code_fsqr_stdcall win));
      ("fsqr2", (fun win -> X64_FastWide.va_code_fsqr2_stdcall win));
      (* ("fast_sqr_loop", (fun win -> X64_FastSqr.va_code_fast_sqr_loop_stdcall win)); *)
      (*("fsqr_loop", (fun win -> X64_FastWide.va_code_fsqr_loop_stdcall win)); *)
      ("cswap2", (fun win -> X64_FastUtil.va_code_cswap2_stdcall win));
    ]
