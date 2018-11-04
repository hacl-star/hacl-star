let _ =
  CmdLineParser.parse_cmdline [
      ("mul2", (fun win -> X64_FastMul.va_code_fast_mul_stdcall win));
      ("sqr",  (fun win -> X64_FastSqr.va_code_fast_sqr_stdcall win));
      ("mul1", (fun win -> X64_FastUtil.va_code_fast_mul1_stdcall win));
      ("add1", (fun win -> X64_FastUtil.va_code_fast_add1_stdcall win));
      ("add",  (fun win -> X64_FastUtil.va_code_fast_add_stdcall win));
    ]
