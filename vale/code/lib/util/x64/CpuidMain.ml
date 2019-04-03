let _ =
  CmdLineParser.parse_cmdline [
      ("check_aesni",  (fun win -> X64_Cpuidstdcall.va_code_check_aesni_stdcall win));
      ("check_sha",    (fun win -> X64_Cpuidstdcall.va_code_check_sha_stdcall win));
      ("check_adx_bmi2",  (fun win -> X64_Cpuidstdcall.va_code_check_adx_bmi2_stdcall win));
      ("check_avx",     (fun win -> X64_Cpuidstdcall.va_code_check_avx_stdcall win));
      ("check_avx2",    (fun win -> X64_Cpuidstdcall.va_code_check_avx2_stdcall win));
    ]
