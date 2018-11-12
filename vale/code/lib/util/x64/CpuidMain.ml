let _ =
  CmdLineParser.parse_cmdline [
      ("check_aesni_stdcall",  (fun win -> X64_Cpuidstdcall.check_aesni_stdcall win));
      ("check_sha_stdcall",    (fun win -> X64_Cpuidstdcall.check_sha_stdcall win));
    ]
