let _ =
  CmdLineParser.parse_cmdline [
      ("sha256_update",           (fun win -> X64_SHA.va_code_sha_update_bytes_stdcall win));
    ]
