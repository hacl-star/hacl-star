let _ =
  CmdLineParser.parse_cmdline [
    ("sha256_update",  (fun win -> Vale_SHA_X64.va_code_Sha_update_bytes_stdcall win, Vale_SHA_X64.va_codegen_success_Sha_update_bytes_stdcall win), 4, false);
  ]
