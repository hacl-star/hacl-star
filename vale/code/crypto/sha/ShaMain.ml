let _ =
  CmdLineParser.parse_cmdline [
      ("sha256_update",  (fun win -> Vale_Def_PossiblyMonad.Ok (Vale_SHA_X64.va_code_sha_update_bytes_stdcall win)), 4, false);
    ]
