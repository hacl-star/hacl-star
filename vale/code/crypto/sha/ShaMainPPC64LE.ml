let _ =
  CmdLineParser.parse_cmdline_ppc64le [
    ("sha256_update", Vale_SHA_PPC64LE.va_code_Sha_update_bytes_main, 4, false);
  ]
