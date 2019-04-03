let _ = CmdLineParser.parse_cmdline [
  ("poly1305", (fun win -> X64_Poly1305.va_code_poly1305 win));
  ]
