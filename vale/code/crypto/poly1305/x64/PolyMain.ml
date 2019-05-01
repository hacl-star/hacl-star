let _ = CmdLineParser.parse_cmdline [
  ("x64_poly1305", (fun win -> X64_Poly1305.va_code_Poly1305 win));
  ]
