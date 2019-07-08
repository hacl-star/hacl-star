let _ =
  CmdLineParser.parse_cmdline [
      (*("mul", (fun win -> Vale_Curve25519_X64_FastMul.va_code_fast_mul_stdcall win, Vale_Def_PossiblyMonad.ttrue));*)
      (*("mul2", (fun win -> Vale_Curve25519_X64_FastMul.va_code_fast_mul2_stdcall win, Vale_Def_PossiblyMonad.ttrue));
      ("sqr",  (fun win -> Vale_Curve25519_X64_FastSqr.va_code_fast_sqr_stdcall win, Vale_Def_PossiblyMonad.ttrue));
      ("sqr2", (fun win -> Vale_Curve25519_X64_FastSqr.va_code_sqr2_stdcall win, Vale_Def_PossiblyMonad.ttrue));
      ("mul1", (fun win -> Vale_Curve25519_X64_FastUtil.va_code_fast_mul1_stdcall win, Vale_Def_PossiblyMonad.ttrue));*)
      ("add1", (fun win -> Vale_Curve25519_X64_FastUtil.va_code_fast_add1_stdcall win, Vale_Def_PossiblyMonad.ttrue), 3, false);
      (*("add",  (fun win -> Vale_Curve25519_X64_FastUtil.va_code_fast_add_stdcall win, Vale_Def_PossiblyMonad.ttrue));
      ("sub1", (fun win -> Vale_Curve25519_X64_FastUtil.va_code_fast_sub1_stdcall win, Vale_Def_PossiblyMonad.ttrue));
      ("sub",  (fun win -> Vale_Curve25519_X64_FastUtil.va_code_fast_sub_stdcall win, Vale_Def_PossiblyMonad.ttrue)); *)
      (* ("mul1_add", (fun win -> Vale_Curve25519_X64_FastHybrid.va_code_fast_mul1_add_stdcall win, Vale_Def_PossiblyMonad.ttrue)); *)
      ("fadd_", (fun win -> Vale_Curve25519_X64_FastHybrid.va_code_fadd_stdcall win, Vale_Def_PossiblyMonad.ttrue), 3, false);
      ("fsub_", (fun win -> Vale_Curve25519_X64_FastHybrid.va_code_fsub_stdcall win, Vale_Def_PossiblyMonad.ttrue), 3, false);
      ("fmul1", (fun win -> Vale_Curve25519_X64_FastHybrid.va_code_fmul1_stdcall win, Vale_Def_PossiblyMonad.ttrue), 3, false);
      (*("carry_wide", (fun win -> Vale_Curve25519_X64_FastHybrid.va_code_carry_wide_stdcall win, Vale_Def_PossiblyMonad.ttrue));*)
      ("fmul_",  (fun win -> Vale_Curve25519_X64_FastWide.va_code_fmul_stdcall win, Vale_Def_PossiblyMonad.ttrue), 4, false);
      ("fmul2", (fun win -> Vale_Curve25519_X64_FastWide.va_code_fmul2_stdcall win, Vale_Def_PossiblyMonad.ttrue), 4, false);
      ("fsqr",  (fun win -> Vale_Curve25519_X64_FastWide.va_code_fsqr_stdcall win, Vale_Def_PossiblyMonad.ttrue), 3, false);
      ("fsqr2", (fun win -> Vale_Curve25519_X64_FastWide.va_code_fsqr2_stdcall win, Vale_Def_PossiblyMonad.ttrue), 3, false);
      (* ("fast_sqr_loop", (fun win -> Vale_Curve25519_X64_FastSqr.va_code_fast_sqr_loop_stdcall win, Vale_Def_PossiblyMonad.ttrue)); *)
      (*("fsqr_loop", (fun win -> Vale_Curve25519_X64_FastWide.va_code_fsqr_loop_stdcall win, Vale_Def_PossiblyMonad.ttrue)); *)
      ("cswap2", (fun win -> Vale_Curve25519_X64_FastUtil.va_code_cswap2_stdcall win, Vale_Def_PossiblyMonad.ttrue), 3, false);
    ]
