module Vale.Stdcalls.X64.Fmul
open FStar.Mul

#reset-options "--z3rlimit 50"
let z3rlimit_hack x = ()

(* And here's the fmul wrapper itself *)
let lowstar_fmul : lowstar_fmul_t  =
  assert_norm (List.length fmul_dom + List.length ([]<:list arg) <= 4);
  IX64.wrap_weak_stdcall
    code_Fmul
    fmul_dom
    (W.mk_prediction code_Fmul fmul_dom [] (fmul_lemma code_Fmul IA.win))

let fmul_e = as_normal_t #lowstar_fmul_t lowstar_fmul

(* And here's the fmul2 wrapper itself *)
let lowstar_fmul2 : lowstar_fmul2_t  =
  assert_norm (List.length fmul_dom + List.length ([]<:list arg) <= 4);
  IX64.wrap_weak_stdcall
    code_Fmul2
    fmul_dom
    (W.mk_prediction code_Fmul2 fmul_dom [] (fmul2_lemma code_Fmul2 IA.win))

let fmul2_e = as_normal_t #lowstar_fmul2_t lowstar_fmul2

(* And here's the fmul1 wrapper itself *)
let lowstar_fmul1 : lowstar_fmul1_t  =
  assert_norm (List.length fmul1_dom + List.length ([]<:list arg) <= 4);
  IX64.wrap_weak_stdcall
    code_Fmul1
    fmul1_dom
    (W.mk_prediction code_Fmul1 fmul1_dom [] (fmul1_lemma code_Fmul1 IA.win))

let fmul_scalar_e = as_normal_t #lowstar_fmul1_t lowstar_fmul1
