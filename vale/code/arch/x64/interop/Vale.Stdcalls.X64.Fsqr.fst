module Vale.Stdcalls.X64.Fsqr
open FStar.Mul

#reset-options "--z3rlimit 50"
let z3rlimit_hack x = ()

(* And here's the fsqr wrapper itself *)
let lowstar_Fsqr : lowstar_Fsqr_t  =
  assert_norm (List.length fsqr_dom + List.length ([]<:list arg) <= 4);
  IX64.wrap_weak_stdcall
    code_Fsqr
    fsqr_dom
    (W.mk_prediction code_Fsqr fsqr_dom [] (fsqr_lemma code_Fsqr IA.win))

let fsqr_e = as_normal_t #lowstar_Fsqr_t lowstar_Fsqr

(* And here's the fsqr2 wrapper itself *)
let lowstar_Fsqr2 : lowstar_Fsqr2_t  =
  assert_norm (List.length fsqr_dom + List.length ([]<:list arg) <= 4);
  IX64.wrap_weak_stdcall
    code_Fsqr2
    fsqr_dom
    (W.mk_prediction code_Fsqr2 fsqr_dom [] (fsqr2_lemma code_Fsqr2 IA.win))

let fsqr2_e = as_normal_t #lowstar_Fsqr2_t lowstar_Fsqr2
