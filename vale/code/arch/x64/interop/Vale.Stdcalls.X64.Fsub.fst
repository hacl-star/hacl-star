module Vale.Stdcalls.X64.Fsub
open FStar.Mul

#reset-options "--z3rlimit 50"
let z3rlimit_hack x = ()

(* And here's the fsub wrapper itself *)
let lowstar_Fsub : lowstar_Fsub_t  =
  assert_norm (List.length dom + List.length ([]<:list arg) <= 4);
  IX64.wrap_weak_stdcall
    code_Fsub
    dom
    (W.mk_prediction code_Fsub dom [] (fsub_lemma code_Fsub IA.win))

let fsub_e //: normal lowstar_Fsub_t
  = as_normal_t #lowstar_Fsub_t lowstar_Fsub
