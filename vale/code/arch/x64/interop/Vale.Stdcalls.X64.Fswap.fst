module Vale.Stdcalls.X64.Fswap
open FStar.Mul

#reset-options "--z3rlimit 50"
let z3rlimit_hack x = ()

(* And here's the cswap wrapper itself *)
let lowstar_cswap : lowstar_cswap_t  =
  assert_norm (List.length cswap_dom + List.length ([]<:list arg) <= 4);
  IX64.wrap_weak_stdcall
    code_cswap
    cswap_dom
    (W.mk_prediction code_cswap cswap_dom [] (cswap_lemma code_cswap IA.win))

let cswap2_e = as_normal_t #lowstar_cswap_t lowstar_cswap
