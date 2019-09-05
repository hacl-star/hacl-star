module Vale.Stdcalls.X64.Poly
open FStar.Mul

#reset-options "--z3rlimit 50"
let z3rlimit_hack x = ()

(* And here's the poly wrapper itself *)
let lowstar_poly : lowstar_poly_t  =
  IX64.wrap_weak_stdcall
    code_poly
    dom
    (W.mk_prediction code_poly dom [] (poly_lemma code_poly IA.win))

let x64_poly1305 = as_normal_t #lowstar_poly_t lowstar_poly
