module Vale.Stdcalls.Poly

(* And here's the poly wrapper itself *)
let lowstar_poly : lowstar_poly_t  =
  IX64.wrap_weak_stdcall
    Interop.down_mem
    code_poly
    dom
    (W.mk_prediction code_poly dom [] (poly_lemma code_poly IA.win))

let poly1305 = as_normal_t #lowstar_poly_t lowstar_poly
