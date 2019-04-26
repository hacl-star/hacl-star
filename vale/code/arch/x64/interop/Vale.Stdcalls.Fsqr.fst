module Vale.Stdcalls.Fsqr

(* And here's the fsqr wrapper itself *)
let lowstar_fsqr : lowstar_fsqr_t  =
  assert_norm (List.length fsqr_dom + List.length ([]<:list arg) <= 4);
  IX64.wrap_weak_stdcall
    Interop.down_mem
    code_fsqr
    fsqr_dom
    (W.mk_prediction code_fsqr fsqr_dom [] (fsqr_lemma code_fsqr IA.win))

let fsqr = as_normal_t #lowstar_fsqr_t lowstar_fsqr

(* And here's the fsqr2 wrapper itself *)
let lowstar_fsqr2 : lowstar_fsqr2_t  =
  assert_norm (List.length fsqr_dom + List.length ([]<:list arg) <= 4);
  IX64.wrap_weak_stdcall
    Interop.down_mem
    code_fsqr2
    fsqr_dom
    (W.mk_prediction code_fsqr2 fsqr_dom [] (fsqr2_lemma code_fsqr2 IA.win))

let fsqr2 = as_normal_t #lowstar_fsqr2_t lowstar_fsqr2
