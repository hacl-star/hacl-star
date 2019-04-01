module Vale.Stdcalls.Fmul

(* And here's the fmul wrapper itself *)
let lowstar_fmul : lowstar_fmul_t  =
  assert_norm (List.length fmul_dom + List.length ([]<:list arg) <= 4);
  IX64.wrap_weak_stdcall
    Interop.down_mem
    code_fmul
    fmul_dom
    (W.mk_prediction code_fmul fmul_dom [] (fmul_lemma code_fmul IA.win))

let fmul_ = as_normal_t #lowstar_fmul_t lowstar_fmul

(* And here's the fmul2 wrapper itself *)
let lowstar_fmul2 : lowstar_fmul2_t  =
  assert_norm (List.length fmul_dom + List.length ([]<:list arg) <= 4); 
  IX64.wrap_weak_stdcall
    Interop.down_mem
    code_fmul2
    fmul_dom
    (W.mk_prediction code_fmul2 fmul_dom [] (fmul2_lemma code_fmul2 IA.win))

let fmul2 = as_normal_t #lowstar_fmul2_t lowstar_fmul2

(* And here's the fmul1 wrapper itself *)
let lowstar_fmul1 : lowstar_fmul1_t  =
  assert_norm (List.length fmul1_dom + List.length ([]<:list arg) <= 4);
  IX64.wrap_weak_stdcall
    Interop.down_mem
    code_fmul1
    fmul1_dom
    (W.mk_prediction code_fmul1 fmul1_dom [] (fmul1_lemma code_fmul1 IA.win))

let fmul1 = as_normal_t #lowstar_fmul1_t lowstar_fmul1
