module Vale.Stdcalls.X64.Cpuid
open FStar.Mul

(* And here's the check_aesni wrapper itself *)
let lowstar_aesni : lowstar_aesni_t  =
  IX64.wrap_weak_stdcall
    code_aesni
    dom
    (W.mk_prediction code_aesni dom [] (aesni_lemma code_aesni IA.win))

let check_aesni = as_normal_t #lowstar_aesni_t lowstar_aesni

(* And here's the check_aesni wrapper itself *)
let lowstar_sha : lowstar_sha_t  =
  IX64.wrap_weak_stdcall
    code_sha
    dom
    (W.mk_prediction code_sha dom [] (sha_lemma code_sha IA.win))

let check_sha = as_normal_t #lowstar_sha_t lowstar_sha

(* And here's the check_adx wrapper itself *)
let lowstar_adx : lowstar_adx_t  =
  IX64.wrap_weak_stdcall
    code_adx
    dom
    (W.mk_prediction code_adx dom [] (adx_lemma code_adx IA.win))

let check_adx_bmi2 = as_normal_t #lowstar_adx_t lowstar_adx

(* And here's the check_avx wrapper itself *)
let lowstar_avx : lowstar_avx_t  =
  IX64.wrap_weak_stdcall
    code_avx
    dom
    (W.mk_prediction code_avx dom [] (avx_lemma code_avx IA.win))

let check_avx = as_normal_t #lowstar_avx_t lowstar_avx

(* And here's the check_avx wrapper itself *)
let lowstar_avx2 : lowstar_avx2_t  =
  IX64.wrap_weak_stdcall
    code_avx2
    dom
    (W.mk_prediction code_avx2 dom [] (avx2_lemma code_avx2 IA.win))

let check_avx2 = as_normal_t #lowstar_avx2_t lowstar_avx2

(* And here's the check_movbe wrapper itself *)
let lowstar_movbe : lowstar_movbe_t  =
  IX64.wrap_weak_stdcall
    code_movbe
    dom
    (W.mk_prediction code_movbe dom [] (movbe_lemma code_movbe IA.win))

let check_movbe = as_normal_t #lowstar_movbe_t lowstar_movbe

(* And here's the check_sse wrapper itself *)
let lowstar_sse : lowstar_sse_t  =
  IX64.wrap_weak_stdcall
    code_sse
    dom
    (W.mk_prediction code_sse dom [] (sse_lemma code_sse IA.win))

let check_sse = as_normal_t #lowstar_sse_t lowstar_sse

(* And here's the check_rdrand wrapper itself *)
let lowstar_rdrand : lowstar_rdrand_t  =
  IX64.wrap_weak_stdcall
    code_rdrand
    dom
    (W.mk_prediction code_rdrand dom [] (rdrand_lemma code_rdrand IA.win))

let check_rdrand = as_normal_t #lowstar_rdrand_t lowstar_rdrand
