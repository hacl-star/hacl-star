module Vale.Stdcalls.X64.Sha
open FStar.Mul

#reset-options "--z3rlimit 50"
let z3rlimit_hack x = ()

(* And here's the sha wrapper itself *)
let lowstar_sha : lowstar_sha_t  =
  IX64.wrap_weak_stdcall
    code_sha
    dom
    (W.mk_prediction code_sha dom [] (sha_lemma code_sha IA.win))

let sha256_update = as_normal_t #lowstar_sha_t lowstar_sha
