module Vale.Stdcalls.Sha

(* And here's the sha wrapper itself *)
let lowstar_sha : lowstar_sha_t  =
  IX64.wrap_weak_stdcall
    Interop.down_mem
    code_sha
    dom
    (W.mk_prediction code_sha dom [] (sha_lemma code_sha IA.win))

let sha256_update = as_normal_t #lowstar_sha_t lowstar_sha
