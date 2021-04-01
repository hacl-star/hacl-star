open Ctypes
module Bindings(F:Cstubs.FOREIGN) =
  struct
    open F
    module Hacl_Spec_applied = (Hacl_Spec_bindings.Bindings)(Hacl_Spec_stubs)
    open Hacl_Spec_applied
    let hacl_FFDHE_ffdhe_len =
      foreign "Hacl_FFDHE_ffdhe_len"
        (spec_FFDHE_ffdhe_alg @-> (returning uint32_t))
    let hacl_FFDHE_new_ffdhe_precomp_p =
      foreign "Hacl_FFDHE_new_ffdhe_precomp_p"
        (spec_FFDHE_ffdhe_alg @-> (returning (ptr uint64_t)))
    let hacl_FFDHE_ffdhe_secret_to_public_precomp =
      foreign "Hacl_FFDHE_ffdhe_secret_to_public_precomp"
        (spec_FFDHE_ffdhe_alg @->
           ((ptr uint64_t) @->
              (ocaml_bytes @-> (ocaml_bytes @-> (returning void)))))
    let hacl_FFDHE_ffdhe_secret_to_public =
      foreign "Hacl_FFDHE_ffdhe_secret_to_public"
        (spec_FFDHE_ffdhe_alg @->
           (ocaml_bytes @-> (ocaml_bytes @-> (returning void))))
    let hacl_FFDHE_ffdhe_shared_secret_precomp =
      foreign "Hacl_FFDHE_ffdhe_shared_secret_precomp"
        (spec_FFDHE_ffdhe_alg @->
           ((ptr uint64_t) @->
              (ocaml_bytes @->
                 (ocaml_bytes @-> (ocaml_bytes @-> (returning uint64_t))))))
    let hacl_FFDHE_ffdhe_shared_secret =
      foreign "Hacl_FFDHE_ffdhe_shared_secret"
        (spec_FFDHE_ffdhe_alg @->
           (ocaml_bytes @->
              (ocaml_bytes @-> (ocaml_bytes @-> (returning uint64_t)))))
  end