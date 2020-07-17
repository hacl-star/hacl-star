open Ctypes
module Bindings(F:Cstubs.FOREIGN) =
  struct
    open F
    module Hacl_Spec_applied = (Hacl_Spec_bindings.Bindings)(Hacl_Spec_stubs)
    open Hacl_Spec_applied
    let hacl_RSAPSS_rsapss_sign =
      foreign "Hacl_RSAPSS_rsapss_sign"
        (spec_Hash_Definitions_hash_alg @->
           (uint32_t @->
              (uint32_t @->
                 (uint32_t @->
                    ((ptr uint64_t) @->
                       (uint32_t @->
                          (ocaml_bytes @->
                             (uint32_t @->
                                (ocaml_bytes @->
                                   (ocaml_bytes @-> (returning void)))))))))))
    let hacl_RSAPSS_rsapss_verify =
      foreign "Hacl_RSAPSS_rsapss_verify"
        (spec_Hash_Definitions_hash_alg @->
           (uint32_t @->
              (uint32_t @->
                 ((ptr uint64_t) @->
                    (uint32_t @->
                       (ocaml_bytes @->
                          (uint32_t @-> (ocaml_bytes @-> (returning bool)))))))))
  end