open Ctypes
module Bindings(F:Cstubs.FOREIGN) =
  struct
    open F
    module Hacl_Streaming_Types_applied =
      (Hacl_Streaming_Types_bindings.Bindings)(Hacl_Streaming_Types_stubs)
    open Hacl_Streaming_Types_applied
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
                                   (ocaml_bytes @-> (returning bool)))))))))))
    let hacl_RSAPSS_rsapss_verify =
      foreign "Hacl_RSAPSS_rsapss_verify"
        (spec_Hash_Definitions_hash_alg @->
           (uint32_t @->
              (uint32_t @->
                 ((ptr uint64_t) @->
                    (uint32_t @->
                       (uint32_t @->
                          (ocaml_bytes @->
                             (uint32_t @-> (ocaml_bytes @-> (returning bool))))))))))
    let hacl_RSAPSS_new_rsapss_load_pkey =
      foreign "Hacl_RSAPSS_new_rsapss_load_pkey"
        (uint32_t @->
           (uint32_t @->
              (ocaml_bytes @-> (ocaml_bytes @-> (returning (ptr uint64_t))))))
    let hacl_RSAPSS_new_rsapss_load_skey =
      foreign "Hacl_RSAPSS_new_rsapss_load_skey"
        (uint32_t @->
           (uint32_t @->
              (uint32_t @->
                 (ocaml_bytes @->
                    (ocaml_bytes @->
                       (ocaml_bytes @-> (returning (ptr uint64_t))))))))
    let hacl_RSAPSS_rsapss_skey_sign =
      foreign "Hacl_RSAPSS_rsapss_skey_sign"
        (spec_Hash_Definitions_hash_alg @->
           (uint32_t @->
              (uint32_t @->
                 (uint32_t @->
                    (ocaml_bytes @->
                       (ocaml_bytes @->
                          (ocaml_bytes @->
                             (uint32_t @->
                                (ocaml_bytes @->
                                   (uint32_t @->
                                      (ocaml_bytes @->
                                         (ocaml_bytes @-> (returning bool)))))))))))))
    let hacl_RSAPSS_rsapss_pkey_verify =
      foreign "Hacl_RSAPSS_rsapss_pkey_verify"
        (spec_Hash_Definitions_hash_alg @->
           (uint32_t @->
              (uint32_t @->
                 (ocaml_bytes @->
                    (ocaml_bytes @->
                       (uint32_t @->
                          (uint32_t @->
                             (ocaml_bytes @->
                                (uint32_t @->
                                   (ocaml_bytes @-> (returning bool)))))))))))
    let hacl_RSAPSS_mgf_hash =
      foreign "Hacl_RSAPSS_mgf_hash"
        (spec_Hash_Definitions_hash_alg @->
           (uint32_t @->
              (ocaml_bytes @->
                 (uint32_t @-> (ocaml_bytes @-> (returning void))))))
  end