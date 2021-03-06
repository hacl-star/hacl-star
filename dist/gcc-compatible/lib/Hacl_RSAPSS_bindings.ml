open Ctypes
module Bindings(F:Cstubs.FOREIGN) =
  struct
    open F
    module Hacl_Spec_applied = (Hacl_Spec_bindings.Bindings)(Hacl_Spec_stubs)
    open Hacl_Spec_applied
    let hacl_Impl_RSAPSS_MGF_hash_len =
      foreign "Hacl_Impl_RSAPSS_MGF_hash_len"
        (spec_Hash_Definitions_hash_alg @-> (returning uint32_t))
    let hacl_Impl_RSAPSS_Keys_check_modulus_u64 =
      foreign "Hacl_Impl_RSAPSS_Keys_check_modulus_u64"
        (uint32_t @-> ((ptr uint64_t) @-> (returning uint64_t)))
    let hacl_Impl_RSAPSS_Keys_check_exponent_u64 =
      foreign "Hacl_Impl_RSAPSS_Keys_check_exponent_u64"
        (uint32_t @-> ((ptr uint64_t) @-> (returning uint64_t)))
    let hacl_Impl_RSAPSS_Padding_pss_encode =
      foreign "Hacl_Impl_RSAPSS_Padding_pss_encode"
        (spec_Hash_Definitions_hash_alg @->
           (uint32_t @->
              (ocaml_bytes @->
                 (uint32_t @->
                    (ocaml_bytes @->
                       (uint32_t @-> (ocaml_bytes @-> (returning void))))))))
    let hacl_Impl_RSAPSS_Padding_pss_verify =
      foreign "Hacl_Impl_RSAPSS_Padding_pss_verify"
        (spec_Hash_Definitions_hash_alg @->
           (uint32_t @->
              (uint32_t @->
                 (ocaml_bytes @->
                    (uint32_t @-> (ocaml_bytes @-> (returning bool)))))))
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
  end