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
    let hacl_Bignum_Convert_bn_from_bytes_be =
      foreign "Hacl_Bignum_Convert_bn_from_bytes_be"
        (uint32_t @-> (ocaml_bytes @-> ((ptr uint64_t) @-> (returning void))))
    let hacl_Bignum_Convert_bn_from_bytes_le =
      foreign "Hacl_Bignum_Convert_bn_from_bytes_le"
        (uint32_t @-> (ocaml_bytes @-> ((ptr uint64_t) @-> (returning void))))
    let hacl_Bignum_Convert_bn_to_bytes_be =
      foreign "Hacl_Bignum_Convert_bn_to_bytes_be"
        (uint32_t @-> ((ptr uint64_t) @-> (ocaml_bytes @-> (returning void))))
    let hacl_Bignum_Convert_bn_to_bytes_le =
      foreign "Hacl_Bignum_Convert_bn_to_bytes_le"
        (uint32_t @-> ((ptr uint64_t) @-> (ocaml_bytes @-> (returning void))))
  end