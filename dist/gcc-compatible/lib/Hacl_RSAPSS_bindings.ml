open Ctypes
module Bindings(F:Cstubs.FOREIGN) =
  struct
    open F
    let hacl_Bignum_Multiplication_mul_carry_add_u64_st =
      foreign "Hacl_Bignum_Multiplication_mul_carry_add_u64_st"
        (uint64_t @->
           (uint64_t @->
              (uint64_t @-> ((ptr uint64_t) @-> (returning uint64_t)))))
    let hacl_Bignum_bn_is_bit_set =
      foreign "Hacl_Bignum_bn_is_bit_set"
        (uint32_t @-> ((ptr uint64_t) @-> (uint32_t @-> (returning bool))))
    let hacl_Bignum_Montgomery_mod_inv_u64 =
      foreign "Hacl_Bignum_Montgomery_mod_inv_u64"
        (uint64_t @-> (returning uint64_t))
    let hacl_RSAPSS_rsapss_sign =
      foreign "Hacl_RSAPSS_rsapss_sign"
        (uint32_t @->
           (uint32_t @->
              (uint32_t @->
                 ((ptr uint64_t) @->
                    (uint32_t @->
                       (ocaml_bytes @->
                          (uint32_t @->
                             (ocaml_bytes @->
                                (ocaml_bytes @-> (returning void))))))))))
    let hacl_RSAPSS_rsapss_verify =
      foreign "Hacl_RSAPSS_rsapss_verify"
        (uint32_t @->
           (uint32_t @->
              ((ptr uint64_t) @->
                 (uint32_t @->
                    (ocaml_bytes @->
                       (uint32_t @-> (ocaml_bytes @-> (returning bool))))))))
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