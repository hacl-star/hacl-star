open Ctypes
module Bindings(F:Cstubs.FOREIGN) =
  struct
    open F
    let hacl_Bignum_Convert_bn_from_bytes_be_uint64 =
      foreign "Hacl_Bignum_Convert_bn_from_bytes_be_uint64"
        (uint32_t @-> (ocaml_bytes @-> ((ptr uint64_t) @-> (returning void))))
    let hacl_Bignum_Convert_bn_to_bytes_be_uint64 =
      foreign "Hacl_Bignum_Convert_bn_to_bytes_be_uint64"
        (uint32_t @-> ((ptr uint64_t) @-> (ocaml_bytes @-> (returning void))))
    let hacl_Bignum_Base_mul_wide_add2_u64 =
      foreign "Hacl_Bignum_Base_mul_wide_add2_u64"
        (uint64_t @->
           (uint64_t @->
              (uint64_t @-> ((ptr uint64_t) @-> (returning uint64_t)))))
    let hacl_Bignum_Lib_bn_get_top_index_u64 =
      foreign "Hacl_Bignum_Lib_bn_get_top_index_u64"
        (uint32_t @-> ((ptr uint64_t) @-> (returning uint64_t)))
    let hacl_Bignum_Karatsuba_bn_karatsuba_mul_uint64 =
      foreign "Hacl_Bignum_Karatsuba_bn_karatsuba_mul_uint64"
        (uint32_t @->
           ((ptr uint64_t) @->
              ((ptr uint64_t) @->
                 ((ptr uint64_t) @-> ((ptr uint64_t) @-> (returning void))))))
    let hacl_Bignum_Karatsuba_bn_karatsuba_sqr_uint64 =
      foreign "Hacl_Bignum_Karatsuba_bn_karatsuba_sqr_uint64"
        (uint32_t @->
           ((ptr uint64_t) @->
              ((ptr uint64_t) @-> ((ptr uint64_t) @-> (returning void)))))
    let hacl_Bignum_bn_add_mod_n_u64 =
      foreign "Hacl_Bignum_bn_add_mod_n_u64"
        (uint32_t @->
           ((ptr uint64_t) @->
              ((ptr uint64_t) @->
                 ((ptr uint64_t) @-> ((ptr uint64_t) @-> (returning void))))))
    let hacl_Bignum_ModInvLimb_mod_inv_uint64 =
      foreign "Hacl_Bignum_ModInvLimb_mod_inv_uint64"
        (uint64_t @-> (returning uint64_t))
    let hacl_Bignum_Montgomery_bn_precomp_r2_mod_n_u64 =
      foreign "Hacl_Bignum_Montgomery_bn_precomp_r2_mod_n_u64"
        (uint32_t @->
           (uint32_t @->
              ((ptr uint64_t) @-> ((ptr uint64_t) @-> (returning void)))))
    let hacl_Bignum_Montgomery_bn_mont_reduction_u64 =
      foreign "Hacl_Bignum_Montgomery_bn_mont_reduction_u64"
        (uint32_t @->
           ((ptr uint64_t) @->
              (uint64_t @->
                 ((ptr uint64_t) @-> ((ptr uint64_t) @-> (returning void))))))
    let hacl_Bignum_Exponentiation_bn_mod_exp_precompr2_u64 =
      foreign "Hacl_Bignum_Exponentiation_bn_mod_exp_precompr2_u64"
        (uint32_t @->
           ((ptr uint64_t) @->
              ((ptr uint64_t) @->
                 (uint32_t @->
                    ((ptr uint64_t) @->
                       ((ptr uint64_t) @->
                          ((ptr uint64_t) @-> (returning void))))))))
    let hacl_Bignum_Exponentiation_bn_mod_exp_mont_ladder_precompr2_u64 =
      foreign
        "Hacl_Bignum_Exponentiation_bn_mod_exp_mont_ladder_precompr2_u64"
        (uint32_t @->
           ((ptr uint64_t) @->
              ((ptr uint64_t) @->
                 (uint32_t @->
                    ((ptr uint64_t) @->
                       ((ptr uint64_t) @->
                          ((ptr uint64_t) @-> (returning void))))))))
  end