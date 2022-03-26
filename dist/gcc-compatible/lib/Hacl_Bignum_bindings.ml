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
    let hacl_Bignum_Lib_bn_get_top_index_u32 =
      foreign "Hacl_Bignum_Lib_bn_get_top_index_u32"
        (uint32_t @-> ((ptr uint32_t) @-> (returning uint32_t)))
    let hacl_Bignum_Lib_bn_get_top_index_u64 =
      foreign "Hacl_Bignum_Lib_bn_get_top_index_u64"
        (uint32_t @-> ((ptr uint64_t) @-> (returning uint64_t)))
    let hacl_Bignum_Addition_bn_sub_eq_len_u32 =
      foreign "Hacl_Bignum_Addition_bn_sub_eq_len_u32"
        (uint32_t @->
           ((ptr uint32_t) @->
              ((ptr uint32_t) @-> ((ptr uint32_t) @-> (returning uint32_t)))))
    let hacl_Bignum_Addition_bn_sub_eq_len_u64 =
      foreign "Hacl_Bignum_Addition_bn_sub_eq_len_u64"
        (uint32_t @->
           ((ptr uint64_t) @->
              ((ptr uint64_t) @-> ((ptr uint64_t) @-> (returning uint64_t)))))
    let hacl_Bignum_Addition_bn_add_eq_len_u32 =
      foreign "Hacl_Bignum_Addition_bn_add_eq_len_u32"
        (uint32_t @->
           ((ptr uint32_t) @->
              ((ptr uint32_t) @-> ((ptr uint32_t) @-> (returning uint32_t)))))
    let hacl_Bignum_Addition_bn_add_eq_len_u64 =
      foreign "Hacl_Bignum_Addition_bn_add_eq_len_u64"
        (uint32_t @->
           ((ptr uint64_t) @->
              ((ptr uint64_t) @-> ((ptr uint64_t) @-> (returning uint64_t)))))
    let hacl_Bignum_Karatsuba_bn_karatsuba_mul_uint32 =
      foreign "Hacl_Bignum_Karatsuba_bn_karatsuba_mul_uint32"
        (uint32_t @->
           ((ptr uint32_t) @->
              ((ptr uint32_t) @->
                 ((ptr uint32_t) @-> ((ptr uint32_t) @-> (returning void))))))
    let hacl_Bignum_Karatsuba_bn_karatsuba_mul_uint64 =
      foreign "Hacl_Bignum_Karatsuba_bn_karatsuba_mul_uint64"
        (uint32_t @->
           ((ptr uint64_t) @->
              ((ptr uint64_t) @->
                 ((ptr uint64_t) @-> ((ptr uint64_t) @-> (returning void))))))
    let hacl_Bignum_Karatsuba_bn_karatsuba_sqr_uint32 =
      foreign "Hacl_Bignum_Karatsuba_bn_karatsuba_sqr_uint32"
        (uint32_t @->
           ((ptr uint32_t) @->
              ((ptr uint32_t) @-> ((ptr uint32_t) @-> (returning void)))))
    let hacl_Bignum_Karatsuba_bn_karatsuba_sqr_uint64 =
      foreign "Hacl_Bignum_Karatsuba_bn_karatsuba_sqr_uint64"
        (uint32_t @->
           ((ptr uint64_t) @->
              ((ptr uint64_t) @-> ((ptr uint64_t) @-> (returning void)))))
    let hacl_Bignum_bn_add_mod_n_u32 =
      foreign "Hacl_Bignum_bn_add_mod_n_u32"
        (uint32_t @->
           ((ptr uint32_t) @->
              ((ptr uint32_t) @->
                 ((ptr uint32_t) @-> ((ptr uint32_t) @-> (returning void))))))
    let hacl_Bignum_bn_add_mod_n_u64 =
      foreign "Hacl_Bignum_bn_add_mod_n_u64"
        (uint32_t @->
           ((ptr uint64_t) @->
              ((ptr uint64_t) @->
                 ((ptr uint64_t) @-> ((ptr uint64_t) @-> (returning void))))))
    let hacl_Bignum_bn_sub_mod_n_u32 =
      foreign "Hacl_Bignum_bn_sub_mod_n_u32"
        (uint32_t @->
           ((ptr uint32_t) @->
              ((ptr uint32_t) @->
                 ((ptr uint32_t) @-> ((ptr uint32_t) @-> (returning void))))))
    let hacl_Bignum_bn_sub_mod_n_u64 =
      foreign "Hacl_Bignum_bn_sub_mod_n_u64"
        (uint32_t @->
           ((ptr uint64_t) @->
              ((ptr uint64_t) @->
                 ((ptr uint64_t) @-> ((ptr uint64_t) @-> (returning void))))))
    let hacl_Bignum_ModInvLimb_mod_inv_uint32 =
      foreign "Hacl_Bignum_ModInvLimb_mod_inv_uint32"
        (uint32_t @-> (returning uint32_t))
    let hacl_Bignum_ModInvLimb_mod_inv_uint64 =
      foreign "Hacl_Bignum_ModInvLimb_mod_inv_uint64"
        (uint64_t @-> (returning uint64_t))
    let hacl_Bignum_Montgomery_bn_check_modulus_u32 =
      foreign "Hacl_Bignum_Montgomery_bn_check_modulus_u32"
        (uint32_t @-> ((ptr uint32_t) @-> (returning uint32_t)))
    let hacl_Bignum_Montgomery_bn_precomp_r2_mod_n_u32 =
      foreign "Hacl_Bignum_Montgomery_bn_precomp_r2_mod_n_u32"
        (uint32_t @->
           (uint32_t @->
              ((ptr uint32_t) @-> ((ptr uint32_t) @-> (returning void)))))
    let hacl_Bignum_Montgomery_bn_mont_reduction_u32 =
      foreign "Hacl_Bignum_Montgomery_bn_mont_reduction_u32"
        (uint32_t @->
           ((ptr uint32_t) @->
              (uint32_t @->
                 ((ptr uint32_t) @-> ((ptr uint32_t) @-> (returning void))))))
    let hacl_Bignum_Montgomery_bn_to_mont_u32 =
      foreign "Hacl_Bignum_Montgomery_bn_to_mont_u32"
        (uint32_t @->
           ((ptr uint32_t) @->
              (uint32_t @->
                 ((ptr uint32_t) @->
                    ((ptr uint32_t) @-> ((ptr uint32_t) @-> (returning void)))))))
    let hacl_Bignum_Montgomery_bn_from_mont_u32 =
      foreign "Hacl_Bignum_Montgomery_bn_from_mont_u32"
        (uint32_t @->
           ((ptr uint32_t) @->
              (uint32_t @->
                 ((ptr uint32_t) @-> ((ptr uint32_t) @-> (returning void))))))
    let hacl_Bignum_Montgomery_bn_mont_mul_u32 =
      foreign "Hacl_Bignum_Montgomery_bn_mont_mul_u32"
        (uint32_t @->
           ((ptr uint32_t) @->
              (uint32_t @->
                 ((ptr uint32_t) @->
                    ((ptr uint32_t) @-> ((ptr uint32_t) @-> (returning void)))))))
    let hacl_Bignum_Montgomery_bn_mont_sqr_u32 =
      foreign "Hacl_Bignum_Montgomery_bn_mont_sqr_u32"
        (uint32_t @->
           ((ptr uint32_t) @->
              (uint32_t @->
                 ((ptr uint32_t) @-> ((ptr uint32_t) @-> (returning void))))))
    let hacl_Bignum_Montgomery_bn_check_modulus_u64 =
      foreign "Hacl_Bignum_Montgomery_bn_check_modulus_u64"
        (uint32_t @-> ((ptr uint64_t) @-> (returning uint64_t)))
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
    let hacl_Bignum_Montgomery_bn_to_mont_u64 =
      foreign "Hacl_Bignum_Montgomery_bn_to_mont_u64"
        (uint32_t @->
           ((ptr uint64_t) @->
              (uint64_t @->
                 ((ptr uint64_t) @->
                    ((ptr uint64_t) @-> ((ptr uint64_t) @-> (returning void)))))))
    let hacl_Bignum_Montgomery_bn_from_mont_u64 =
      foreign "Hacl_Bignum_Montgomery_bn_from_mont_u64"
        (uint32_t @->
           ((ptr uint64_t) @->
              (uint64_t @->
                 ((ptr uint64_t) @-> ((ptr uint64_t) @-> (returning void))))))
    let hacl_Bignum_Montgomery_bn_mont_mul_u64 =
      foreign "Hacl_Bignum_Montgomery_bn_mont_mul_u64"
        (uint32_t @->
           ((ptr uint64_t) @->
              (uint64_t @->
                 ((ptr uint64_t) @->
                    ((ptr uint64_t) @-> ((ptr uint64_t) @-> (returning void)))))))
    let hacl_Bignum_Montgomery_bn_mont_sqr_u64 =
      foreign "Hacl_Bignum_Montgomery_bn_mont_sqr_u64"
        (uint32_t @->
           ((ptr uint64_t) @->
              (uint64_t @->
                 ((ptr uint64_t) @-> ((ptr uint64_t) @-> (returning void))))))
    let hacl_Bignum_Exponentiation_bn_check_mod_exp_u32 =
      foreign "Hacl_Bignum_Exponentiation_bn_check_mod_exp_u32"
        (uint32_t @->
           ((ptr uint32_t) @->
              ((ptr uint32_t) @->
                 (uint32_t @-> ((ptr uint32_t) @-> (returning uint32_t))))))
    let hacl_Bignum_Exponentiation_bn_mod_exp_vartime_precomp_u32 =
      foreign "Hacl_Bignum_Exponentiation_bn_mod_exp_vartime_precomp_u32"
        (uint32_t @->
           ((ptr uint32_t) @->
              (uint32_t @->
                 ((ptr uint32_t) @->
                    ((ptr uint32_t) @->
                       (uint32_t @->
                          ((ptr uint32_t) @->
                             ((ptr uint32_t) @-> (returning void)))))))))
    let hacl_Bignum_Exponentiation_bn_mod_exp_consttime_precomp_u32 =
      foreign "Hacl_Bignum_Exponentiation_bn_mod_exp_consttime_precomp_u32"
        (uint32_t @->
           ((ptr uint32_t) @->
              (uint32_t @->
                 ((ptr uint32_t) @->
                    ((ptr uint32_t) @->
                       (uint32_t @->
                          ((ptr uint32_t) @->
                             ((ptr uint32_t) @-> (returning void)))))))))
    let hacl_Bignum_Exponentiation_bn_mod_exp_vartime_u32 =
      foreign "Hacl_Bignum_Exponentiation_bn_mod_exp_vartime_u32"
        (uint32_t @->
           (uint32_t @->
              ((ptr uint32_t) @->
                 ((ptr uint32_t) @->
                    (uint32_t @->
                       ((ptr uint32_t) @->
                          ((ptr uint32_t) @-> (returning void))))))))
    let hacl_Bignum_Exponentiation_bn_mod_exp_consttime_u32 =
      foreign "Hacl_Bignum_Exponentiation_bn_mod_exp_consttime_u32"
        (uint32_t @->
           (uint32_t @->
              ((ptr uint32_t) @->
                 ((ptr uint32_t) @->
                    (uint32_t @->
                       ((ptr uint32_t) @->
                          ((ptr uint32_t) @-> (returning void))))))))
    let hacl_Bignum_Exponentiation_bn_check_mod_exp_u64 =
      foreign "Hacl_Bignum_Exponentiation_bn_check_mod_exp_u64"
        (uint32_t @->
           ((ptr uint64_t) @->
              ((ptr uint64_t) @->
                 (uint32_t @-> ((ptr uint64_t) @-> (returning uint64_t))))))
    let hacl_Bignum_Exponentiation_bn_mod_exp_vartime_precomp_u64 =
      foreign "Hacl_Bignum_Exponentiation_bn_mod_exp_vartime_precomp_u64"
        (uint32_t @->
           ((ptr uint64_t) @->
              (uint64_t @->
                 ((ptr uint64_t) @->
                    ((ptr uint64_t) @->
                       (uint32_t @->
                          ((ptr uint64_t) @->
                             ((ptr uint64_t) @-> (returning void)))))))))
    let hacl_Bignum_Exponentiation_bn_mod_exp_consttime_precomp_u64 =
      foreign "Hacl_Bignum_Exponentiation_bn_mod_exp_consttime_precomp_u64"
        (uint32_t @->
           ((ptr uint64_t) @->
              (uint64_t @->
                 ((ptr uint64_t) @->
                    ((ptr uint64_t) @->
                       (uint32_t @->
                          ((ptr uint64_t) @->
                             ((ptr uint64_t) @-> (returning void)))))))))
    let hacl_Bignum_Exponentiation_bn_mod_exp_vartime_u64 =
      foreign "Hacl_Bignum_Exponentiation_bn_mod_exp_vartime_u64"
        (uint32_t @->
           (uint32_t @->
              ((ptr uint64_t) @->
                 ((ptr uint64_t) @->
                    (uint32_t @->
                       ((ptr uint64_t) @->
                          ((ptr uint64_t) @-> (returning void))))))))
    let hacl_Bignum_Exponentiation_bn_mod_exp_consttime_u64 =
      foreign "Hacl_Bignum_Exponentiation_bn_mod_exp_consttime_u64"
        (uint32_t @->
           (uint32_t @->
              ((ptr uint64_t) @->
                 ((ptr uint64_t) @->
                    (uint32_t @->
                       ((ptr uint64_t) @->
                          ((ptr uint64_t) @-> (returning void))))))))
  end