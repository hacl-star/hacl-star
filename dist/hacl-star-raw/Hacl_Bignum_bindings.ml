open Ctypes
module Bindings(F:Cstubs.FOREIGN) =
  struct
    open F
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
    type hacl_Bignum_MontArithmetic_bn_mont_ctx_u32 =
      [ `hacl_Bignum_MontArithmetic_bn_mont_ctx_u32 ] structure
    let (hacl_Bignum_MontArithmetic_bn_mont_ctx_u32 :
      [ `hacl_Bignum_MontArithmetic_bn_mont_ctx_u32 ] structure typ) =
      structure "Hacl_Bignum_MontArithmetic_bn_mont_ctx_u32_s"
    let hacl_Bignum_MontArithmetic_bn_mont_ctx_u32_len =
      field hacl_Bignum_MontArithmetic_bn_mont_ctx_u32 "len" uint32_t
    let hacl_Bignum_MontArithmetic_bn_mont_ctx_u32_n =
      field hacl_Bignum_MontArithmetic_bn_mont_ctx_u32 "n" (ptr uint32_t)
    let hacl_Bignum_MontArithmetic_bn_mont_ctx_u32_mu =
      field hacl_Bignum_MontArithmetic_bn_mont_ctx_u32 "mu" uint32_t
    let hacl_Bignum_MontArithmetic_bn_mont_ctx_u32_r2 =
      field hacl_Bignum_MontArithmetic_bn_mont_ctx_u32 "r2" (ptr uint32_t)
    let _ = seal hacl_Bignum_MontArithmetic_bn_mont_ctx_u32
    type hacl_Bignum_MontArithmetic_bn_mont_ctx_u64 =
      [ `hacl_Bignum_MontArithmetic_bn_mont_ctx_u64 ] structure
    let (hacl_Bignum_MontArithmetic_bn_mont_ctx_u64 :
      [ `hacl_Bignum_MontArithmetic_bn_mont_ctx_u64 ] structure typ) =
      structure "Hacl_Bignum_MontArithmetic_bn_mont_ctx_u64_s"
    let hacl_Bignum_MontArithmetic_bn_mont_ctx_u64_len =
      field hacl_Bignum_MontArithmetic_bn_mont_ctx_u64 "len" uint32_t
    let hacl_Bignum_MontArithmetic_bn_mont_ctx_u64_n =
      field hacl_Bignum_MontArithmetic_bn_mont_ctx_u64 "n" (ptr uint64_t)
    let hacl_Bignum_MontArithmetic_bn_mont_ctx_u64_mu =
      field hacl_Bignum_MontArithmetic_bn_mont_ctx_u64 "mu" uint64_t
    let hacl_Bignum_MontArithmetic_bn_mont_ctx_u64_r2 =
      field hacl_Bignum_MontArithmetic_bn_mont_ctx_u64 "r2" (ptr uint64_t)
    let _ = seal hacl_Bignum_MontArithmetic_bn_mont_ctx_u64
  end