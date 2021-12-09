open Ctypes
module Bindings(F:Cstubs.FOREIGN) =
  struct
    open F
    let hacl_Bignum256_add =
      foreign "Hacl_Bignum256_add"
        ((ptr uint64_t) @->
           ((ptr uint64_t) @-> ((ptr uint64_t) @-> (returning uint64_t))))
    let hacl_Bignum256_sub =
      foreign "Hacl_Bignum256_sub"
        ((ptr uint64_t) @->
           ((ptr uint64_t) @-> ((ptr uint64_t) @-> (returning uint64_t))))
    let hacl_Bignum256_add_mod =
      foreign "Hacl_Bignum256_add_mod"
        ((ptr uint64_t) @->
           ((ptr uint64_t) @->
              ((ptr uint64_t) @-> ((ptr uint64_t) @-> (returning void)))))
    let hacl_Bignum256_sub_mod =
      foreign "Hacl_Bignum256_sub_mod"
        ((ptr uint64_t) @->
           ((ptr uint64_t) @->
              ((ptr uint64_t) @-> ((ptr uint64_t) @-> (returning void)))))
    let hacl_Bignum256_mul =
      foreign "Hacl_Bignum256_mul"
        ((ptr uint64_t) @->
           ((ptr uint64_t) @-> ((ptr uint64_t) @-> (returning void))))
    let hacl_Bignum256_sqr =
      foreign "Hacl_Bignum256_sqr"
        ((ptr uint64_t) @-> ((ptr uint64_t) @-> (returning void)))
    let hacl_Bignum256_mod =
      foreign "Hacl_Bignum256_mod"
        ((ptr uint64_t) @->
           ((ptr uint64_t) @-> ((ptr uint64_t) @-> (returning bool))))
    let hacl_Bignum256_mod_exp_vartime =
      foreign "Hacl_Bignum256_mod_exp_vartime"
        ((ptr uint64_t) @->
           ((ptr uint64_t) @->
              (uint32_t @->
                 ((ptr uint64_t) @-> ((ptr uint64_t) @-> (returning bool))))))
    let hacl_Bignum256_mod_exp_consttime =
      foreign "Hacl_Bignum256_mod_exp_consttime"
        ((ptr uint64_t) @->
           ((ptr uint64_t) @->
              (uint32_t @->
                 ((ptr uint64_t) @-> ((ptr uint64_t) @-> (returning bool))))))
    let hacl_Bignum256_mod_inv_prime_vartime =
      foreign "Hacl_Bignum256_mod_inv_prime_vartime"
        ((ptr uint64_t) @->
           ((ptr uint64_t) @-> ((ptr uint64_t) @-> (returning bool))))
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
    let hacl_Bignum256_mont_ctx_init =
      foreign "Hacl_Bignum256_mont_ctx_init"
        ((ptr uint64_t) @->
           (returning (ptr hacl_Bignum_MontArithmetic_bn_mont_ctx_u64)))
    let hacl_Bignum256_mont_ctx_free =
      foreign "Hacl_Bignum256_mont_ctx_free"
        ((ptr hacl_Bignum_MontArithmetic_bn_mont_ctx_u64) @->
           (returning void))
    let hacl_Bignum256_mod_precomp =
      foreign "Hacl_Bignum256_mod_precomp"
        ((ptr hacl_Bignum_MontArithmetic_bn_mont_ctx_u64) @->
           ((ptr uint64_t) @-> ((ptr uint64_t) @-> (returning void))))
    let hacl_Bignum256_mod_exp_vartime_precomp =
      foreign "Hacl_Bignum256_mod_exp_vartime_precomp"
        ((ptr hacl_Bignum_MontArithmetic_bn_mont_ctx_u64) @->
           ((ptr uint64_t) @->
              (uint32_t @->
                 ((ptr uint64_t) @-> ((ptr uint64_t) @-> (returning void))))))
    let hacl_Bignum256_mod_exp_consttime_precomp =
      foreign "Hacl_Bignum256_mod_exp_consttime_precomp"
        ((ptr hacl_Bignum_MontArithmetic_bn_mont_ctx_u64) @->
           ((ptr uint64_t) @->
              (uint32_t @->
                 ((ptr uint64_t) @-> ((ptr uint64_t) @-> (returning void))))))
    let hacl_Bignum256_mod_inv_prime_vartime_precomp =
      foreign "Hacl_Bignum256_mod_inv_prime_vartime_precomp"
        ((ptr hacl_Bignum_MontArithmetic_bn_mont_ctx_u64) @->
           ((ptr uint64_t) @-> ((ptr uint64_t) @-> (returning void))))
    let hacl_Bignum256_new_bn_from_bytes_be =
      foreign "Hacl_Bignum256_new_bn_from_bytes_be"
        (uint32_t @-> (ocaml_bytes @-> (returning (ptr uint64_t))))
    let hacl_Bignum256_new_bn_from_bytes_le =
      foreign "Hacl_Bignum256_new_bn_from_bytes_le"
        (uint32_t @-> (ocaml_bytes @-> (returning (ptr uint64_t))))
    let hacl_Bignum256_bn_to_bytes_be =
      foreign "Hacl_Bignum256_bn_to_bytes_be"
        ((ptr uint64_t) @-> (ocaml_bytes @-> (returning void)))
    let hacl_Bignum256_bn_to_bytes_le =
      foreign "Hacl_Bignum256_bn_to_bytes_le"
        ((ptr uint64_t) @-> (ocaml_bytes @-> (returning void)))
    let hacl_Bignum256_lt_mask =
      foreign "Hacl_Bignum256_lt_mask"
        ((ptr uint64_t) @-> ((ptr uint64_t) @-> (returning uint64_t)))
    let hacl_Bignum256_eq_mask =
      foreign "Hacl_Bignum256_eq_mask"
        ((ptr uint64_t) @-> ((ptr uint64_t) @-> (returning uint64_t)))
  end