open Ctypes
module Bindings(F:Cstubs.FOREIGN) =
  struct
    open F
    module Hacl_Bignum256_applied =
      (Hacl_Bignum256_bindings.Bindings)(Hacl_Bignum256_stubs)
    open Hacl_Bignum256_applied
    let hacl_Bignum64_add =
      foreign "Hacl_Bignum64_add"
        (uint32_t @->
           ((ptr uint64_t) @->
              ((ptr uint64_t) @-> ((ptr uint64_t) @-> (returning uint64_t)))))
    let hacl_Bignum64_sub =
      foreign "Hacl_Bignum64_sub"
        (uint32_t @->
           ((ptr uint64_t) @->
              ((ptr uint64_t) @-> ((ptr uint64_t) @-> (returning uint64_t)))))
    let hacl_Bignum64_add_mod =
      foreign "Hacl_Bignum64_add_mod"
        (uint32_t @->
           ((ptr uint64_t) @->
              ((ptr uint64_t) @->
                 ((ptr uint64_t) @-> ((ptr uint64_t) @-> (returning void))))))
    let hacl_Bignum64_sub_mod =
      foreign "Hacl_Bignum64_sub_mod"
        (uint32_t @->
           ((ptr uint64_t) @->
              ((ptr uint64_t) @->
                 ((ptr uint64_t) @-> ((ptr uint64_t) @-> (returning void))))))
    let hacl_Bignum64_mul =
      foreign "Hacl_Bignum64_mul"
        (uint32_t @->
           ((ptr uint64_t) @->
              ((ptr uint64_t) @-> ((ptr uint64_t) @-> (returning void)))))
    let hacl_Bignum64_sqr =
      foreign "Hacl_Bignum64_sqr"
        (uint32_t @->
           ((ptr uint64_t) @-> ((ptr uint64_t) @-> (returning void))))
    let hacl_Bignum64_mod =
      foreign "Hacl_Bignum64_mod"
        (uint32_t @->
           ((ptr uint64_t) @->
              ((ptr uint64_t) @-> ((ptr uint64_t) @-> (returning bool)))))
    let hacl_Bignum64_mod_exp_vartime =
      foreign "Hacl_Bignum64_mod_exp_vartime"
        (uint32_t @->
           ((ptr uint64_t) @->
              ((ptr uint64_t) @->
                 (uint32_t @->
                    ((ptr uint64_t) @-> ((ptr uint64_t) @-> (returning bool)))))))
    let hacl_Bignum64_mod_exp_consttime =
      foreign "Hacl_Bignum64_mod_exp_consttime"
        (uint32_t @->
           ((ptr uint64_t) @->
              ((ptr uint64_t) @->
                 (uint32_t @->
                    ((ptr uint64_t) @-> ((ptr uint64_t) @-> (returning bool)))))))
    let hacl_Bignum64_mod_inv_prime_vartime =
      foreign "Hacl_Bignum64_mod_inv_prime_vartime"
        (uint32_t @->
           ((ptr uint64_t) @->
              ((ptr uint64_t) @-> ((ptr uint64_t) @-> (returning bool)))))
    let hacl_Bignum64_mont_ctx_init =
      foreign "Hacl_Bignum64_mont_ctx_init"
        (uint32_t @->
           ((ptr uint64_t) @->
              (returning (ptr hacl_Bignum_MontArithmetic_bn_mont_ctx_u64))))
    let hacl_Bignum64_mont_ctx_free =
      foreign "Hacl_Bignum64_mont_ctx_free"
        ((ptr hacl_Bignum_MontArithmetic_bn_mont_ctx_u64) @->
           (returning void))
    let hacl_Bignum64_mod_precomp =
      foreign "Hacl_Bignum64_mod_precomp"
        ((ptr hacl_Bignum_MontArithmetic_bn_mont_ctx_u64) @->
           ((ptr uint64_t) @-> ((ptr uint64_t) @-> (returning void))))
    let hacl_Bignum64_mod_exp_vartime_precomp =
      foreign "Hacl_Bignum64_mod_exp_vartime_precomp"
        ((ptr hacl_Bignum_MontArithmetic_bn_mont_ctx_u64) @->
           ((ptr uint64_t) @->
              (uint32_t @->
                 ((ptr uint64_t) @-> ((ptr uint64_t) @-> (returning void))))))
    let hacl_Bignum64_mod_exp_consttime_precomp =
      foreign "Hacl_Bignum64_mod_exp_consttime_precomp"
        ((ptr hacl_Bignum_MontArithmetic_bn_mont_ctx_u64) @->
           ((ptr uint64_t) @->
              (uint32_t @->
                 ((ptr uint64_t) @-> ((ptr uint64_t) @-> (returning void))))))
    let hacl_Bignum64_mod_inv_prime_vartime_precomp =
      foreign "Hacl_Bignum64_mod_inv_prime_vartime_precomp"
        ((ptr hacl_Bignum_MontArithmetic_bn_mont_ctx_u64) @->
           ((ptr uint64_t) @-> ((ptr uint64_t) @-> (returning void))))
    let hacl_Bignum64_new_bn_from_bytes_be =
      foreign "Hacl_Bignum64_new_bn_from_bytes_be"
        (uint32_t @-> (ocaml_bytes @-> (returning (ptr uint64_t))))
    let hacl_Bignum64_new_bn_from_bytes_le =
      foreign "Hacl_Bignum64_new_bn_from_bytes_le"
        (uint32_t @-> (ocaml_bytes @-> (returning (ptr uint64_t))))
    let hacl_Bignum64_bn_to_bytes_be =
      foreign "Hacl_Bignum64_bn_to_bytes_be"
        (uint32_t @-> ((ptr uint64_t) @-> (ocaml_bytes @-> (returning void))))
    let hacl_Bignum64_bn_to_bytes_le =
      foreign "Hacl_Bignum64_bn_to_bytes_le"
        (uint32_t @-> ((ptr uint64_t) @-> (ocaml_bytes @-> (returning void))))
    let hacl_Bignum64_lt_mask =
      foreign "Hacl_Bignum64_lt_mask"
        (uint32_t @->
           ((ptr uint64_t) @-> ((ptr uint64_t) @-> (returning uint64_t))))
    let hacl_Bignum64_eq_mask =
      foreign "Hacl_Bignum64_eq_mask"
        (uint32_t @->
           ((ptr uint64_t) @-> ((ptr uint64_t) @-> (returning uint64_t))))
  end