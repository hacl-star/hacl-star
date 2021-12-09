open Ctypes
module Bindings(F:Cstubs.FOREIGN) =
  struct
    open F
    module Hacl_GenericField32_applied =
      (Hacl_GenericField32_bindings.Bindings)(Hacl_GenericField32_stubs)
    open Hacl_GenericField32_applied
    let hacl_Bignum32_add =
      foreign "Hacl_Bignum32_add"
        (uint32_t @->
           ((ptr uint32_t) @->
              ((ptr uint32_t) @-> ((ptr uint32_t) @-> (returning uint32_t)))))
    let hacl_Bignum32_sub =
      foreign "Hacl_Bignum32_sub"
        (uint32_t @->
           ((ptr uint32_t) @->
              ((ptr uint32_t) @-> ((ptr uint32_t) @-> (returning uint32_t)))))
    let hacl_Bignum32_add_mod =
      foreign "Hacl_Bignum32_add_mod"
        (uint32_t @->
           ((ptr uint32_t) @->
              ((ptr uint32_t) @->
                 ((ptr uint32_t) @-> ((ptr uint32_t) @-> (returning void))))))
    let hacl_Bignum32_sub_mod =
      foreign "Hacl_Bignum32_sub_mod"
        (uint32_t @->
           ((ptr uint32_t) @->
              ((ptr uint32_t) @->
                 ((ptr uint32_t) @-> ((ptr uint32_t) @-> (returning void))))))
    let hacl_Bignum32_mul =
      foreign "Hacl_Bignum32_mul"
        (uint32_t @->
           ((ptr uint32_t) @->
              ((ptr uint32_t) @-> ((ptr uint32_t) @-> (returning void)))))
    let hacl_Bignum32_sqr =
      foreign "Hacl_Bignum32_sqr"
        (uint32_t @->
           ((ptr uint32_t) @-> ((ptr uint32_t) @-> (returning void))))
    let hacl_Bignum32_mod =
      foreign "Hacl_Bignum32_mod"
        (uint32_t @->
           ((ptr uint32_t) @->
              ((ptr uint32_t) @-> ((ptr uint32_t) @-> (returning bool)))))
    let hacl_Bignum32_mod_exp_vartime =
      foreign "Hacl_Bignum32_mod_exp_vartime"
        (uint32_t @->
           ((ptr uint32_t) @->
              ((ptr uint32_t) @->
                 (uint32_t @->
                    ((ptr uint32_t) @-> ((ptr uint32_t) @-> (returning bool)))))))
    let hacl_Bignum32_mod_exp_consttime =
      foreign "Hacl_Bignum32_mod_exp_consttime"
        (uint32_t @->
           ((ptr uint32_t) @->
              ((ptr uint32_t) @->
                 (uint32_t @->
                    ((ptr uint32_t) @-> ((ptr uint32_t) @-> (returning bool)))))))
    let hacl_Bignum32_mod_inv_prime_vartime =
      foreign "Hacl_Bignum32_mod_inv_prime_vartime"
        (uint32_t @->
           ((ptr uint32_t) @->
              ((ptr uint32_t) @-> ((ptr uint32_t) @-> (returning bool)))))
    let hacl_Bignum32_mont_ctx_init =
      foreign "Hacl_Bignum32_mont_ctx_init"
        (uint32_t @->
           ((ptr uint32_t) @->
              (returning (ptr hacl_Bignum_MontArithmetic_bn_mont_ctx_u32))))
    let hacl_Bignum32_mont_ctx_free =
      foreign "Hacl_Bignum32_mont_ctx_free"
        ((ptr hacl_Bignum_MontArithmetic_bn_mont_ctx_u32) @->
           (returning void))
    let hacl_Bignum32_mod_precomp =
      foreign "Hacl_Bignum32_mod_precomp"
        ((ptr hacl_Bignum_MontArithmetic_bn_mont_ctx_u32) @->
           ((ptr uint32_t) @-> ((ptr uint32_t) @-> (returning void))))
    let hacl_Bignum32_mod_exp_vartime_precomp =
      foreign "Hacl_Bignum32_mod_exp_vartime_precomp"
        ((ptr hacl_Bignum_MontArithmetic_bn_mont_ctx_u32) @->
           ((ptr uint32_t) @->
              (uint32_t @->
                 ((ptr uint32_t) @-> ((ptr uint32_t) @-> (returning void))))))
    let hacl_Bignum32_mod_exp_consttime_precomp =
      foreign "Hacl_Bignum32_mod_exp_consttime_precomp"
        ((ptr hacl_Bignum_MontArithmetic_bn_mont_ctx_u32) @->
           ((ptr uint32_t) @->
              (uint32_t @->
                 ((ptr uint32_t) @-> ((ptr uint32_t) @-> (returning void))))))
    let hacl_Bignum32_mod_inv_prime_vartime_precomp =
      foreign "Hacl_Bignum32_mod_inv_prime_vartime_precomp"
        ((ptr hacl_Bignum_MontArithmetic_bn_mont_ctx_u32) @->
           ((ptr uint32_t) @-> ((ptr uint32_t) @-> (returning void))))
    let hacl_Bignum32_new_bn_from_bytes_be =
      foreign "Hacl_Bignum32_new_bn_from_bytes_be"
        (uint32_t @-> (ocaml_bytes @-> (returning (ptr uint32_t))))
    let hacl_Bignum32_new_bn_from_bytes_le =
      foreign "Hacl_Bignum32_new_bn_from_bytes_le"
        (uint32_t @-> (ocaml_bytes @-> (returning (ptr uint32_t))))
    let hacl_Bignum32_bn_to_bytes_be =
      foreign "Hacl_Bignum32_bn_to_bytes_be"
        (uint32_t @-> ((ptr uint32_t) @-> (ocaml_bytes @-> (returning void))))
    let hacl_Bignum32_bn_to_bytes_le =
      foreign "Hacl_Bignum32_bn_to_bytes_le"
        (uint32_t @-> ((ptr uint32_t) @-> (ocaml_bytes @-> (returning void))))
    let hacl_Bignum32_lt_mask =
      foreign "Hacl_Bignum32_lt_mask"
        (uint32_t @->
           ((ptr uint32_t) @-> ((ptr uint32_t) @-> (returning uint32_t))))
    let hacl_Bignum32_eq_mask =
      foreign "Hacl_Bignum32_eq_mask"
        (uint32_t @->
           ((ptr uint32_t) @-> ((ptr uint32_t) @-> (returning uint32_t))))
  end