open Ctypes
module Bindings(F:Cstubs.FOREIGN) =
  struct
    open F
    module Hacl_Bignum256_applied =
      (Hacl_Bignum256_bindings.Bindings)(Hacl_Bignum256_stubs)
    open Hacl_Bignum256_applied
    let hacl_GenericField64_field_modulus_check =
      foreign "Hacl_GenericField64_field_modulus_check"
        (uint32_t @-> ((ptr uint64_t) @-> (returning bool)))
    let hacl_GenericField64_field_init =
      foreign "Hacl_GenericField64_field_init"
        (uint32_t @->
           ((ptr uint64_t) @->
              (returning (ptr hacl_Bignum_MontArithmetic_bn_mont_ctx_u64))))
    let hacl_GenericField64_field_free =
      foreign "Hacl_GenericField64_field_free"
        ((ptr hacl_Bignum_MontArithmetic_bn_mont_ctx_u64) @->
           (returning void))
    let hacl_GenericField64_field_get_len =
      foreign "Hacl_GenericField64_field_get_len"
        ((ptr hacl_Bignum_MontArithmetic_bn_mont_ctx_u64) @->
           (returning uint32_t))
    let hacl_GenericField64_to_field =
      foreign "Hacl_GenericField64_to_field"
        ((ptr hacl_Bignum_MontArithmetic_bn_mont_ctx_u64) @->
           ((ptr uint64_t) @-> ((ptr uint64_t) @-> (returning void))))
    let hacl_GenericField64_from_field =
      foreign "Hacl_GenericField64_from_field"
        ((ptr hacl_Bignum_MontArithmetic_bn_mont_ctx_u64) @->
           ((ptr uint64_t) @-> ((ptr uint64_t) @-> (returning void))))
    let hacl_GenericField64_add =
      foreign "Hacl_GenericField64_add"
        ((ptr hacl_Bignum_MontArithmetic_bn_mont_ctx_u64) @->
           ((ptr uint64_t) @->
              ((ptr uint64_t) @-> ((ptr uint64_t) @-> (returning void)))))
    let hacl_GenericField64_sub =
      foreign "Hacl_GenericField64_sub"
        ((ptr hacl_Bignum_MontArithmetic_bn_mont_ctx_u64) @->
           ((ptr uint64_t) @->
              ((ptr uint64_t) @-> ((ptr uint64_t) @-> (returning void)))))
    let hacl_GenericField64_mul =
      foreign "Hacl_GenericField64_mul"
        ((ptr hacl_Bignum_MontArithmetic_bn_mont_ctx_u64) @->
           ((ptr uint64_t) @->
              ((ptr uint64_t) @-> ((ptr uint64_t) @-> (returning void)))))
    let hacl_GenericField64_sqr =
      foreign "Hacl_GenericField64_sqr"
        ((ptr hacl_Bignum_MontArithmetic_bn_mont_ctx_u64) @->
           ((ptr uint64_t) @-> ((ptr uint64_t) @-> (returning void))))
    let hacl_GenericField64_one =
      foreign "Hacl_GenericField64_one"
        ((ptr hacl_Bignum_MontArithmetic_bn_mont_ctx_u64) @->
           ((ptr uint64_t) @-> (returning void)))
    let hacl_GenericField64_exp_consttime =
      foreign "Hacl_GenericField64_exp_consttime"
        ((ptr hacl_Bignum_MontArithmetic_bn_mont_ctx_u64) @->
           ((ptr uint64_t) @->
              (uint32_t @->
                 ((ptr uint64_t) @-> ((ptr uint64_t) @-> (returning void))))))
    let hacl_GenericField64_exp_vartime =
      foreign "Hacl_GenericField64_exp_vartime"
        ((ptr hacl_Bignum_MontArithmetic_bn_mont_ctx_u64) @->
           ((ptr uint64_t) @->
              (uint32_t @->
                 ((ptr uint64_t) @-> ((ptr uint64_t) @-> (returning void))))))
    let hacl_GenericField64_inverse =
      foreign "Hacl_GenericField64_inverse"
        ((ptr hacl_Bignum_MontArithmetic_bn_mont_ctx_u64) @->
           ((ptr uint64_t) @-> ((ptr uint64_t) @-> (returning void))))
  end