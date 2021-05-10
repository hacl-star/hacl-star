open Ctypes
module Bindings(F:Cstubs.FOREIGN) =
  struct
    open F
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
    let hacl_GenericField32_field_modulus_check =
      foreign "Hacl_GenericField32_field_modulus_check"
        (uint32_t @-> ((ptr uint32_t) @-> (returning bool)))
    let hacl_GenericField32_field_init =
      foreign "Hacl_GenericField32_field_init"
        (uint32_t @->
           ((ptr uint32_t) @->
              (returning (ptr hacl_Bignum_MontArithmetic_bn_mont_ctx_u32))))
    let hacl_GenericField32_field_free =
      foreign "Hacl_GenericField32_field_free"
        ((ptr hacl_Bignum_MontArithmetic_bn_mont_ctx_u32) @->
           (returning void))
    let hacl_GenericField32_field_get_len =
      foreign "Hacl_GenericField32_field_get_len"
        ((ptr hacl_Bignum_MontArithmetic_bn_mont_ctx_u32) @->
           (returning uint32_t))
    let hacl_GenericField32_to_field =
      foreign "Hacl_GenericField32_to_field"
        ((ptr hacl_Bignum_MontArithmetic_bn_mont_ctx_u32) @->
           ((ptr uint32_t) @-> ((ptr uint32_t) @-> (returning void))))
    let hacl_GenericField32_from_field =
      foreign "Hacl_GenericField32_from_field"
        ((ptr hacl_Bignum_MontArithmetic_bn_mont_ctx_u32) @->
           ((ptr uint32_t) @-> ((ptr uint32_t) @-> (returning void))))
    let hacl_GenericField32_add =
      foreign "Hacl_GenericField32_add"
        ((ptr hacl_Bignum_MontArithmetic_bn_mont_ctx_u32) @->
           ((ptr uint32_t) @->
              ((ptr uint32_t) @-> ((ptr uint32_t) @-> (returning void)))))
    let hacl_GenericField32_sub =
      foreign "Hacl_GenericField32_sub"
        ((ptr hacl_Bignum_MontArithmetic_bn_mont_ctx_u32) @->
           ((ptr uint32_t) @->
              ((ptr uint32_t) @-> ((ptr uint32_t) @-> (returning void)))))
    let hacl_GenericField32_mul =
      foreign "Hacl_GenericField32_mul"
        ((ptr hacl_Bignum_MontArithmetic_bn_mont_ctx_u32) @->
           ((ptr uint32_t) @->
              ((ptr uint32_t) @-> ((ptr uint32_t) @-> (returning void)))))
    let hacl_GenericField32_sqr =
      foreign "Hacl_GenericField32_sqr"
        ((ptr hacl_Bignum_MontArithmetic_bn_mont_ctx_u32) @->
           ((ptr uint32_t) @-> ((ptr uint32_t) @-> (returning void))))
    let hacl_GenericField32_one =
      foreign "Hacl_GenericField32_one"
        ((ptr hacl_Bignum_MontArithmetic_bn_mont_ctx_u32) @->
           ((ptr uint32_t) @-> (returning void)))
    let hacl_GenericField32_exp_consttime =
      foreign "Hacl_GenericField32_exp_consttime"
        ((ptr hacl_Bignum_MontArithmetic_bn_mont_ctx_u32) @->
           ((ptr uint32_t) @->
              (uint32_t @->
                 ((ptr uint32_t) @-> ((ptr uint32_t) @-> (returning void))))))
    let hacl_GenericField32_exp_vartime =
      foreign "Hacl_GenericField32_exp_vartime"
        ((ptr hacl_Bignum_MontArithmetic_bn_mont_ctx_u32) @->
           ((ptr uint32_t) @->
              (uint32_t @->
                 ((ptr uint32_t) @-> ((ptr uint32_t) @-> (returning void))))))
    let hacl_GenericField32_inverse =
      foreign "Hacl_GenericField32_inverse"
        ((ptr hacl_Bignum_MontArithmetic_bn_mont_ctx_u32) @->
           ((ptr uint32_t) @-> ((ptr uint32_t) @-> (returning void))))
  end