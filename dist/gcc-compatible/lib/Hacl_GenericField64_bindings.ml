open Ctypes
module Bindings(F:Cstubs.FOREIGN) =
  struct
    open F
    type hacl_Bignum_GenericField_bn_mont_ctx_u64 =
      [ `hacl_Bignum_GenericField_bn_mont_ctx_u64 ] structure
    let (hacl_Bignum_GenericField_bn_mont_ctx_u64 :
      [ `hacl_Bignum_GenericField_bn_mont_ctx_u64 ] structure typ) =
      structure "Hacl_Bignum_GenericField_bn_mont_ctx_u64_s"
    let hacl_Bignum_GenericField_bn_mont_ctx_u64_nBits =
      field hacl_Bignum_GenericField_bn_mont_ctx_u64 "nBits" uint32_t
    let hacl_Bignum_GenericField_bn_mont_ctx_u64_len =
      field hacl_Bignum_GenericField_bn_mont_ctx_u64 "len" uint32_t
    let hacl_Bignum_GenericField_bn_mont_ctx_u64_n =
      field hacl_Bignum_GenericField_bn_mont_ctx_u64 "n" (ptr uint64_t)
    let hacl_Bignum_GenericField_bn_mont_ctx_u64_mu =
      field hacl_Bignum_GenericField_bn_mont_ctx_u64 "mu" uint64_t
    let hacl_Bignum_GenericField_bn_mont_ctx_u64_r2 =
      field hacl_Bignum_GenericField_bn_mont_ctx_u64 "r2" (ptr uint64_t)
    let _ = seal hacl_Bignum_GenericField_bn_mont_ctx_u64
    let hacl_GenericField64_field_init =
      foreign "Hacl_GenericField64_field_init"
        (uint32_t @->
           (uint32_t @->
              ((ptr uint64_t) @->
                 (returning hacl_Bignum_GenericField_bn_mont_ctx_u64))))
    let hacl_GenericField64_field_get_len =
      foreign "Hacl_GenericField64_field_get_len"
        (hacl_Bignum_GenericField_bn_mont_ctx_u64 @-> (returning uint32_t))
    let hacl_GenericField64_to_field =
      foreign "Hacl_GenericField64_to_field"
        (hacl_Bignum_GenericField_bn_mont_ctx_u64 @->
           ((ptr uint64_t) @-> ((ptr uint64_t) @-> (returning void))))
    let hacl_GenericField64_from_field =
      foreign "Hacl_GenericField64_from_field"
        (hacl_Bignum_GenericField_bn_mont_ctx_u64 @->
           ((ptr uint64_t) @-> ((ptr uint64_t) @-> (returning void))))
    let hacl_GenericField64_add =
      foreign "Hacl_GenericField64_add"
        (hacl_Bignum_GenericField_bn_mont_ctx_u64 @->
           ((ptr uint64_t) @->
              ((ptr uint64_t) @-> ((ptr uint64_t) @-> (returning void)))))
    let hacl_GenericField64_sub =
      foreign "Hacl_GenericField64_sub"
        (hacl_Bignum_GenericField_bn_mont_ctx_u64 @->
           ((ptr uint64_t) @->
              ((ptr uint64_t) @-> ((ptr uint64_t) @-> (returning void)))))
    let hacl_GenericField64_mul =
      foreign "Hacl_GenericField64_mul"
        (hacl_Bignum_GenericField_bn_mont_ctx_u64 @->
           ((ptr uint64_t) @->
              ((ptr uint64_t) @-> ((ptr uint64_t) @-> (returning void)))))
    let hacl_GenericField64_sqr =
      foreign "Hacl_GenericField64_sqr"
        (hacl_Bignum_GenericField_bn_mont_ctx_u64 @->
           ((ptr uint64_t) @-> ((ptr uint64_t) @-> (returning void))))
    let hacl_GenericField64_one =
      foreign "Hacl_GenericField64_one"
        (hacl_Bignum_GenericField_bn_mont_ctx_u64 @->
           ((ptr uint64_t) @-> (returning void)))
    let hacl_GenericField64_inverse =
      foreign "Hacl_GenericField64_inverse"
        (hacl_Bignum_GenericField_bn_mont_ctx_u64 @->
           ((ptr uint64_t) @-> ((ptr uint64_t) @-> (returning void))))
  end