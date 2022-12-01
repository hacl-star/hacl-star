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
    let hacl_Bignum_Base_mul_wide_add2_u32 =
      foreign "Hacl_Bignum_Base_mul_wide_add2_u32"
        (uint32_t @->
           (uint32_t @->
              (uint32_t @-> ((ptr uint32_t) @-> (returning uint32_t)))))
    let hacl_Bignum_Base_mul_wide_add2_u64 =
      foreign "Hacl_Bignum_Base_mul_wide_add2_u64"
        (uint64_t @->
           (uint64_t @->
              (uint64_t @-> ((ptr uint64_t) @-> (returning uint64_t)))))
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
    let hacl_Bignum_Multiplication_bn_mul_u32 =
      foreign "Hacl_Bignum_Multiplication_bn_mul_u32"
        (uint32_t @->
           ((ptr uint32_t) @->
              (uint32_t @->
                 ((ptr uint32_t) @-> ((ptr uint32_t) @-> (returning void))))))
    let hacl_Bignum_Multiplication_bn_mul_u64 =
      foreign "Hacl_Bignum_Multiplication_bn_mul_u64"
        (uint32_t @->
           ((ptr uint64_t) @->
              (uint32_t @->
                 ((ptr uint64_t) @-> ((ptr uint64_t) @-> (returning void))))))
    let hacl_Bignum_Multiplication_bn_sqr_u32 =
      foreign "Hacl_Bignum_Multiplication_bn_sqr_u32"
        (uint32_t @->
           ((ptr uint32_t) @-> ((ptr uint32_t) @-> (returning void))))
    let hacl_Bignum_Multiplication_bn_sqr_u64 =
      foreign "Hacl_Bignum_Multiplication_bn_sqr_u64"
        (uint32_t @->
           ((ptr uint64_t) @-> ((ptr uint64_t) @-> (returning void))))
  end