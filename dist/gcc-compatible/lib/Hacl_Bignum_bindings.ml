open Ctypes
module Bindings(F:Cstubs.FOREIGN) =
  struct
    open F
    let hacl_Bignum_Multiplication_mul_carry_add_u64_st =
      foreign "Hacl_Bignum_Multiplication_mul_carry_add_u64_st"
        (uint64_t @->
           (uint64_t @->
              (uint64_t @-> ((ptr uint64_t) @-> (returning uint64_t)))))
    let hacl_Bignum_Karatsuba_bn_karatsuba_mul_ =
      foreign "Hacl_Bignum_Karatsuba_bn_karatsuba_mul_"
        (uint32_t @->
           ((ptr uint64_t) @->
              ((ptr uint64_t) @->
                 ((ptr uint64_t) @-> ((ptr uint64_t) @-> (returning void))))))
    let hacl_Bignum_Karatsuba_bn_karatsuba_sqr_ =
      foreign "Hacl_Bignum_Karatsuba_bn_karatsuba_sqr_"
        (uint32_t @->
           ((ptr uint64_t) @->
              ((ptr uint64_t) @-> ((ptr uint64_t) @-> (returning void)))))
    let hacl_Bignum_bn_is_bit_set =
      foreign "Hacl_Bignum_bn_is_bit_set"
        (uint32_t @-> ((ptr uint64_t) @-> (uint32_t @-> (returning bool))))
    let hacl_Bignum_bn_bit_set =
      foreign "Hacl_Bignum_bn_bit_set"
        (uint32_t @-> ((ptr uint64_t) @-> (uint32_t @-> (returning void))))
    let hacl_Bignum_bn_is_less =
      foreign "Hacl_Bignum_bn_is_less"
        (uint32_t @->
           ((ptr uint64_t) @-> ((ptr uint64_t) @-> (returning bool))))
    let hacl_Bignum_ModInv64_mod_inv_u64 =
      foreign "Hacl_Bignum_ModInv64_mod_inv_u64"
        (uint64_t @-> (returning uint64_t))
  end