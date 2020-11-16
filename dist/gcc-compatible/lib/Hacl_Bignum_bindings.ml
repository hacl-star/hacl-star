open Ctypes
module Bindings(F:Cstubs.FOREIGN) =
  struct
    open F
    let hacl_Bignum_Karatsuba_bn_karatsuba_mul_uint64 =
      foreign "Hacl_Bignum_Karatsuba_bn_karatsuba_mul_uint64"
        (uint32_t @->
           ((ptr uint64_t) @->
              ((ptr uint64_t) @->
                 ((ptr uint64_t) @-> ((ptr uint64_t) @-> (returning void))))))
    let hacl_Bignum_Karatsuba_bn_karatsuba_sqr_uint64 =
      foreign "Hacl_Bignum_Karatsuba_bn_karatsuba_sqr_uint64"
        (uint32_t @->
           ((ptr uint64_t) @->
              ((ptr uint64_t) @-> ((ptr uint64_t) @-> (returning void)))))
    let hacl_Bignum_bn_add_mod_n_u64 =
      foreign "Hacl_Bignum_bn_add_mod_n_u64"
        (uint32_t @->
           ((ptr uint64_t) @->
              ((ptr uint64_t) @->
                 ((ptr uint64_t) @-> ((ptr uint64_t) @-> (returning void))))))
    let hacl_Bignum_ModInvLimb_mod_inv_uint64 =
      foreign "Hacl_Bignum_ModInvLimb_mod_inv_uint64"
        (uint64_t @-> (returning uint64_t))
  end