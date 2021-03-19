open Ctypes
module Bindings(F:Cstubs.FOREIGN) =
  struct
    open F
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
    let hacl_Bignum64_mul =
      foreign "Hacl_Bignum64_mul"
        (uint32_t @->
           ((ptr uint64_t) @->
              ((ptr uint64_t) @-> ((ptr uint64_t) @-> (returning void)))))
    let hacl_Bignum64_sqr =
      foreign "Hacl_Bignum64_sqr"
        (uint32_t @->
           ((ptr uint64_t) @-> ((ptr uint64_t) @-> (returning void))))
    let hacl_Bignum64_mod_precompr2 =
      foreign "Hacl_Bignum64_mod_precompr2"
        (uint32_t @->
           ((ptr uint64_t) @->
              ((ptr uint64_t) @->
                 ((ptr uint64_t) @-> ((ptr uint64_t) @-> (returning void))))))
    let hacl_Bignum64_mod =
      foreign "Hacl_Bignum64_mod"
        (uint32_t @->
           ((ptr uint64_t) @->
              ((ptr uint64_t) @-> ((ptr uint64_t) @-> (returning bool)))))
    let hacl_Bignum64_mod_exp_vartime_precompr2 =
      foreign "Hacl_Bignum64_mod_exp_vartime_precompr2"
        (uint32_t @->
           ((ptr uint64_t) @->
              ((ptr uint64_t) @->
                 (uint32_t @->
                    ((ptr uint64_t) @->
                       ((ptr uint64_t) @->
                          ((ptr uint64_t) @-> (returning void))))))))
    let hacl_Bignum64_mod_exp_consttime_precompr2 =
      foreign "Hacl_Bignum64_mod_exp_consttime_precompr2"
        (uint32_t @->
           ((ptr uint64_t) @->
              ((ptr uint64_t) @->
                 (uint32_t @->
                    ((ptr uint64_t) @->
                       ((ptr uint64_t) @->
                          ((ptr uint64_t) @-> (returning void))))))))
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
    let hacl_Bignum64_new_precompr2 =
      foreign "Hacl_Bignum64_new_precompr2"
        (uint32_t @-> ((ptr uint64_t) @-> (returning (ptr uint64_t))))
    let hacl_Bignum64_mod_inv_prime_vartime =
      foreign "Hacl_Bignum64_mod_inv_prime_vartime"
        (uint32_t @->
           ((ptr uint64_t) @->
              ((ptr uint64_t) @-> ((ptr uint64_t) @-> (returning bool)))))
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
  end