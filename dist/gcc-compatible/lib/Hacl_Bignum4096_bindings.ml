open Ctypes
module Bindings(F:Cstubs.FOREIGN) =
  struct
    open F
    let hacl_Bignum4096_add =
      foreign "Hacl_Bignum4096_add"
        ((ptr uint64_t) @->
           ((ptr uint64_t) @-> ((ptr uint64_t) @-> (returning uint64_t))))
    let hacl_Bignum4096_sub =
      foreign "Hacl_Bignum4096_sub"
        ((ptr uint64_t) @->
           ((ptr uint64_t) @-> ((ptr uint64_t) @-> (returning uint64_t))))
    let hacl_Bignum4096_mul =
      foreign "Hacl_Bignum4096_mul"
        ((ptr uint64_t) @->
           ((ptr uint64_t) @-> ((ptr uint64_t) @-> (returning void))))
    let hacl_Bignum4096_mod_precompr2 =
      foreign "Hacl_Bignum4096_mod_precompr2"
        ((ptr uint64_t) @->
           ((ptr uint64_t) @->
              ((ptr uint64_t) @-> ((ptr uint64_t) @-> (returning void)))))
    let hacl_Bignum4096_mod =
      foreign "Hacl_Bignum4096_mod"
        ((ptr uint64_t) @->
           ((ptr uint64_t) @-> ((ptr uint64_t) @-> (returning bool))))
    let hacl_Bignum4096_mod_exp_precompr2 =
      foreign "Hacl_Bignum4096_mod_exp_precompr2"
        ((ptr uint64_t) @->
           ((ptr uint64_t) @->
              (uint32_t @->
                 ((ptr uint64_t) @->
                    ((ptr uint64_t) @-> ((ptr uint64_t) @-> (returning void)))))))
    let hacl_Bignum4096_mod_exp =
      foreign "Hacl_Bignum4096_mod_exp"
        ((ptr uint64_t) @->
           ((ptr uint64_t) @->
              (uint32_t @->
                 ((ptr uint64_t) @-> ((ptr uint64_t) @-> (returning bool))))))
    let hacl_Bignum4096_mod_exp_mont_ladder_precompr2 =
      foreign "Hacl_Bignum4096_mod_exp_mont_ladder_precompr2"
        ((ptr uint64_t) @->
           ((ptr uint64_t) @->
              (uint32_t @->
                 ((ptr uint64_t) @->
                    ((ptr uint64_t) @-> ((ptr uint64_t) @-> (returning void)))))))
    let hacl_Bignum4096_mod_exp_mont_ladder =
      foreign "Hacl_Bignum4096_mod_exp_mont_ladder"
        ((ptr uint64_t) @->
           ((ptr uint64_t) @->
              (uint32_t @->
                 ((ptr uint64_t) @-> ((ptr uint64_t) @-> (returning bool))))))
    let hacl_Bignum4096_new_precompr2 =
      foreign "Hacl_Bignum4096_new_precompr2"
        (uint32_t @-> ((ptr uint64_t) @-> (returning (ptr uint64_t))))
    let hacl_Bignum4096_mod_inv_prime =
      foreign "Hacl_Bignum4096_mod_inv_prime"
        ((ptr uint64_t) @->
           ((ptr uint64_t) @-> ((ptr uint64_t) @-> (returning bool))))
    let hacl_Bignum4096_new_bn_from_bytes_be =
      foreign "Hacl_Bignum4096_new_bn_from_bytes_be"
        (uint32_t @-> (ocaml_bytes @-> (returning (ptr uint64_t))))
    let hacl_Bignum4096_bn_to_bytes_be =
      foreign "Hacl_Bignum4096_bn_to_bytes_be"
        ((ptr uint64_t) @-> (ocaml_bytes @-> (returning void)))
    let hacl_Bignum4096_lt_mask =
      foreign "Hacl_Bignum4096_lt_mask"
        ((ptr uint64_t) @-> ((ptr uint64_t) @-> (returning uint64_t)))
  end