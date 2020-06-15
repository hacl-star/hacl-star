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
    let hacl_Bignum4096_mod_exp =
      foreign "Hacl_Bignum4096_mod_exp"
        ((ptr uint64_t) @->
           ((ptr uint64_t) @->
              (uint32_t @->
                 ((ptr uint64_t) @-> ((ptr uint64_t) @-> (returning void))))))
  end