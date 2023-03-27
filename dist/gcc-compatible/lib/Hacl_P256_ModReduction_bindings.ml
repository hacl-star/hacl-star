open Ctypes
module Bindings(F:Cstubs.FOREIGN) =
  struct
    open F
    let hacl_P256_ModReduction_mul_mod_solinas =
      foreign "Hacl_P256_ModReduction_mul_mod_solinas"
        ((ptr uint64_t) @->
           ((ptr uint64_t) @-> ((ptr uint64_t) @-> (returning void))))
    let hacl_P256_ModReduction_mul_mod_mont =
      foreign "Hacl_P256_ModReduction_mul_mod_mont"
        ((ptr uint64_t) @->
           ((ptr uint64_t) @-> ((ptr uint64_t) @-> (returning void))))
  end