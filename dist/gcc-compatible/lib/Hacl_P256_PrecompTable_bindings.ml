open Ctypes
module Bindings(F:Cstubs.FOREIGN) =
  struct
    open F
    let hacl_P256_PrecompTable_precomp_get_consttime =
      foreign "Hacl_P256_PrecompTable_precomp_get_consttime"
        ((ptr uint64_t) @->
           ((ptr uint64_t) @->
              (uint64_t @-> ((ptr uint64_t) @-> (returning void)))))
  end