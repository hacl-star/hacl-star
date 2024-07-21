open Ctypes
module Bindings(F:Cstubs.FOREIGN) =
  struct
    open F
    let hacl_Impl_PCurves_PrecompTable_P256_precomp_get_consttime =
      foreign "Hacl_Impl_PCurves_PrecompTable_P256_precomp_get_consttime"
        ((ptr uint64_t) @->
           ((ptr uint64_t) @->
              (uint64_t @-> ((ptr uint64_t) @-> (returning void)))))
  end