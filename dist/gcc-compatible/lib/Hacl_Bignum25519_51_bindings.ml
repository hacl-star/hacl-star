open Ctypes
module Bindings(F:Cstubs.FOREIGN) =
  struct
    open F
    let hacl_Impl_Curve25519_Field51_fadd =
      foreign "Hacl_Impl_Curve25519_Field51_fadd"
        ((ptr uint64_t) @->
           ((ptr uint64_t) @-> ((ptr uint64_t) @-> (returning void))))
    let hacl_Impl_Curve25519_Field51_fsub =
      foreign "Hacl_Impl_Curve25519_Field51_fsub"
        ((ptr uint64_t) @->
           ((ptr uint64_t) @-> ((ptr uint64_t) @-> (returning void))))
    let hacl_Impl_Curve25519_Field51_fmul1 =
      foreign "Hacl_Impl_Curve25519_Field51_fmul1"
        ((ptr uint64_t) @->
           ((ptr uint64_t) @-> (uint64_t @-> (returning void))))
    let hacl_Impl_Curve25519_Field51_store_felem =
      foreign "Hacl_Impl_Curve25519_Field51_store_felem"
        ((ptr uint64_t) @-> ((ptr uint64_t) @-> (returning void)))
    let hacl_Impl_Curve25519_Field51_cswap2 =
      foreign "Hacl_Impl_Curve25519_Field51_cswap2"
        (uint64_t @->
           ((ptr uint64_t) @-> ((ptr uint64_t) @-> (returning void))))
  end