open Ctypes
module Bindings(F:Cstubs.FOREIGN) =
  struct
    open F
    let hacl_Curve25519_64_Slow_scalarmult =
      foreign "Hacl_Curve25519_64_Slow_scalarmult"
        ((ptr uint8_t) @->
           ((ptr uint8_t) @-> ((ptr uint8_t) @-> (returning void))))
      
    let hacl_Curve25519_64_Slow_secret_to_public =
      foreign "Hacl_Curve25519_64_Slow_secret_to_public"
        ((ptr uint8_t) @-> ((ptr uint8_t) @-> (returning void)))
      
    let hacl_Curve25519_64_Slow_ecdh =
      foreign "Hacl_Curve25519_64_Slow_ecdh"
        ((ptr uint8_t) @->
           ((ptr uint8_t) @-> ((ptr uint8_t) @-> (returning bool))))
      
  end