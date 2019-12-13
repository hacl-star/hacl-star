open Ctypes
module Bindings(F:Cstubs.FOREIGN) =
  struct
    open F
    let everCrypt_Curve25519_secret_to_public =
      foreign "EverCrypt_Curve25519_secret_to_public"
        ((ptr uint8_t) @-> ((ptr uint8_t) @-> (returning void)))
      
    let everCrypt_Curve25519_scalarmult =
      foreign "EverCrypt_Curve25519_scalarmult"
        ((ptr uint8_t) @->
           ((ptr uint8_t) @-> ((ptr uint8_t) @-> (returning void))))
      
    let everCrypt_Curve25519_ecdh =
      foreign "EverCrypt_Curve25519_ecdh"
        ((ptr uint8_t) @->
           ((ptr uint8_t) @-> ((ptr uint8_t) @-> (returning bool))))
      
  end