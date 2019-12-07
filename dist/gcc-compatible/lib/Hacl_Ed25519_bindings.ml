open Ctypes
module Bindings(F:Cstubs.FOREIGN) =
  struct
    open F
    let hacl_Ed25519_sign =
      foreign "Hacl_Ed25519_sign"
        ((ptr uint8_t) @->
           ((ptr uint8_t) @->
              (uint32_t @-> ((ptr uint8_t) @-> (returning void)))))
      
    let hacl_Ed25519_verify =
      foreign "Hacl_Ed25519_verify"
        ((ptr uint8_t) @->
           (uint32_t @->
              ((ptr uint8_t) @-> ((ptr uint8_t) @-> (returning bool)))))
      
    let hacl_Ed25519_secret_to_public =
      foreign "Hacl_Ed25519_secret_to_public"
        ((ptr uint8_t) @-> ((ptr uint8_t) @-> (returning void)))
      
    let hacl_Ed25519_expand_keys =
      foreign "Hacl_Ed25519_expand_keys"
        ((ptr uint8_t) @-> ((ptr uint8_t) @-> (returning void)))
      
    let hacl_Ed25519_sign_expanded =
      foreign "Hacl_Ed25519_sign_expanded"
        ((ptr uint8_t) @->
           ((ptr uint8_t) @->
              (uint32_t @-> ((ptr uint8_t) @-> (returning void)))))
      
  end