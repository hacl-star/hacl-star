open Ctypes
module Bindings(F:Cstubs.FOREIGN) =
  struct
    open F
    let hacl_Frodo_KEM_crypto_kem_keypair =
      foreign "Hacl_Frodo_KEM_crypto_kem_keypair"
        ((ptr uint8_t) @-> ((ptr uint8_t) @-> (returning uint32_t)))
      
    let hacl_Frodo_KEM_crypto_kem_enc =
      foreign "Hacl_Frodo_KEM_crypto_kem_enc"
        ((ptr uint8_t) @->
           ((ptr uint8_t) @-> ((ptr uint8_t) @-> (returning uint32_t))))
      
    let hacl_Frodo_KEM_crypto_kem_dec =
      foreign "Hacl_Frodo_KEM_crypto_kem_dec"
        ((ptr uint8_t) @->
           ((ptr uint8_t) @-> ((ptr uint8_t) @-> (returning uint32_t))))
      
  end