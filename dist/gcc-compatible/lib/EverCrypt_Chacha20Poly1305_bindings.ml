open Ctypes
module Bindings(F:Cstubs.FOREIGN) =
  struct
    open F
    let everCrypt_Chacha20Poly1305_aead_encrypt =
      foreign "EverCrypt_Chacha20Poly1305_aead_encrypt"
        ((ptr uint8_t) @->
           ((ptr uint8_t) @->
              (uint32_t @->
                 ((ptr uint8_t) @->
                    (uint32_t @->
                       ((ptr uint8_t) @->
                          ((ptr uint8_t) @->
                             ((ptr uint8_t) @-> (returning void)))))))))
      
    let everCrypt_Chacha20Poly1305_aead_decrypt =
      foreign "EverCrypt_Chacha20Poly1305_aead_decrypt"
        ((ptr uint8_t) @->
           ((ptr uint8_t) @->
              (uint32_t @->
                 ((ptr uint8_t) @->
                    (uint32_t @->
                       ((ptr uint8_t) @->
                          ((ptr uint8_t) @->
                             ((ptr uint8_t) @-> (returning uint32_t)))))))))
      
  end