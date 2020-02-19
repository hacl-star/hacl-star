open Ctypes
module Bindings(F:Cstubs.FOREIGN) =
  struct
    open F
    let hacl_Chacha20Poly1305_128_aead_encrypt =
      foreign "Hacl_Chacha20Poly1305_128_aead_encrypt"
        ((ptr uint8_t) @->
           ((ptr uint8_t) @->
              (uint32_t @->
                 ((ptr uint8_t) @->
                    (uint32_t @->
                       ((ptr uint8_t) @->
                          ((ptr uint8_t) @->
                             ((ptr uint8_t) @-> (returning void)))))))))
      
    let hacl_Chacha20Poly1305_128_aead_decrypt =
      foreign "Hacl_Chacha20Poly1305_128_aead_decrypt"
        ((ptr uint8_t) @->
           ((ptr uint8_t) @->
              (uint32_t @->
                 ((ptr uint8_t) @->
                    (uint32_t @->
                       ((ptr uint8_t) @->
                          ((ptr uint8_t) @->
                             ((ptr uint8_t) @-> (returning uint32_t)))))))))
      
  end