open Ctypes
module Bindings(F:Cstubs.FOREIGN) =
  struct
    open F
    let hacl_Chacha20_Vec256_chacha20_encrypt_256 =
      foreign "Hacl_Chacha20_Vec256_chacha20_encrypt_256"
        (uint32_t @->
           ((ptr uint8_t) @->
              ((ptr uint8_t) @->
                 ((ptr uint8_t) @->
                    ((ptr uint8_t) @-> (uint32_t @-> (returning void)))))))
      
    let hacl_Chacha20_Vec256_chacha20_decrypt_256 =
      foreign "Hacl_Chacha20_Vec256_chacha20_decrypt_256"
        (uint32_t @->
           ((ptr uint8_t) @->
              ((ptr uint8_t) @->
                 ((ptr uint8_t) @->
                    ((ptr uint8_t) @-> (uint32_t @-> (returning void)))))))
      
  end