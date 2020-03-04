open Ctypes
module Bindings(F:Cstubs.FOREIGN) =
  struct
    open F
    let everCrypt_Cipher_chacha20 =
      foreign "EverCrypt_Cipher_chacha20"
        (uint32_t @->
           ((ptr uint8_t) @->
              ((ptr uint8_t) @->
                 ((ptr uint8_t) @->
                    ((ptr uint8_t) @-> (uint32_t @-> (returning void)))))))
      
  end