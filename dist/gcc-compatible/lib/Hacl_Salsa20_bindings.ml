open Ctypes
module Bindings(F:Cstubs.FOREIGN) =
  struct
    open F
    let hacl_Salsa20_salsa20_encrypt =
      foreign "Hacl_Salsa20_salsa20_encrypt"
        (uint32_t @->
           ((ptr uint8_t) @->
              ((ptr uint8_t) @->
                 ((ptr uint8_t) @->
                    ((ptr uint8_t) @-> (uint32_t @-> (returning void)))))))
      
    let hacl_Salsa20_salsa20_decrypt =
      foreign "Hacl_Salsa20_salsa20_decrypt"
        (uint32_t @->
           ((ptr uint8_t) @->
              ((ptr uint8_t) @->
                 ((ptr uint8_t) @->
                    ((ptr uint8_t) @-> (uint32_t @-> (returning void)))))))
      
    let hacl_Salsa20_salsa20_key_block0 =
      foreign "Hacl_Salsa20_salsa20_key_block0"
        ((ptr uint8_t) @->
           ((ptr uint8_t) @-> ((ptr uint8_t) @-> (returning void))))
      
    let hacl_Salsa20_hsalsa20 =
      foreign "Hacl_Salsa20_hsalsa20"
        ((ptr uint8_t) @->
           ((ptr uint8_t) @-> ((ptr uint8_t) @-> (returning void))))
      
  end