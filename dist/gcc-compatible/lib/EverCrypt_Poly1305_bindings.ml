open Ctypes
module Bindings(F:Cstubs.FOREIGN) =
  struct
    open F
    let everCrypt_Poly1305_poly1305 =
      foreign "EverCrypt_Poly1305_poly1305"
        ((ptr uint8_t) @->
           ((ptr uint8_t) @->
              (uint32_t @-> ((ptr uint8_t) @-> (returning void)))))
      
  end