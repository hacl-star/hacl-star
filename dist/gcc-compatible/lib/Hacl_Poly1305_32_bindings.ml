open Ctypes
module Bindings(F:Cstubs.FOREIGN) =
  struct
    open F
    let hacl_Poly1305_32_blocklen =
      foreign_value "Hacl_Poly1305_32_blocklen" uint32_t 
    let hacl_Poly1305_32_poly1305_init =
      foreign "Hacl_Poly1305_32_poly1305_init"
        ((ptr uint64_t) @-> ((ptr uint8_t) @-> (returning void)))
      
    let hacl_Poly1305_32_poly1305_update1 =
      foreign "Hacl_Poly1305_32_poly1305_update1"
        ((ptr uint64_t) @-> ((ptr uint8_t) @-> (returning void)))
      
    let hacl_Poly1305_32_poly1305_update =
      foreign "Hacl_Poly1305_32_poly1305_update"
        ((ptr uint64_t) @->
           (uint32_t @-> ((ptr uint8_t) @-> (returning void))))
      
    let hacl_Poly1305_32_poly1305_finish =
      foreign "Hacl_Poly1305_32_poly1305_finish"
        ((ptr uint8_t) @->
           ((ptr uint8_t) @-> ((ptr uint64_t) @-> (returning void))))
      
    let hacl_Poly1305_32_poly1305_mac =
      foreign "Hacl_Poly1305_32_poly1305_mac"
        ((ptr uint8_t) @->
           (uint32_t @->
              ((ptr uint8_t) @-> ((ptr uint8_t) @-> (returning void)))))
      
  end