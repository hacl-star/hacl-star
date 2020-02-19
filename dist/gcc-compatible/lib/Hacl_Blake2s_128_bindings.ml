open Ctypes
module Bindings(F:Cstubs.FOREIGN) =
  struct
    open F
    let hacl_Blake2s_128_blake2s =
      foreign "Hacl_Blake2s_128_blake2s"
        (uint32_t @->
           ((ptr uint8_t) @->
              (uint32_t @->
                 ((ptr uint8_t) @->
                    (uint32_t @-> ((ptr uint8_t) @-> (returning void)))))))
  end