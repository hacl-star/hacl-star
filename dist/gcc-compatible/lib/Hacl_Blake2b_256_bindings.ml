open Ctypes
module Bindings(F:Cstubs.FOREIGN) =
  struct
    open F
    let hacl_Blake2b_256_blake2b =
      foreign "Hacl_Blake2b_256_blake2b"
        (uint32_t @->
           ((ptr uint8_t) @->
              (uint32_t @->
                 ((ptr uint8_t) @->
                    (uint32_t @-> ((ptr uint8_t) @-> (returning void)))))))
    let hacl_Blake2b_256_blake2b_bytes =
      foreign "Hacl_Blake2b_256_blake2b"
        (uint32_t @->
           (ocaml_bytes @->
              (uint32_t @->
                 (ocaml_bytes @->
                    (uint32_t @-> (ocaml_bytes @-> (returning void)))))))
  end
