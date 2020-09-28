open Ctypes
module Bindings(F:Cstubs.FOREIGN) =
  struct
    open F
    let hacl_Blake2b_32_blake2b_init =
      foreign "Hacl_Blake2b_32_blake2b_init"
        ((ptr uint64_t) @->
           ((ptr uint64_t) @->
              (uint32_t @-> (ocaml_bytes @-> (uint32_t @-> (returning void))))))
    let hacl_Blake2b_32_blake2b_finish =
      foreign "Hacl_Blake2b_32_blake2b_finish"
        (uint32_t @-> (ocaml_bytes @-> ((ptr uint64_t) @-> (returning void))))
    let hacl_Blake2b_32_blake2b =
      foreign "Hacl_Blake2b_32_blake2b"
        (uint32_t @->
           (ocaml_bytes @->
              (uint32_t @->
                 (ocaml_bytes @->
                    (uint32_t @-> (ocaml_bytes @-> (returning void)))))))
  end