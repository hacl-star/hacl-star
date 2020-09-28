open Ctypes
module Bindings(F:Cstubs.FOREIGN) =
  struct
    open F
    let hacl_Blake2s_32_blake2s_init =
      foreign "Hacl_Blake2s_32_blake2s_init"
        ((ptr uint32_t) @->
           ((ptr uint32_t) @->
              (uint32_t @-> (ocaml_bytes @-> (uint32_t @-> (returning void))))))
    let hacl_Blake2s_32_blake2s_update_multi =
      foreign "Hacl_Blake2s_32_blake2s_update_multi"
        (uint32_t @->
           ((ptr uint32_t) @->
              ((ptr uint32_t) @->
                 (uint64_t @->
                    (ocaml_bytes @-> (uint32_t @-> (returning void)))))))
    let hacl_Blake2s_32_blake2s_update_last =
      foreign "Hacl_Blake2s_32_blake2s_update_last"
        (uint32_t @->
           ((ptr uint32_t) @->
              ((ptr uint32_t) @->
                 (uint64_t @->
                    (uint32_t @-> (ocaml_bytes @-> (returning void)))))))
    let hacl_Blake2s_32_blake2s_finish =
      foreign "Hacl_Blake2s_32_blake2s_finish"
        (uint32_t @-> (ocaml_bytes @-> ((ptr uint32_t) @-> (returning void))))
    let hacl_Blake2s_32_blake2s =
      foreign "Hacl_Blake2s_32_blake2s"
        (uint32_t @->
           (ocaml_bytes @->
              (uint32_t @->
                 (ocaml_bytes @->
                    (uint32_t @-> (ocaml_bytes @-> (returning void)))))))
  end