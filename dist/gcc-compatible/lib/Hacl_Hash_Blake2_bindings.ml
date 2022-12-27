open Ctypes
module Bindings(F:Cstubs.FOREIGN) =
  struct
    open F
    let hacl_Blake2b_32_blake2b_init =
      foreign "Hacl_Blake2b_32_blake2b_init"
        ((ptr uint64_t) @-> (uint32_t @-> (uint32_t @-> (returning void))))
    let hacl_Blake2b_32_blake2b_update_key =
      foreign "Hacl_Blake2b_32_blake2b_update_key"
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
    let hacl_Blake2b_32_blake2b_malloc =
      foreign "Hacl_Blake2b_32_blake2b_malloc"
        (void @-> (returning (ptr uint64_t)))
    let hacl_Blake2s_32_blake2s_init =
      foreign "Hacl_Blake2s_32_blake2s_init"
        ((ptr uint32_t) @-> (uint32_t @-> (uint32_t @-> (returning void))))
    let hacl_Blake2s_32_blake2s_update_key =
      foreign "Hacl_Blake2s_32_blake2s_update_key"
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
    let hacl_Blake2s_32_blake2s_malloc =
      foreign "Hacl_Blake2s_32_blake2s_malloc"
        (void @-> (returning (ptr uint32_t)))
  end