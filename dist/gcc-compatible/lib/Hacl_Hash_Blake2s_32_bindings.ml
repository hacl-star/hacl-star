open Ctypes
module Bindings(F:Cstubs.FOREIGN) =
  struct
    open F
    let hacl_Blake2s_32_init =
      foreign "Hacl_Blake2s_32_init"
        ((ptr uint32_t) @-> (uint32_t @-> (uint32_t @-> (returning void))))
    let hacl_Blake2s_32_update_key =
      foreign "Hacl_Blake2s_32_update_key"
        ((ptr uint32_t) @->
           ((ptr uint32_t) @->
              (uint32_t @-> (ocaml_bytes @-> (uint32_t @-> (returning void))))))
    let hacl_Blake2s_32_update_multi =
      foreign "Hacl_Blake2s_32_update_multi"
        (uint32_t @->
           ((ptr uint32_t) @->
              ((ptr uint32_t) @->
                 (uint64_t @->
                    (ocaml_bytes @-> (uint32_t @-> (returning void)))))))
    let hacl_Blake2s_32_update_last =
      foreign "Hacl_Blake2s_32_update_last"
        (uint32_t @->
           ((ptr uint32_t) @->
              ((ptr uint32_t) @->
                 (uint64_t @->
                    (uint32_t @-> (ocaml_bytes @-> (returning void)))))))
    let hacl_Blake2s_32_finish =
      foreign "Hacl_Blake2s_32_finish"
        (uint32_t @-> (ocaml_bytes @-> ((ptr uint32_t) @-> (returning void))))
    let hacl_Blake2s_32_hash_with_key =
      foreign "Hacl_Blake2s_32_hash_with_key"
        (ocaml_bytes @->
           (uint32_t @->
              (ocaml_bytes @->
                 (uint32_t @->
                    (ocaml_bytes @-> (uint32_t @-> (returning void)))))))
    let hacl_Blake2s_32_malloc_with_key =
      foreign "Hacl_Blake2s_32_malloc_with_key"
        (void @-> (returning (ptr uint32_t)))
  end