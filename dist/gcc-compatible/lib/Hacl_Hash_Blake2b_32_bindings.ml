open Ctypes
module Bindings(F:Cstubs.FOREIGN) =
  struct
    open F
    let hacl_Blake2b_32_init =
      foreign "Hacl_Blake2b_32_init"
        ((ptr uint64_t) @-> (uint32_t @-> (uint32_t @-> (returning void))))
    let hacl_Blake2b_32_update_key =
      foreign "Hacl_Blake2b_32_update_key"
        ((ptr uint64_t) @->
           ((ptr uint64_t) @->
              (uint32_t @-> (ocaml_bytes @-> (uint32_t @-> (returning void))))))
    let hacl_Blake2b_32_finish =
      foreign "Hacl_Blake2b_32_finish"
        (uint32_t @-> (ocaml_bytes @-> ((ptr uint64_t) @-> (returning void))))
    let hacl_Blake2b_32_hash_with_key =
      foreign "Hacl_Blake2b_32_hash_with_key"
        (ocaml_bytes @->
           (uint32_t @->
              (ocaml_bytes @->
                 (uint32_t @->
                    (ocaml_bytes @-> (uint32_t @-> (returning void)))))))
    let hacl_Blake2b_32_malloc_with_key =
      foreign "Hacl_Blake2b_32_malloc_with_key"
        (void @-> (returning (ptr uint64_t)))
  end