open Ctypes
module Bindings(F:Cstubs.FOREIGN) =
  struct
    open F
    let hacl_Hash_Core_SHA2_init_224 =
      foreign "Hacl_Hash_Core_SHA2_init_224"
        ((ptr uint32_t) @-> (returning void))
    let hacl_Hash_Core_SHA2_init_256 =
      foreign "Hacl_Hash_Core_SHA2_init_256"
        ((ptr uint32_t) @-> (returning void))
    let hacl_Hash_Core_SHA2_init_384 =
      foreign "Hacl_Hash_Core_SHA2_init_384"
        ((ptr uint64_t) @-> (returning void))
    let hacl_Hash_Core_SHA2_init_512 =
      foreign "Hacl_Hash_Core_SHA2_init_512"
        ((ptr uint64_t) @-> (returning void))
    let hacl_Hash_Core_SHA2_update_384 =
      foreign "Hacl_Hash_Core_SHA2_update_384"
        ((ptr uint64_t) @-> (ocaml_bytes @-> (returning void)))
    let hacl_Hash_Core_SHA2_update_512 =
      foreign "Hacl_Hash_Core_SHA2_update_512"
        ((ptr uint64_t) @-> (ocaml_bytes @-> (returning void)))
    let hacl_Hash_Core_SHA2_pad_256 =
      foreign "Hacl_Hash_Core_SHA2_pad_256"
        (uint64_t @-> (ocaml_bytes @-> (returning void)))
    let hacl_Hash_Core_SHA2_finish_224 =
      foreign "Hacl_Hash_Core_SHA2_finish_224"
        ((ptr uint32_t) @-> (ocaml_bytes @-> (returning void)))
    let hacl_Hash_Core_SHA2_finish_256 =
      foreign "Hacl_Hash_Core_SHA2_finish_256"
        ((ptr uint32_t) @-> (ocaml_bytes @-> (returning void)))
    let hacl_Hash_Core_SHA2_finish_384 =
      foreign "Hacl_Hash_Core_SHA2_finish_384"
        ((ptr uint64_t) @-> (ocaml_bytes @-> (returning void)))
    let hacl_Hash_Core_SHA2_finish_512 =
      foreign "Hacl_Hash_Core_SHA2_finish_512"
        ((ptr uint64_t) @-> (ocaml_bytes @-> (returning void)))
    let hacl_Hash_SHA2_update_multi_224 =
      foreign "Hacl_Hash_SHA2_update_multi_224"
        ((ptr uint32_t) @-> (ocaml_bytes @-> (uint32_t @-> (returning void))))
    let hacl_Hash_SHA2_update_multi_256 =
      foreign "Hacl_Hash_SHA2_update_multi_256"
        ((ptr uint32_t) @-> (ocaml_bytes @-> (uint32_t @-> (returning void))))
    let hacl_Hash_SHA2_update_multi_384 =
      foreign "Hacl_Hash_SHA2_update_multi_384"
        ((ptr uint64_t) @-> (ocaml_bytes @-> (uint32_t @-> (returning void))))
    let hacl_Hash_SHA2_update_multi_512 =
      foreign "Hacl_Hash_SHA2_update_multi_512"
        ((ptr uint64_t) @-> (ocaml_bytes @-> (uint32_t @-> (returning void))))
    let hacl_Hash_SHA2_update_last_224 =
      foreign "Hacl_Hash_SHA2_update_last_224"
        ((ptr uint32_t) @->
           (uint64_t @-> (ocaml_bytes @-> (uint32_t @-> (returning void)))))
    let hacl_Hash_SHA2_update_last_256 =
      foreign "Hacl_Hash_SHA2_update_last_256"
        ((ptr uint32_t) @->
           (uint64_t @-> (ocaml_bytes @-> (uint32_t @-> (returning void)))))
    let hacl_Hash_SHA2_hash_224 =
      foreign "Hacl_Hash_SHA2_hash_224"
        (ocaml_bytes @-> (uint32_t @-> (ocaml_bytes @-> (returning void))))
    let hacl_Hash_SHA2_hash_256 =
      foreign "Hacl_Hash_SHA2_hash_256"
        (ocaml_bytes @-> (uint32_t @-> (ocaml_bytes @-> (returning void))))
    let hacl_Hash_SHA2_hash_384 =
      foreign "Hacl_Hash_SHA2_hash_384"
        (ocaml_bytes @-> (uint32_t @-> (ocaml_bytes @-> (returning void))))
    let hacl_Hash_SHA2_hash_512 =
      foreign "Hacl_Hash_SHA2_hash_512"
        (ocaml_bytes @-> (uint32_t @-> (ocaml_bytes @-> (returning void))))
  end