open Ctypes
module Bindings(F:Cstubs.FOREIGN) =
  struct
    open F
    let hacl_Hash_Core_MD5_legacy_init =
      foreign "Hacl_Hash_Core_MD5_legacy_init"
        ((ptr uint32_t) @-> (returning void))
    let hacl_Hash_Core_MD5_legacy_update =
      foreign "Hacl_Hash_Core_MD5_legacy_update"
        ((ptr uint32_t) @-> (ocaml_bytes @-> (returning void)))
    let hacl_Hash_Core_MD5_legacy_finish =
      foreign "Hacl_Hash_Core_MD5_legacy_finish"
        ((ptr uint32_t) @-> (ocaml_bytes @-> (returning void)))
    let hacl_Hash_MD5_legacy_update_multi =
      foreign "Hacl_Hash_MD5_legacy_update_multi"
        ((ptr uint32_t) @-> (ocaml_bytes @-> (uint32_t @-> (returning void))))
    let hacl_Hash_MD5_legacy_update_last =
      foreign "Hacl_Hash_MD5_legacy_update_last"
        ((ptr uint32_t) @->
           (uint64_t @-> (ocaml_bytes @-> (uint32_t @-> (returning void)))))
    let hacl_Hash_MD5_legacy_hash =
      foreign "Hacl_Hash_MD5_legacy_hash"
        (ocaml_bytes @-> (uint32_t @-> (ocaml_bytes @-> (returning void))))
  end