open Ctypes
module Bindings(F:Cstubs.FOREIGN) =
  struct
    open F
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