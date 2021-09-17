open Ctypes
module Bindings(F:Cstubs.FOREIGN) =
  struct
    open F
    let hacl_Hash_Blake2s_128_hash_blake2s_128 =
      foreign "Hacl_Hash_Blake2s_128_hash_blake2s_128"
        (ocaml_bytes @-> (uint32_t @-> (ocaml_bytes @-> (returning void))))
    let hacl_Blake2s_128_blake2s =
      foreign "Hacl_Blake2s_128_blake2s"
        (uint32_t @->
           (ocaml_bytes @->
              (uint32_t @->
                 (ocaml_bytes @->
                    (uint32_t @-> (ocaml_bytes @-> (returning void)))))))
  end