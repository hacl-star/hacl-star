open Ctypes
module Bindings(F:Cstubs.FOREIGN) =
  struct
    open F
    let hacl_Hash_Blake2b_Simd256_hash_with_key =
      foreign "Hacl_Hash_Blake2b_Simd256_hash_with_key"
        (ocaml_bytes @->
           (uint32_t @->
              (ocaml_bytes @->
                 (uint32_t @->
                    (ocaml_bytes @-> (uint32_t @-> (returning void)))))))
  end