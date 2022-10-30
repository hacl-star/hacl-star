open Ctypes
module Bindings(F:Cstubs.FOREIGN) =
  struct
    open F
    let hacl_HKDF_Blake2b_256_expand_blake2b_256 =
      foreign "Hacl_HKDF_Blake2b_256_expand_blake2b_256"
        (ocaml_bytes @->
           (ocaml_bytes @->
              (uint32_t @->
                 (ocaml_bytes @->
                    (uint32_t @-> (uint32_t @-> (returning void)))))))
    let hacl_HKDF_Blake2b_256_extract_blake2b_256 =
      foreign "Hacl_HKDF_Blake2b_256_extract_blake2b_256"
        (ocaml_bytes @->
           (ocaml_bytes @->
              (uint32_t @-> (ocaml_bytes @-> (uint32_t @-> (returning void))))))
  end