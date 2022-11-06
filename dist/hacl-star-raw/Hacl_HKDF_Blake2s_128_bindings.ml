open Ctypes
module Bindings(F:Cstubs.FOREIGN) =
  struct
    open F
    let hacl_HKDF_Blake2s_128_expand_blake2s_128 =
      foreign "Hacl_HKDF_Blake2s_128_expand_blake2s_128"
        (ocaml_bytes @->
           (ocaml_bytes @->
              (uint32_t @->
                 (ocaml_bytes @->
                    (uint32_t @-> (uint32_t @-> (returning void)))))))
    let hacl_HKDF_Blake2s_128_extract_blake2s_128 =
      foreign "Hacl_HKDF_Blake2s_128_extract_blake2s_128"
        (ocaml_bytes @->
           (ocaml_bytes @->
              (uint32_t @-> (ocaml_bytes @-> (uint32_t @-> (returning void))))))
  end