open Ctypes
module Bindings(F:Cstubs.FOREIGN) =
  struct
    open F
    let hacl_HKDF_expand_sha2_256 =
      foreign "Hacl_HKDF_expand_sha2_256"
        (ocaml_bytes @->
           (ocaml_bytes @->
              (uint32_t @->
                 (ocaml_bytes @->
                    (uint32_t @-> (uint32_t @-> (returning void)))))))
    let hacl_HKDF_extract_sha2_256 =
      foreign "Hacl_HKDF_extract_sha2_256"
        (ocaml_bytes @->
           (ocaml_bytes @->
              (uint32_t @-> (ocaml_bytes @-> (uint32_t @-> (returning void))))))
    let hacl_HKDF_expand_sha2_512 =
      foreign "Hacl_HKDF_expand_sha2_512"
        (ocaml_bytes @->
           (ocaml_bytes @->
              (uint32_t @->
                 (ocaml_bytes @->
                    (uint32_t @-> (uint32_t @-> (returning void)))))))
    let hacl_HKDF_extract_sha2_512 =
      foreign "Hacl_HKDF_extract_sha2_512"
        (ocaml_bytes @->
           (ocaml_bytes @->
              (uint32_t @-> (ocaml_bytes @-> (uint32_t @-> (returning void))))))
    let hacl_HKDF_expand_blake2s_32 =
      foreign "Hacl_HKDF_expand_blake2s_32"
        (ocaml_bytes @->
           (ocaml_bytes @->
              (uint32_t @->
                 (ocaml_bytes @->
                    (uint32_t @-> (uint32_t @-> (returning void)))))))
    let hacl_HKDF_extract_blake2s_32 =
      foreign "Hacl_HKDF_extract_blake2s_32"
        (ocaml_bytes @->
           (ocaml_bytes @->
              (uint32_t @-> (ocaml_bytes @-> (uint32_t @-> (returning void))))))
    let hacl_HKDF_expand_blake2b_32 =
      foreign "Hacl_HKDF_expand_blake2b_32"
        (ocaml_bytes @->
           (ocaml_bytes @->
              (uint32_t @->
                 (ocaml_bytes @->
                    (uint32_t @-> (uint32_t @-> (returning void)))))))
    let hacl_HKDF_extract_blake2b_32 =
      foreign "Hacl_HKDF_extract_blake2b_32"
        (ocaml_bytes @->
           (ocaml_bytes @->
              (uint32_t @-> (ocaml_bytes @-> (uint32_t @-> (returning void))))))
  end