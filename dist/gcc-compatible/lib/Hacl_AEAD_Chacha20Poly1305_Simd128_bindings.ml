open Ctypes
module Bindings(F:Cstubs.FOREIGN) =
  struct
    open F
    let hacl_AEAD_Chacha20Poly1305_Simd128_encrypt =
      foreign "Hacl_AEAD_Chacha20Poly1305_Simd128_encrypt"
        (ocaml_bytes @->
           (ocaml_bytes @->
              (ocaml_bytes @->
                 (uint32_t @->
                    (ocaml_bytes @->
                       (uint32_t @->
                          (ocaml_bytes @-> (ocaml_bytes @-> (returning void)))))))))
    let hacl_AEAD_Chacha20Poly1305_Simd128_decrypt =
      foreign "Hacl_AEAD_Chacha20Poly1305_Simd128_decrypt"
        (ocaml_bytes @->
           (ocaml_bytes @->
              (uint32_t @->
                 (ocaml_bytes @->
                    (uint32_t @->
                       (ocaml_bytes @->
                          (ocaml_bytes @->
                             (ocaml_bytes @-> (returning uint32_t)))))))))
  end