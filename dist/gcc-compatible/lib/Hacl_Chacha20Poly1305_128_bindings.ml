open Ctypes
module Bindings(F:Cstubs.FOREIGN) =
  struct
    open F
    let hacl_Chacha20Poly1305_128_aead_encrypt =
      foreign "Hacl_Chacha20Poly1305_128_aead_encrypt"
        (ocaml_bytes @->
           (ocaml_bytes @->
              (uint32_t @->
                 (ocaml_bytes @->
                    (uint32_t @->
                       (ocaml_bytes @->
                          (ocaml_bytes @-> (ocaml_bytes @-> (returning void)))))))))
    let hacl_Chacha20Poly1305_128_aead_decrypt =
      foreign "Hacl_Chacha20Poly1305_128_aead_decrypt"
        (ocaml_bytes @->
           (ocaml_bytes @->
              (uint32_t @->
                 (ocaml_bytes @->
                    (uint32_t @->
                       (ocaml_bytes @->
                          (ocaml_bytes @->
                             (ocaml_bytes @-> (returning uint32_t)))))))))
  end