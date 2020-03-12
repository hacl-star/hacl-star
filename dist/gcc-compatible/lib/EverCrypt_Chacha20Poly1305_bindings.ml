open Ctypes
module Bindings(F:Cstubs.FOREIGN) =
  struct
    open F
    let everCrypt_Chacha20Poly1305_aead_encrypt =
      foreign "EverCrypt_Chacha20Poly1305_aead_encrypt"
        (ocaml_bytes @->
           (ocaml_bytes @->
              (uint32_t @->
                 (ocaml_bytes @->
                    (uint32_t @->
                       (ocaml_bytes @->
                          (ocaml_bytes @-> (ocaml_bytes @-> (returning void)))))))))
    let everCrypt_Chacha20Poly1305_aead_decrypt =
      foreign "EverCrypt_Chacha20Poly1305_aead_decrypt"
        (ocaml_bytes @->
           (ocaml_bytes @->
              (uint32_t @->
                 (ocaml_bytes @->
                    (uint32_t @->
                       (ocaml_bytes @->
                          (ocaml_bytes @->
                             (ocaml_bytes @-> (returning uint32_t)))))))))
  end