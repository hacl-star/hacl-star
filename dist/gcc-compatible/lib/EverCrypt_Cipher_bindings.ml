open Ctypes
module Bindings(F:Cstubs.FOREIGN) =
  struct
    open F
    let everCrypt_Cipher_chacha20 =
      foreign "EverCrypt_Cipher_chacha20"
        (uint32_t @->
           (ocaml_bytes @->
              (ocaml_bytes @->
                 (ocaml_bytes @->
                    (ocaml_bytes @-> (uint32_t @-> (returning void)))))))
  end