open Ctypes
module Bindings(F:Cstubs.FOREIGN) =
  struct
    open F
    let hacl_Chacha20_Vec512_chacha20_encrypt_512 =
      foreign "Hacl_Chacha20_Vec512_chacha20_encrypt_512"
        (uint32_t @->
           (ocaml_bytes @->
              (ocaml_bytes @->
                 (ocaml_bytes @->
                    (ocaml_bytes @-> (uint32_t @-> (returning void)))))))
    let hacl_Chacha20_Vec512_chacha20_decrypt_512 =
      foreign "Hacl_Chacha20_Vec512_chacha20_decrypt_512"
        (uint32_t @->
           (ocaml_bytes @->
              (ocaml_bytes @->
                 (ocaml_bytes @->
                    (ocaml_bytes @-> (uint32_t @-> (returning void)))))))
  end