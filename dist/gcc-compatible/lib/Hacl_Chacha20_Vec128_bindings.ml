open Ctypes
module Bindings(F:Cstubs.FOREIGN) =
  struct
    open F
    let hacl_Chacha20_Vec128_chacha20_encrypt_128 =
      foreign "Hacl_Chacha20_Vec128_chacha20_encrypt_128"
        (uint32_t @->
           (ocaml_bytes @->
              (ocaml_bytes @->
                 (ocaml_bytes @->
                    (ocaml_bytes @-> (uint32_t @-> (returning void)))))))
    let hacl_Chacha20_Vec128_chacha20_decrypt_128 =
      foreign "Hacl_Chacha20_Vec128_chacha20_decrypt_128"
        (uint32_t @->
           (ocaml_bytes @->
              (ocaml_bytes @->
                 (ocaml_bytes @->
                    (ocaml_bytes @-> (uint32_t @-> (returning void)))))))
  end