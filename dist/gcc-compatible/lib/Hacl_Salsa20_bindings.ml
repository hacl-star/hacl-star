open Ctypes
module Bindings(F:Cstubs.FOREIGN) =
  struct
    open F
    let hacl_Salsa20_salsa20_encrypt =
      foreign "Hacl_Salsa20_salsa20_encrypt"
        (uint32_t @->
           (ocaml_bytes @->
              (ocaml_bytes @->
                 (ocaml_bytes @->
                    (ocaml_bytes @-> (uint32_t @-> (returning void)))))))
    let hacl_Salsa20_salsa20_decrypt =
      foreign "Hacl_Salsa20_salsa20_decrypt"
        (uint32_t @->
           (ocaml_bytes @->
              (ocaml_bytes @->
                 (ocaml_bytes @->
                    (ocaml_bytes @-> (uint32_t @-> (returning void)))))))
    let hacl_Salsa20_salsa20_key_block0 =
      foreign "Hacl_Salsa20_salsa20_key_block0"
        (ocaml_bytes @-> (ocaml_bytes @-> (ocaml_bytes @-> (returning void))))
    let hacl_Salsa20_hsalsa20 =
      foreign "Hacl_Salsa20_hsalsa20"
        (ocaml_bytes @-> (ocaml_bytes @-> (ocaml_bytes @-> (returning void))))
  end