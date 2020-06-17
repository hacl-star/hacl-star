open Ctypes
module Bindings(F:Cstubs.FOREIGN) =
  struct
    open F
    let hacl_Impl_Chacha20_chacha20_init =
      foreign "Hacl_Impl_Chacha20_chacha20_init"
        ((ptr uint32_t) @->
           (ocaml_bytes @-> (ocaml_bytes @-> (uint32_t @-> (returning void)))))
    let hacl_Impl_Chacha20_chacha20_encrypt_block =
      foreign "Hacl_Impl_Chacha20_chacha20_encrypt_block"
        ((ptr uint32_t) @->
           (ocaml_bytes @-> (uint32_t @-> (ocaml_bytes @-> (returning void)))))
    let hacl_Impl_Chacha20_chacha20_update =
      foreign "Hacl_Impl_Chacha20_chacha20_update"
        ((ptr uint32_t) @->
           (uint32_t @-> (ocaml_bytes @-> (ocaml_bytes @-> (returning void)))))
    let hacl_Chacha20_chacha20_encrypt =
      foreign "Hacl_Chacha20_chacha20_encrypt"
        (uint32_t @->
           (ocaml_bytes @->
              (ocaml_bytes @->
                 (ocaml_bytes @->
                    (ocaml_bytes @-> (uint32_t @-> (returning void)))))))
    let hacl_Chacha20_chacha20_decrypt =
      foreign "Hacl_Chacha20_chacha20_decrypt"
        (uint32_t @->
           (ocaml_bytes @->
              (ocaml_bytes @->
                 (ocaml_bytes @->
                    (ocaml_bytes @-> (uint32_t @-> (returning void)))))))
  end