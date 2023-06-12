open Ctypes
module Bindings(F:Cstubs.FOREIGN) =
  struct
    open F
    let hacl_AES_256_BitSlice_aes256_init =
      foreign "Hacl_AES_256_BitSlice_aes256_init"
        ((ptr uint64_t) @->
           (ocaml_bytes @-> (ocaml_bytes @-> (returning void))))
    let hacl_AES_256_BitSlice_aes256_set_nonce =
      foreign "Hacl_AES_256_BitSlice_aes256_set_nonce"
        ((ptr uint64_t) @-> (ocaml_bytes @-> (returning void)))
    let hacl_AES_256_BitSlice_aes256_key_block =
      foreign "Hacl_AES_256_BitSlice_aes256_key_block"
        (ocaml_bytes @-> ((ptr uint64_t) @-> (uint32_t @-> (returning void))))
    let hacl_AES_256_BitSlice_aes256_ctr =
      foreign "Hacl_AES_256_BitSlice_aes256_ctr"
        (uint32_t @->
           (ocaml_bytes @->
              (ocaml_bytes @->
                 ((ptr uint64_t) @-> (uint32_t @-> (returning void))))))
    let hacl_AES_256_BitSlice_aes256_ctr_encrypt =
      foreign "Hacl_AES_256_BitSlice_aes256_ctr_encrypt"
        (uint32_t @->
           (ocaml_bytes @->
              (ocaml_bytes @->
                 (ocaml_bytes @->
                    (ocaml_bytes @-> (uint32_t @-> (returning void)))))))
    let hacl_AES_256_BitSlice_aes256_ctr_decrypt =
      foreign "Hacl_AES_256_BitSlice_aes256_ctr_decrypt"
        (uint32_t @->
           (ocaml_bytes @->
              (ocaml_bytes @->
                 (ocaml_bytes @->
                    (ocaml_bytes @-> (uint32_t @-> (returning void)))))))
  end