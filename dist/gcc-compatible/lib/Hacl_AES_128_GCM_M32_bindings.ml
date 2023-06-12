open Ctypes
module Bindings(F:Cstubs.FOREIGN) =
  struct
    open F
    let hacl_AES_128_GCM_M32_aes_gcm_ctx_len =
      foreign_value "Hacl_AES_128_GCM_M32_aes_gcm_ctx_len" uint32_t
    let hacl_AES_128_GCM_M32_aes128_gcm_init =
      foreign "Hacl_AES_128_GCM_M32_aes128_gcm_init"
        ((ptr uint64_t) @->
           (ocaml_bytes @-> (ocaml_bytes @-> (returning void))))
    let hacl_AES_128_GCM_M32_aes128_gcm_encrypt =
      foreign "Hacl_AES_128_GCM_M32_aes128_gcm_encrypt"
        ((ptr uint64_t) @->
           (uint32_t @->
              (ocaml_bytes @->
                 (ocaml_bytes @->
                    (uint32_t @-> (ocaml_bytes @-> (returning void)))))))
    let hacl_AES_128_GCM_M32_aes128_gcm_decrypt =
      foreign "Hacl_AES_128_GCM_M32_aes128_gcm_decrypt"
        ((ptr uint64_t) @->
           (uint32_t @->
              (ocaml_bytes @->
                 (ocaml_bytes @->
                    (uint32_t @-> (ocaml_bytes @-> (returning bool)))))))
  end