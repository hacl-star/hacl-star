open Ctypes
module Bindings(F:Cstubs.FOREIGN) =
  struct
    open F
    let hacl_Impl_AES_CoreBitSlice_store_block0 =
      foreign "Hacl_Impl_AES_CoreBitSlice_store_block0"
        (ocaml_bytes @-> ((ptr uint64_t) @-> (returning void)))
    let hacl_Impl_AES_CoreBitSlice_load_key1 =
      foreign "Hacl_Impl_AES_CoreBitSlice_load_key1"
        ((ptr uint64_t) @-> (ocaml_bytes @-> (returning void)))
    let hacl_Impl_AES_CoreBitSlice_load_nonce =
      foreign "Hacl_Impl_AES_CoreBitSlice_load_nonce"
        ((ptr uint64_t) @-> (ocaml_bytes @-> (returning void)))
    let hacl_Impl_AES_CoreBitSlice_load_state =
      foreign "Hacl_Impl_AES_CoreBitSlice_load_state"
        ((ptr uint64_t) @->
           ((ptr uint64_t) @-> (uint32_t @-> (returning void))))
    let hacl_Impl_AES_CoreBitSlice_xor_state_key1 =
      foreign "Hacl_Impl_AES_CoreBitSlice_xor_state_key1"
        ((ptr uint64_t) @-> ((ptr uint64_t) @-> (returning void)))
    let hacl_Impl_AES_CoreBitSlice_aes_enc =
      foreign "Hacl_Impl_AES_CoreBitSlice_aes_enc"
        ((ptr uint64_t) @-> ((ptr uint64_t) @-> (returning void)))
    let hacl_Impl_AES_CoreBitSlice_aes_enc_last =
      foreign "Hacl_Impl_AES_CoreBitSlice_aes_enc_last"
        ((ptr uint64_t) @-> ((ptr uint64_t) @-> (returning void)))
    let hacl_Impl_AES_CoreBitSlice_aes_keygen_assist =
      foreign "Hacl_Impl_AES_CoreBitSlice_aes_keygen_assist"
        ((ptr uint64_t) @->
           ((ptr uint64_t) @-> (uint8_t @-> (returning void))))
    let hacl_Impl_AES_CoreBitSlice_key_expansion_step =
      foreign "Hacl_Impl_AES_CoreBitSlice_key_expansion_step"
        ((ptr uint64_t) @-> ((ptr uint64_t) @-> (returning void)))
    let hacl_Impl_AES_Generic_aes128_ctr_bitslice =
      foreign "Hacl_Impl_AES_Generic_aes128_ctr_bitslice"
        (uint32_t @->
           (ocaml_bytes @->
              (ocaml_bytes @->
                 ((ptr uint64_t) @-> (uint32_t @-> (returning void))))))
    let hacl_Impl_AES_Generic_aes256_ctr_bitslice =
      foreign "Hacl_Impl_AES_Generic_aes256_ctr_bitslice"
        (uint32_t @->
           (ocaml_bytes @->
              (ocaml_bytes @->
                 ((ptr uint64_t) @-> (uint32_t @-> (returning void))))))
    let hacl_AES_128_BitSlice_aes128_init =
      foreign "Hacl_AES_128_BitSlice_aes128_init"
        ((ptr uint64_t) @->
           (ocaml_bytes @-> (ocaml_bytes @-> (returning void))))
    let hacl_AES_128_BitSlice_aes128_set_nonce =
      foreign "Hacl_AES_128_BitSlice_aes128_set_nonce"
        ((ptr uint64_t) @-> (ocaml_bytes @-> (returning void)))
    let hacl_AES_128_BitSlice_aes128_key_block =
      foreign "Hacl_AES_128_BitSlice_aes128_key_block"
        (ocaml_bytes @-> ((ptr uint64_t) @-> (uint32_t @-> (returning void))))
    let hacl_AES_128_BitSlice_aes128_ctr_encrypt =
      foreign "Hacl_AES_128_BitSlice_aes128_ctr_encrypt"
        (uint32_t @->
           (ocaml_bytes @->
              (ocaml_bytes @->
                 (ocaml_bytes @->
                    (ocaml_bytes @-> (uint32_t @-> (returning void)))))))
    let hacl_AES_128_BitSlice_aes128_ctr_decrypt =
      foreign "Hacl_AES_128_BitSlice_aes128_ctr_decrypt"
        (uint32_t @->
           (ocaml_bytes @->
              (ocaml_bytes @->
                 (ocaml_bytes @->
                    (ocaml_bytes @-> (uint32_t @-> (returning void)))))))
  end