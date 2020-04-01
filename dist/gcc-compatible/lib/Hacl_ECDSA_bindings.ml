open Ctypes
module Bindings(F:Cstubs.FOREIGN) =
  struct
    open F
    let hacl_Impl_P256_DH_ecp256dh_i =
      foreign "Hacl_Impl_P256_DH_ecp256dh_i"
        (ocaml_bytes @-> (ocaml_bytes @-> (returning uint64_t)))
      
    let hacl_Impl_P256_DH_ecp256dh_r =
      foreign "Hacl_Impl_P256_DH_ecp256dh_r"
        (ocaml_bytes @->
           (ocaml_bytes @-> (ocaml_bytes @-> (returning uint64_t))))
      
    let hacl_Impl_ECDSA_secretToPublicU8 =
      foreign "Hacl_Impl_ECDSA_secretToPublicU8"
        (ocaml_bytes @->
           (ocaml_bytes @-> ((ptr uint64_t) @-> (returning void))))
      
    let hacl_Impl_ECDSA_ecdsa_p256_sha2_sign =
      foreign "Hacl_Impl_ECDSA_ecdsa_p256_sha2_sign"
        (ocaml_bytes @->
           (uint32_t @->
              (ocaml_bytes @->
                 (ocaml_bytes @-> (ocaml_bytes @-> (returning uint64_t))))))
      
    let hacl_Impl_ECDSA_ecdsa_p256_sha2_384_sign =
      foreign "Hacl_Impl_ECDSA_ecdsa_p256_sha2_384_sign"
        (ocaml_bytes @->
           (uint32_t @->
              (ocaml_bytes @->
                 (ocaml_bytes @-> (ocaml_bytes @-> (returning uint64_t))))))
      
    let hacl_Impl_ECDSA_ecdsa_p256_sha2_512_sign =
      foreign "Hacl_Impl_ECDSA_ecdsa_p256_sha2_512_sign"
        (ocaml_bytes @->
           (uint32_t @->
              (ocaml_bytes @->
                 (ocaml_bytes @-> (ocaml_bytes @-> (returning uint64_t))))))
      
    let hacl_Impl_ECDSA_ecdsa_signature_blake2 =
      foreign "Hacl_Impl_ECDSA_ecdsa_signature_blake2"
        (ocaml_bytes @->
           (uint32_t @->
              (ocaml_bytes @->
                 (ocaml_bytes @-> (ocaml_bytes @-> (returning uint64_t))))))
      
    let hacl_Impl_ECDSA_ecdsa_p256_sha2_verification =
      foreign "Hacl_Impl_ECDSA_ecdsa_p256_sha2_verification"
        (uint32_t @->
           (ocaml_bytes @->
              (ocaml_bytes @->
                 (ocaml_bytes @-> (ocaml_bytes @-> (returning bool))))))
      
    let hacl_Impl_ECDSA_ecdsa_verification_blake2 =
      foreign "Hacl_Impl_ECDSA_ecdsa_verification_blake2"
        (uint32_t @->
           (ocaml_bytes @->
              (ocaml_bytes @->
                 (ocaml_bytes @-> (ocaml_bytes @-> (returning bool))))))
      
    let hacl_Impl_ECDSA_ecdsa_verification_blake2hl =
      foreign "Hacl_Impl_ECDSA_ecdsa_verification_blake2hl"
        (uint32_t @->
           (ocaml_bytes @->
              (ocaml_bytes @->
                 (ocaml_bytes @-> (ocaml_bytes @-> (returning bool))))))
      
    let hacl_Impl_ECDSA_decompressionNotCompressedForm =
      foreign "Hacl_Impl_ECDSA_decompressionNotCompressedForm"
        (ocaml_bytes @-> (ocaml_bytes @-> (returning bool)))
      
    let hacl_Impl_ECDSA_decompressionCompressedForm =
      foreign "Hacl_Impl_ECDSA_decompressionCompressedForm"
        (ocaml_bytes @-> (ocaml_bytes @-> (returning bool)))
      
    let hacl_Impl_ECDSA_compressionNotCompressedForm =
      foreign "Hacl_Impl_ECDSA_compressionNotCompressedForm"
        (ocaml_bytes @-> (ocaml_bytes @-> (returning void)))
      
    let hacl_Impl_ECDSA_compressionCompressedForm =
      foreign "Hacl_Impl_ECDSA_compressionCompressedForm"
        (ocaml_bytes @-> (ocaml_bytes @-> (returning void)))
      
  end