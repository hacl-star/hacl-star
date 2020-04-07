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
      
    let hacl_Impl_ECDSA_ecdsa_sign_p256_sha2 =
      foreign "Hacl_Impl_ECDSA_ecdsa_sign_p256_sha2"
        (ocaml_bytes @->
           (uint32_t @->
              (ocaml_bytes @->
                 (ocaml_bytes @-> (ocaml_bytes @-> (returning uint64_t))))))
      
    let hacl_Impl_ECDSA_ecdsa_sign_p256_blake2 =
      foreign "Hacl_Impl_ECDSA_ecdsa_sign_p256_blake2"
        (ocaml_bytes @->
           (uint32_t @->
              (ocaml_bytes @->
                 (ocaml_bytes @-> (ocaml_bytes @-> (returning uint64_t))))))
      
    let hacl_Impl_ECDSA_ecdsa_sign_p256_without_hash =
      foreign "Hacl_Impl_ECDSA_ecdsa_sign_p256_without_hash"
        (ocaml_bytes @->
           (ocaml_bytes @->
              (ocaml_bytes @-> (ocaml_bytes @-> (returning uint64_t)))))
      
    let hacl_Impl_ECDSA_ecdsa_verif_p256_sha2 =
      foreign "Hacl_Impl_ECDSA_ecdsa_verif_p256_sha2"
        (uint32_t @->
           (ocaml_bytes @->
              (ocaml_bytes @->
                 (ocaml_bytes @-> (ocaml_bytes @-> (returning bool))))))
      
    let hacl_Impl_ECDSA_ecdsa_verif_blake2 =
      foreign "Hacl_Impl_ECDSA_ecdsa_verif_blake2"
        (uint32_t @->
           (ocaml_bytes @->
              (ocaml_bytes @->
                 (ocaml_bytes @-> (ocaml_bytes @-> (returning bool))))))
      
    let hacl_Impl_ECDSA_ecdsa_verif_without_hash =
      foreign "Hacl_Impl_ECDSA_ecdsa_verif_without_hash"
        (ocaml_bytes @->
           (ocaml_bytes @->
              (ocaml_bytes @-> (ocaml_bytes @-> (returning bool)))))
      
    let hacl_Impl_ECDSA_verifyQ =
      foreign "Hacl_Impl_ECDSA_verifyQ" (ocaml_bytes @-> (returning bool)) 
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
      
    let hacl_Impl_ECDSA_Reduction_reduction_8_32 =
      foreign "Hacl_Impl_ECDSA_Reduction_reduction_8_32"
        (ocaml_bytes @-> (ocaml_bytes @-> (returning void)))
      
  end