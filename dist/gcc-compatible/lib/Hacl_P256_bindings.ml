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
      
    let hacl_Interface_P256_ecdsa_sign_p256_sha2 =
      foreign "Hacl_Interface_P256_ecdsa_sign_p256_sha2"
        (ocaml_bytes @->
           (uint32_t @->
              (ocaml_bytes @->
                 (ocaml_bytes @-> (ocaml_bytes @-> (returning uint64_t))))))
      
    let hacl_Interface_P256_ecdsa_sign_p256_sha384 =
      foreign "Hacl_Interface_P256_ecdsa_sign_p256_sha384"
        (ocaml_bytes @->
           (uint32_t @->
              (ocaml_bytes @->
                 (ocaml_bytes @-> (ocaml_bytes @-> (returning uint64_t))))))
      
    let hacl_Interface_P256_ecdsa_sign_p256_sha512 =
      foreign "Hacl_Interface_P256_ecdsa_sign_p256_sha512"
        (ocaml_bytes @->
           (uint32_t @->
              (ocaml_bytes @->
                 (ocaml_bytes @-> (ocaml_bytes @-> (returning uint64_t))))))
      
    let hacl_Interface_P256_ecdsa_sign_p256_without_hash =
      foreign "Hacl_Interface_P256_ecdsa_sign_p256_without_hash"
        (ocaml_bytes @->
           (uint32_t @->
              (ocaml_bytes @->
                 (ocaml_bytes @-> (ocaml_bytes @-> (returning uint64_t))))))
      
    let hacl_Interface_P256_ecdsa_verif_p256_sha2 =
      foreign "Hacl_Interface_P256_ecdsa_verif_p256_sha2"
        (uint32_t @->
           (ocaml_bytes @->
              (ocaml_bytes @->
                 (ocaml_bytes @-> (ocaml_bytes @-> (returning bool))))))
      
    let hacl_Interface_P256_ecdsa_verif_p256_sha384 =
      foreign "Hacl_Interface_P256_ecdsa_verif_p256_sha384"
        (uint32_t @->
           (ocaml_bytes @->
              (ocaml_bytes @->
                 (ocaml_bytes @-> (ocaml_bytes @-> (returning bool))))))
      
    let hacl_Interface_P256_ecdsa_verif_p256_sha512 =
      foreign "Hacl_Interface_P256_ecdsa_verif_p256_sha512"
        (uint32_t @->
           (ocaml_bytes @->
              (ocaml_bytes @->
                 (ocaml_bytes @-> (ocaml_bytes @-> (returning bool))))))
      
    let hacl_Interface_P256_ecdsa_verif_without_hash =
      foreign "Hacl_Interface_P256_ecdsa_verif_without_hash"
        (uint32_t @->
           (ocaml_bytes @->
              (ocaml_bytes @->
                 (ocaml_bytes @-> (ocaml_bytes @-> (returning bool))))))
      
    let hacl_Interface_P256_verifyQ =
      foreign "Hacl_Interface_P256_verifyQ"
        (ocaml_bytes @-> (returning bool))
      
    let hacl_Interface_P256_decompressionNotCompressedForm =
      foreign "Hacl_Interface_P256_decompressionNotCompressedForm"
        (ocaml_bytes @-> (ocaml_bytes @-> (returning bool)))
      
    let hacl_Interface_P256_decompressionCompressedForm =
      foreign "Hacl_Interface_P256_decompressionCompressedForm"
        (ocaml_bytes @-> (ocaml_bytes @-> (returning bool)))
      
    let hacl_Interface_P256_compressionNotCompressedForm =
      foreign "Hacl_Interface_P256_compressionNotCompressedForm"
        (ocaml_bytes @-> (ocaml_bytes @-> (returning void)))
      
    let hacl_Interface_P256_compressionCompressedForm =
      foreign "Hacl_Interface_P256_compressionCompressedForm"
        (ocaml_bytes @-> (ocaml_bytes @-> (returning void)))
      
    let hacl_Interface_P256_reduction_8_32 =
      foreign "Hacl_Interface_P256_reduction_8_32"
        (ocaml_bytes @-> (ocaml_bytes @-> (returning void)))
      
    let hacl_Interface_P256_ecp256dh_i =
      foreign "Hacl_Interface_P256_ecp256dh_i"
        (ocaml_bytes @-> (ocaml_bytes @-> (returning uint64_t)))
      
    let hacl_Interface_P256_ecp256dh_r =
      foreign "Hacl_Interface_P256_ecp256dh_r"
        (ocaml_bytes @->
           (ocaml_bytes @-> (ocaml_bytes @-> (returning uint64_t))))
      
  end