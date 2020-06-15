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
      
    let hacl_P256_ecdsa_sign_p256_sha2 =
      foreign "Hacl_P256_ecdsa_sign_p256_sha2"
        (ocaml_bytes @->
           (uint32_t @->
              (ocaml_bytes @->
                 (ocaml_bytes @-> (ocaml_bytes @-> (returning uint64_t))))))
      
    let hacl_P256_ecdsa_sign_p256_sha384 =
      foreign "Hacl_P256_ecdsa_sign_p256_sha384"
        (ocaml_bytes @->
           (uint32_t @->
              (ocaml_bytes @->
                 (ocaml_bytes @-> (ocaml_bytes @-> (returning uint64_t))))))
      
    let hacl_P256_ecdsa_sign_p256_sha512 =
      foreign "Hacl_P256_ecdsa_sign_p256_sha512"
        (ocaml_bytes @->
           (uint32_t @->
              (ocaml_bytes @->
                 (ocaml_bytes @-> (ocaml_bytes @-> (returning uint64_t))))))
      
    let hacl_P256_ecdsa_sign_p256_without_hash =
      foreign "Hacl_P256_ecdsa_sign_p256_without_hash"
        (ocaml_bytes @->
           (uint32_t @->
              (ocaml_bytes @->
                 (ocaml_bytes @-> (ocaml_bytes @-> (returning uint64_t))))))
      
    let hacl_P256_ecdsa_verif_p256_sha2 =
      foreign "Hacl_P256_ecdsa_verif_p256_sha2"
        (uint32_t @->
           (ocaml_bytes @->
              (ocaml_bytes @->
                 (ocaml_bytes @-> (ocaml_bytes @-> (returning bool))))))
      
    let hacl_P256_ecdsa_verif_p256_sha384 =
      foreign "Hacl_P256_ecdsa_verif_p256_sha384"
        (uint32_t @->
           (ocaml_bytes @->
              (ocaml_bytes @->
                 (ocaml_bytes @-> (ocaml_bytes @-> (returning bool))))))
      
    let hacl_P256_ecdsa_verif_p256_sha512 =
      foreign "Hacl_P256_ecdsa_verif_p256_sha512"
        (uint32_t @->
           (ocaml_bytes @->
              (ocaml_bytes @->
                 (ocaml_bytes @-> (ocaml_bytes @-> (returning bool))))))
      
    let hacl_P256_ecdsa_verif_without_hash =
      foreign "Hacl_P256_ecdsa_verif_without_hash"
        (uint32_t @->
           (ocaml_bytes @->
              (ocaml_bytes @->
                 (ocaml_bytes @-> (ocaml_bytes @-> (returning bool))))))
      
    let hacl_P256_verify_q =
      foreign "Hacl_P256_verify_q" (ocaml_bytes @-> (returning bool)) 
    let hacl_P256_decompression_not_compressed_form =
      foreign "Hacl_P256_decompression_not_compressed_form"
        (ocaml_bytes @-> (ocaml_bytes @-> (returning bool)))
      
    let hacl_P256_decompression_compressed_form =
      foreign "Hacl_P256_decompression_compressed_form"
        (ocaml_bytes @-> (ocaml_bytes @-> (returning bool)))
      
    let hacl_P256_compression_not_compressed_form =
      foreign "Hacl_P256_compression_not_compressed_form"
        (ocaml_bytes @-> (ocaml_bytes @-> (returning void)))
      
    let hacl_P256_compression_compressed_form =
      foreign "Hacl_P256_compression_compressed_form"
        (ocaml_bytes @-> (ocaml_bytes @-> (returning void)))
      
    let hacl_P256_reduction_8_32 =
      foreign "Hacl_P256_reduction_8_32"
        (ocaml_bytes @-> (ocaml_bytes @-> (returning void)))
      
    let hacl_P256_ecp256dh_i =
      foreign "Hacl_P256_ecp256dh_i"
        (ocaml_bytes @-> (ocaml_bytes @-> (returning uint64_t)))
      
    let hacl_P256_ecp256dh_r =
      foreign "Hacl_P256_ecp256dh_r"
        (ocaml_bytes @->
           (ocaml_bytes @-> (ocaml_bytes @-> (returning uint64_t))))
      
  end