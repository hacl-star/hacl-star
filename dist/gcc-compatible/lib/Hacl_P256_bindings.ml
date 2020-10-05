open Ctypes
module Bindings(F:Cstubs.FOREIGN) =
  struct
    open F
    let hacl_Impl_P256_LowLevel_toUint8 =
      foreign "Hacl_Impl_P256_LowLevel_toUint8"
        ((ptr uint64_t) @-> (ocaml_bytes @-> (returning void)))
    let hacl_Impl_P256_LowLevel_changeEndian =
      foreign "Hacl_Impl_P256_LowLevel_changeEndian"
        ((ptr uint64_t) @-> (returning void))
    let hacl_Impl_P256_LowLevel_toUint64ChangeEndian =
      foreign "Hacl_Impl_P256_LowLevel_toUint64ChangeEndian"
        (ocaml_bytes @-> ((ptr uint64_t) @-> (returning void)))
    let hacl_Impl_P256_Core_isPointAtInfinityPrivate =
      foreign "Hacl_Impl_P256_Core_isPointAtInfinityPrivate"
        ((ptr uint64_t) @-> (returning uint64_t))
    let hacl_Impl_P256_Core_secretToPublic =
      foreign "Hacl_Impl_P256_Core_secretToPublic"
        ((ptr uint64_t) @->
           (ocaml_bytes @-> ((ptr uint64_t) @-> (returning void))))
    let hacl_Impl_P256_DH__ecp256dh_r =
      foreign "Hacl_Impl_P256_DH__ecp256dh_r"
        ((ptr uint64_t) @->
           ((ptr uint64_t) @-> (ocaml_bytes @-> (returning uint64_t))))
    let hacl_P256_ecdsa_sign_p256_sha2 =
      foreign "Hacl_P256_ecdsa_sign_p256_sha2"
        (ocaml_bytes @->
           (uint32_t @->
              (ocaml_bytes @->
                 (ocaml_bytes @-> (ocaml_bytes @-> (returning bool))))))
    let hacl_P256_ecdsa_sign_p256_sha384 =
      foreign "Hacl_P256_ecdsa_sign_p256_sha384"
        (ocaml_bytes @->
           (uint32_t @->
              (ocaml_bytes @->
                 (ocaml_bytes @-> (ocaml_bytes @-> (returning bool))))))
    let hacl_P256_ecdsa_sign_p256_sha512 =
      foreign "Hacl_P256_ecdsa_sign_p256_sha512"
        (ocaml_bytes @->
           (uint32_t @->
              (ocaml_bytes @->
                 (ocaml_bytes @-> (ocaml_bytes @-> (returning bool))))))
    let hacl_P256_ecdsa_sign_p256_without_hash =
      foreign "Hacl_P256_ecdsa_sign_p256_without_hash"
        (ocaml_bytes @->
           (uint32_t @->
              (ocaml_bytes @->
                 (ocaml_bytes @-> (ocaml_bytes @-> (returning bool))))))
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
    let hacl_P256_ecp256dh_i =
      foreign "Hacl_P256_ecp256dh_i"
        (ocaml_bytes @-> (ocaml_bytes @-> (returning bool)))
    let hacl_P256_ecp256dh_r =
      foreign "Hacl_P256_ecp256dh_r"
        (ocaml_bytes @-> (ocaml_bytes @-> (ocaml_bytes @-> (returning bool))))
    let hacl_P256_is_more_than_zero_less_than_order =
      foreign "Hacl_P256_is_more_than_zero_less_than_order"
        (ocaml_bytes @-> (returning bool))
  end