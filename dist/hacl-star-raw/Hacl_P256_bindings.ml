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
    let hacl_P256_validate_public_key =
      foreign "Hacl_P256_validate_public_key"
        (ocaml_bytes @-> (returning bool))
    let hacl_P256_validate_private_key =
      foreign "Hacl_P256_validate_private_key"
        (ocaml_bytes @-> (returning bool))
    let hacl_P256_uncompressed_to_raw =
      foreign "Hacl_P256_uncompressed_to_raw"
        (ocaml_bytes @-> (ocaml_bytes @-> (returning bool)))
    let hacl_P256_compressed_to_raw =
      foreign "Hacl_P256_compressed_to_raw"
        (ocaml_bytes @-> (ocaml_bytes @-> (returning bool)))
    let hacl_P256_raw_to_uncompressed =
      foreign "Hacl_P256_raw_to_uncompressed"
        (ocaml_bytes @-> (ocaml_bytes @-> (returning void)))
    let hacl_P256_raw_to_compressed =
      foreign "Hacl_P256_raw_to_compressed"
        (ocaml_bytes @-> (ocaml_bytes @-> (returning void)))
    let hacl_P256_dh_initiator =
      foreign "Hacl_P256_dh_initiator"
        (ocaml_bytes @-> (ocaml_bytes @-> (returning bool)))
    let hacl_P256_dh_responder =
      foreign "Hacl_P256_dh_responder"
        (ocaml_bytes @-> (ocaml_bytes @-> (ocaml_bytes @-> (returning bool))))
  end