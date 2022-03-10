open Ctypes
module Bindings(F:Cstubs.FOREIGN) =
  struct
    open F
    let hacl_K256_ECDSA_ecdsa_sign_hashed_msg =
      foreign "Hacl_K256_ECDSA_ecdsa_sign_hashed_msg"
        (ocaml_bytes @->
           (ocaml_bytes @->
              (ocaml_bytes @->
                 (ocaml_bytes @-> (ocaml_bytes @-> (returning bool))))))
    let hacl_K256_ECDSA_ecdsa_verify_hashed_msg =
      foreign "Hacl_K256_ECDSA_ecdsa_verify_hashed_msg"
        (ocaml_bytes @->
           (ocaml_bytes @->
              (ocaml_bytes @-> (ocaml_bytes @-> (returning bool)))))
    let hacl_K256_ECDSA_ecdsa_sign_sha256 =
      foreign "Hacl_K256_ECDSA_ecdsa_sign_sha256"
        (ocaml_bytes @->
           (ocaml_bytes @->
              (uint32_t @->
                 (ocaml_bytes @->
                    (ocaml_bytes @-> (ocaml_bytes @-> (returning bool)))))))
    let hacl_K256_ECDSA_ecdsa_verify_sha256 =
      foreign "Hacl_K256_ECDSA_ecdsa_verify_sha256"
        (uint32_t @->
           (ocaml_bytes @->
              (ocaml_bytes @->
                 (ocaml_bytes @-> (ocaml_bytes @-> (returning bool))))))
    let hacl_K256_ECDSA_pk_uncompressed_to_raw =
      foreign "Hacl_K256_ECDSA_pk_uncompressed_to_raw"
        (ocaml_bytes @-> (ocaml_bytes @-> (returning bool)))
    let hacl_K256_ECDSA_pk_uncompressed_from_raw =
      foreign "Hacl_K256_ECDSA_pk_uncompressed_from_raw"
        (ocaml_bytes @-> (ocaml_bytes @-> (returning void)))
    let hacl_K256_ECDSA_pk_compressed_to_raw =
      foreign "Hacl_K256_ECDSA_pk_compressed_to_raw"
        (ocaml_bytes @-> (ocaml_bytes @-> (returning bool)))
    let hacl_K256_ECDSA_pk_compressed_from_raw =
      foreign "Hacl_K256_ECDSA_pk_compressed_from_raw"
        (ocaml_bytes @-> (ocaml_bytes @-> (returning void)))
  end