open Ctypes
module Bindings(F:Cstubs.FOREIGN) =
  struct
    open F
    module Hacl_Spec_applied = (Hacl_Spec_bindings.Bindings)(Hacl_Spec_stubs)
    open Hacl_Spec_applied
    let everCrypt_HMAC_compute_sha1 =
      foreign "EverCrypt_HMAC_compute_sha1"
        (ocaml_bytes @->
           (ocaml_bytes @->
              (uint32_t @-> (ocaml_bytes @-> (uint32_t @-> (returning void))))))
    let everCrypt_HMAC_compute_sha2_256 =
      foreign "EverCrypt_HMAC_compute_sha2_256"
        (ocaml_bytes @->
           (ocaml_bytes @->
              (uint32_t @-> (ocaml_bytes @-> (uint32_t @-> (returning void))))))
    let everCrypt_HMAC_compute_sha2_384 =
      foreign "EverCrypt_HMAC_compute_sha2_384"
        (ocaml_bytes @->
           (ocaml_bytes @->
              (uint32_t @-> (ocaml_bytes @-> (uint32_t @-> (returning void))))))
    let everCrypt_HMAC_compute_sha2_512 =
      foreign "EverCrypt_HMAC_compute_sha2_512"
        (ocaml_bytes @->
           (ocaml_bytes @->
              (uint32_t @-> (ocaml_bytes @-> (uint32_t @-> (returning void))))))
    let everCrypt_HMAC_compute_blake2s =
      foreign "EverCrypt_HMAC_compute_blake2s"
        (ocaml_bytes @->
           (ocaml_bytes @->
              (uint32_t @-> (ocaml_bytes @-> (uint32_t @-> (returning void))))))
    let everCrypt_HMAC_compute_blake2b =
      foreign "EverCrypt_HMAC_compute_blake2b"
        (ocaml_bytes @->
           (ocaml_bytes @->
              (uint32_t @-> (ocaml_bytes @-> (uint32_t @-> (returning void))))))
    let everCrypt_HMAC_is_supported_alg =
      foreign "EverCrypt_HMAC_is_supported_alg"
        (spec_Hash_Definitions_hash_alg @-> (returning bool))
    type everCrypt_HMAC_supported_alg = spec_Hash_Definitions_hash_alg
    let everCrypt_HMAC_supported_alg =
      typedef spec_Hash_Definitions_hash_alg "EverCrypt_HMAC_supported_alg"
    let everCrypt_HMAC_compute =
      foreign "EverCrypt_HMAC_compute"
        (spec_Hash_Definitions_hash_alg @->
           (ocaml_bytes @->
              (ocaml_bytes @->
                 (uint32_t @->
                    (ocaml_bytes @-> (uint32_t @-> (returning void)))))))
  end