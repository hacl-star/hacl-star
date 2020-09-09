open Ctypes
module Bindings(F:Cstubs.FOREIGN) =
  struct
    open F
    module Hacl_Spec_applied = (Hacl_Spec_bindings.Bindings)(Hacl_Spec_stubs)
    open Hacl_Spec_applied
    let everCrypt_HKDF_expand_sha1 =
      foreign "EverCrypt_HKDF_expand_sha1"
        (ocaml_bytes @->
           (ocaml_bytes @->
              (uint32_t @->
                 (ocaml_bytes @->
                    (uint32_t @-> (uint32_t @-> (returning void)))))))
    let everCrypt_HKDF_extract_sha1 =
      foreign "EverCrypt_HKDF_extract_sha1"
        (ocaml_bytes @->
           (ocaml_bytes @->
              (uint32_t @-> (ocaml_bytes @-> (uint32_t @-> (returning void))))))
    let everCrypt_HKDF_expand_sha2_256 =
      foreign "EverCrypt_HKDF_expand_sha2_256"
        (ocaml_bytes @->
           (ocaml_bytes @->
              (uint32_t @->
                 (ocaml_bytes @->
                    (uint32_t @-> (uint32_t @-> (returning void)))))))
    let everCrypt_HKDF_extract_sha2_256 =
      foreign "EverCrypt_HKDF_extract_sha2_256"
        (ocaml_bytes @->
           (ocaml_bytes @->
              (uint32_t @-> (ocaml_bytes @-> (uint32_t @-> (returning void))))))
    let everCrypt_HKDF_expand_sha2_384 =
      foreign "EverCrypt_HKDF_expand_sha2_384"
        (ocaml_bytes @->
           (ocaml_bytes @->
              (uint32_t @->
                 (ocaml_bytes @->
                    (uint32_t @-> (uint32_t @-> (returning void)))))))
    let everCrypt_HKDF_extract_sha2_384 =
      foreign "EverCrypt_HKDF_extract_sha2_384"
        (ocaml_bytes @->
           (ocaml_bytes @->
              (uint32_t @-> (ocaml_bytes @-> (uint32_t @-> (returning void))))))
    let everCrypt_HKDF_expand_sha2_512 =
      foreign "EverCrypt_HKDF_expand_sha2_512"
        (ocaml_bytes @->
           (ocaml_bytes @->
              (uint32_t @->
                 (ocaml_bytes @->
                    (uint32_t @-> (uint32_t @-> (returning void)))))))
    let everCrypt_HKDF_extract_sha2_512 =
      foreign "EverCrypt_HKDF_extract_sha2_512"
        (ocaml_bytes @->
           (ocaml_bytes @->
              (uint32_t @-> (ocaml_bytes @-> (uint32_t @-> (returning void))))))
    let everCrypt_HKDF_expand_blake2s =
      foreign "EverCrypt_HKDF_expand_blake2s"
        (ocaml_bytes @->
           (ocaml_bytes @->
              (uint32_t @->
                 (ocaml_bytes @->
                    (uint32_t @-> (uint32_t @-> (returning void)))))))
    let everCrypt_HKDF_extract_blake2s =
      foreign "EverCrypt_HKDF_extract_blake2s"
        (ocaml_bytes @->
           (ocaml_bytes @->
              (uint32_t @-> (ocaml_bytes @-> (uint32_t @-> (returning void))))))
    let everCrypt_HKDF_expand_blake2b =
      foreign "EverCrypt_HKDF_expand_blake2b"
        (ocaml_bytes @->
           (ocaml_bytes @->
              (uint32_t @->
                 (ocaml_bytes @->
                    (uint32_t @-> (uint32_t @-> (returning void)))))))
    let everCrypt_HKDF_extract_blake2b =
      foreign "EverCrypt_HKDF_extract_blake2b"
        (ocaml_bytes @->
           (ocaml_bytes @->
              (uint32_t @-> (ocaml_bytes @-> (uint32_t @-> (returning void))))))
    let everCrypt_HKDF_expand =
      foreign "EverCrypt_HKDF_expand"
        (spec_Hash_Definitions_hash_alg @->
           (ocaml_bytes @->
              (ocaml_bytes @->
                 (uint32_t @->
                    (ocaml_bytes @->
                       (uint32_t @-> (uint32_t @-> (returning void))))))))
    let everCrypt_HKDF_extract =
      foreign "EverCrypt_HKDF_extract"
        (spec_Hash_Definitions_hash_alg @->
           (ocaml_bytes @->
              (ocaml_bytes @->
                 (uint32_t @->
                    (ocaml_bytes @-> (uint32_t @-> (returning void)))))))
    let everCrypt_HKDF_hkdf_expand =
      foreign "EverCrypt_HKDF_hkdf_expand"
        (spec_Hash_Definitions_hash_alg @->
           (ocaml_bytes @->
              (ocaml_bytes @->
                 (uint32_t @->
                    (ocaml_bytes @->
                       (uint32_t @-> (uint32_t @-> (returning void))))))))
    let everCrypt_HKDF_hkdf_extract =
      foreign "EverCrypt_HKDF_hkdf_extract"
        (spec_Hash_Definitions_hash_alg @->
           (ocaml_bytes @->
              (ocaml_bytes @->
                 (uint32_t @->
                    (ocaml_bytes @-> (uint32_t @-> (returning void)))))))
  end