open Ctypes
module Bindings(F:Cstubs.FOREIGN) =
  struct
    open F
    include (Hacl_Spec_bindings.Bindings)(Hacl_Spec_stubs)
    let everCrypt_HMAC_compute_sha1 =
      foreign "EverCrypt_HMAC_compute_sha1"
        ((ptr uint8_t) @->
           ((ptr uint8_t) @->
              (uint32_t @->
                 ((ptr uint8_t) @-> (uint32_t @-> (returning void))))))
      
    let everCrypt_HMAC_compute_sha2_256 =
      foreign "EverCrypt_HMAC_compute_sha2_256"
        ((ptr uint8_t) @->
           ((ptr uint8_t) @->
              (uint32_t @->
                 ((ptr uint8_t) @-> (uint32_t @-> (returning void))))))
      
    let everCrypt_HMAC_compute_sha2_384 =
      foreign "EverCrypt_HMAC_compute_sha2_384"
        ((ptr uint8_t) @->
           ((ptr uint8_t) @->
              (uint32_t @->
                 ((ptr uint8_t) @-> (uint32_t @-> (returning void))))))
      
    let everCrypt_HMAC_compute_sha2_512 =
      foreign "EverCrypt_HMAC_compute_sha2_512"
        ((ptr uint8_t) @->
           ((ptr uint8_t) @->
              (uint32_t @->
                 ((ptr uint8_t) @-> (uint32_t @-> (returning void))))))
      
    let everCrypt_HMAC_is_supported_alg =
      foreign "EverCrypt_HMAC_is_supported_alg"
        (spec_Hash_Definitions_hash_alg @-> (returning bool))
      
    type everCrypt_HMAC_supported_alg = spec_Hash_Definitions_hash_alg
    let everCrypt_HMAC_supported_alg =
      typedef spec_Hash_Definitions_hash_alg "EverCrypt_HMAC_supported_alg" 
    let everCrypt_HMAC_compute =
      foreign "EverCrypt_HMAC_compute"
        (spec_Hash_Definitions_hash_alg @->
           ((ptr uint8_t) @->
              ((ptr uint8_t) @->
                 (uint32_t @->
                    ((ptr uint8_t) @-> (uint32_t @-> (returning void)))))))
      
  end