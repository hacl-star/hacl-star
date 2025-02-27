open Ctypes
module Bindings(F:Cstubs.FOREIGN) =
  struct
    open F
    module Hacl_Streaming_Types_applied =
      (Hacl_Streaming_Types_bindings.Bindings)(Hacl_Streaming_Types_stubs)
    open Hacl_Streaming_Types_applied
    type everCrypt_DRBG_supported_alg = spec_Hash_Definitions_hash_alg
    let everCrypt_DRBG_supported_alg =
      typedef spec_Hash_Definitions_hash_alg "EverCrypt_DRBG_supported_alg"
    let everCrypt_DRBG_reseed_interval =
      foreign_value "EverCrypt_DRBG_reseed_interval" uint32_t
    let everCrypt_DRBG_max_output_length =
      foreign_value "EverCrypt_DRBG_max_output_length" uint32_t
    let everCrypt_DRBG_max_length =
      foreign_value "EverCrypt_DRBG_max_length" uint32_t
    let everCrypt_DRBG_max_personalization_string_length =
      foreign_value "EverCrypt_DRBG_max_personalization_string_length"
        uint32_t
    let everCrypt_DRBG_max_additional_input_length =
      foreign_value "EverCrypt_DRBG_max_additional_input_length" uint32_t
    let everCrypt_DRBG_min_length =
      foreign "EverCrypt_DRBG_min_length"
        (spec_Hash_Definitions_hash_alg @-> (returning uint32_t))
    type state_s_tags = Unsigned.UInt8.t
    let state_s_tags = typedef uint8_t "state_s_tags"
    let state_s_tags_SHA1_s = Unsigned.UInt8.of_int 0
    let state_s_tags_SHA2_256_s = Unsigned.UInt8.of_int 1
    let state_s_tags_SHA2_384_s = Unsigned.UInt8.of_int 2
    let state_s_tags_SHA2_512_s = Unsigned.UInt8.of_int 3
    type everCrypt_DRBG_state_s = [ `everCrypt_DRBG_state_s ] structure
    let (everCrypt_DRBG_state_s : [ `everCrypt_DRBG_state_s ] structure typ)
      = structure "EverCrypt_DRBG_state_s_s"
    let everCrypt_DRBG_create_in =
      foreign "EverCrypt_DRBG_create_in"
        (spec_Hash_Definitions_hash_alg @->
           (returning (ptr everCrypt_DRBG_state_s)))
    let everCrypt_DRBG_create =
      foreign "EverCrypt_DRBG_create"
        (spec_Hash_Definitions_hash_alg @->
           (returning (ptr everCrypt_DRBG_state_s)))
    let everCrypt_DRBG_instantiate =
      foreign "EverCrypt_DRBG_instantiate"
        ((ptr everCrypt_DRBG_state_s) @->
           (ocaml_bytes @-> (uint32_t @-> (returning bool))))
    let everCrypt_DRBG_reseed =
      foreign "EverCrypt_DRBG_reseed"
        ((ptr everCrypt_DRBG_state_s) @->
           (ocaml_bytes @-> (uint32_t @-> (returning bool))))
    let everCrypt_DRBG_generate =
      foreign "EverCrypt_DRBG_generate"
        (ocaml_bytes @->
           ((ptr everCrypt_DRBG_state_s) @->
              (uint32_t @-> (ocaml_bytes @-> (uint32_t @-> (returning bool))))))
    let everCrypt_DRBG_uninstantiate =
      foreign "EverCrypt_DRBG_uninstantiate"
        ((ptr everCrypt_DRBG_state_s) @-> (returning void))
  end