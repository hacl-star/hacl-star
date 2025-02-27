open Ctypes
module Bindings(F:Cstubs.FOREIGN) =
  struct
    open F
    module Hacl_Streaming_Types_applied =
      (Hacl_Streaming_Types_bindings.Bindings)(Hacl_Streaming_Types_stubs)
    open Hacl_Streaming_Types_applied
    module EverCrypt_Error_applied =
      (EverCrypt_Error_bindings.Bindings)(EverCrypt_Error_stubs)
    open EverCrypt_Error_applied
    type everCrypt_Hash_state_s_tags = Unsigned.UInt8.t
    let everCrypt_Hash_state_s_tags =
      typedef uint8_t "EverCrypt_Hash_state_s_tags"
    let everCrypt_Hash_state_s_tags_EverCrypt_Hash_MD5_s =
      Unsigned.UInt8.of_int 0
    let everCrypt_Hash_state_s_tags_EverCrypt_Hash_SHA1_s =
      Unsigned.UInt8.of_int 1
    let everCrypt_Hash_state_s_tags_EverCrypt_Hash_SHA2_224_s =
      Unsigned.UInt8.of_int 2
    let everCrypt_Hash_state_s_tags_EverCrypt_Hash_SHA2_256_s =
      Unsigned.UInt8.of_int 3
    let everCrypt_Hash_state_s_tags_EverCrypt_Hash_SHA2_384_s =
      Unsigned.UInt8.of_int 4
    let everCrypt_Hash_state_s_tags_EverCrypt_Hash_SHA2_512_s =
      Unsigned.UInt8.of_int 5
    let everCrypt_Hash_state_s_tags_EverCrypt_Hash_SHA3_224_s =
      Unsigned.UInt8.of_int 6
    let everCrypt_Hash_state_s_tags_EverCrypt_Hash_SHA3_256_s =
      Unsigned.UInt8.of_int 7
    let everCrypt_Hash_state_s_tags_EverCrypt_Hash_SHA3_384_s =
      Unsigned.UInt8.of_int 8
    let everCrypt_Hash_state_s_tags_EverCrypt_Hash_SHA3_512_s =
      Unsigned.UInt8.of_int 9
    let everCrypt_Hash_state_s_tags_EverCrypt_Hash_Blake2S_s =
      Unsigned.UInt8.of_int 10
    let everCrypt_Hash_state_s_tags_EverCrypt_Hash_Blake2S_128_s =
      Unsigned.UInt8.of_int 11
    let everCrypt_Hash_state_s_tags_EverCrypt_Hash_Blake2B_s =
      Unsigned.UInt8.of_int 12
    let everCrypt_Hash_state_s_tags_EverCrypt_Hash_Blake2B_256_s =
      Unsigned.UInt8.of_int 13
    type everCrypt_Hash_state_s = [ `everCrypt_Hash_state_s ] structure
    let (everCrypt_Hash_state_s : [ `everCrypt_Hash_state_s ] structure typ)
      = structure "EverCrypt_Hash_state_s_s"
    let everCrypt_Hash_update_multi_256 =
      foreign "EverCrypt_Hash_update_multi_256"
        ((ptr uint32_t) @-> (ocaml_bytes @-> (uint32_t @-> (returning void))))
    let everCrypt_Hash_Incremental_hash_len =
      foreign "EverCrypt_Hash_Incremental_hash_len"
        (spec_Hash_Definitions_hash_alg @-> (returning uint32_t))
    type everCrypt_Hash_Incremental_state_t =
      [ `everCrypt_Hash_Incremental_state_t ] structure
    let (everCrypt_Hash_Incremental_state_t :
      [ `everCrypt_Hash_Incremental_state_t ] structure typ) =
      structure "EverCrypt_Hash_Incremental_state_t_s"
    let everCrypt_Hash_Incremental_malloc =
      foreign "EverCrypt_Hash_Incremental_malloc"
        (spec_Hash_Definitions_hash_alg @->
           (returning (ptr everCrypt_Hash_Incremental_state_t)))
    let everCrypt_Hash_Incremental_reset =
      foreign "EverCrypt_Hash_Incremental_reset"
        ((ptr everCrypt_Hash_Incremental_state_t) @-> (returning void))
    let everCrypt_Hash_Incremental_update =
      foreign "EverCrypt_Hash_Incremental_update"
        ((ptr everCrypt_Hash_Incremental_state_t) @->
           (ocaml_bytes @->
              (uint32_t @-> (returning everCrypt_Error_error_code))))
    let everCrypt_Hash_Incremental_alg_of_state =
      foreign "EverCrypt_Hash_Incremental_alg_of_state"
        ((ptr everCrypt_Hash_Incremental_state_t) @->
           (returning spec_Hash_Definitions_hash_alg))
    let everCrypt_Hash_Incremental_digest =
      foreign "EverCrypt_Hash_Incremental_digest"
        ((ptr everCrypt_Hash_Incremental_state_t) @->
           (ocaml_bytes @-> (returning void)))
    let everCrypt_Hash_Incremental_free =
      foreign "EverCrypt_Hash_Incremental_free"
        ((ptr everCrypt_Hash_Incremental_state_t) @-> (returning void))
    let everCrypt_Hash_Incremental_hash_256 =
      foreign "EverCrypt_Hash_Incremental_hash_256"
        (ocaml_bytes @-> (ocaml_bytes @-> (uint32_t @-> (returning void))))
    let everCrypt_Hash_Incremental_hash =
      foreign "EverCrypt_Hash_Incremental_hash"
        (spec_Hash_Definitions_hash_alg @->
           (ocaml_bytes @-> (ocaml_bytes @-> (uint32_t @-> (returning void)))))
  end