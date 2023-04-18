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
    type state_s_tags = Unsigned.UInt8.t
    let state_s_tags = typedef uint8_t "state_s_tags"
    let state_s_tags_MD5_s = Unsigned.UInt8.of_int 0
    let state_s_tags_SHA1_s = Unsigned.UInt8.of_int 1
    let state_s_tags_SHA2_224_s = Unsigned.UInt8.of_int 2
    let state_s_tags_SHA2_256_s = Unsigned.UInt8.of_int 3
    let state_s_tags_SHA2_384_s = Unsigned.UInt8.of_int 4
    let state_s_tags_SHA2_512_s = Unsigned.UInt8.of_int 5
    let state_s_tags_SHA3_224_s = Unsigned.UInt8.of_int 6
    let state_s_tags_SHA3_256_s = Unsigned.UInt8.of_int 7
    let state_s_tags_SHA3_384_s = Unsigned.UInt8.of_int 8
    let state_s_tags_SHA3_512_s = Unsigned.UInt8.of_int 9
    let state_s_tags_Blake2S_s = Unsigned.UInt8.of_int 10
    let state_s_tags_Blake2S_128_s = Unsigned.UInt8.of_int 11
    let state_s_tags_Blake2B_s = Unsigned.UInt8.of_int 12
    let state_s_tags_Blake2B_256_s = Unsigned.UInt8.of_int 13
    type everCrypt_Hash_state_s = [ `everCrypt_Hash_state_s ] structure
    let (everCrypt_Hash_state_s : [ `everCrypt_Hash_state_s ] structure typ)
      = structure "EverCrypt_Hash_state_s_s"
    let everCrypt_Hash_update_multi_256 =
      foreign "EverCrypt_Hash_update_multi_256"
        ((ptr uint32_t) @-> (ocaml_bytes @-> (uint32_t @-> (returning void))))
    let everCrypt_Hash_update_last_256 =
      foreign "EverCrypt_Hash_update_last_256"
        ((ptr uint32_t) @->
           (uint64_t @-> (ocaml_bytes @-> (uint32_t @-> (returning void)))))
    let everCrypt_Hash_Incremental_hash_len =
      foreign "EverCrypt_Hash_Incremental_hash_len"
        (spec_Hash_Definitions_hash_alg @-> (returning uint32_t))
    type everCrypt_Hash_Incremental_hash_state =
      [ `everCrypt_Hash_Incremental_hash_state ] structure
    let (everCrypt_Hash_Incremental_hash_state :
      [ `everCrypt_Hash_Incremental_hash_state ] structure typ) =
      structure "EverCrypt_Hash_Incremental_hash_state_s"
    let everCrypt_Hash_Incremental_hash_state_block_state =
      field everCrypt_Hash_Incremental_hash_state "block_state"
        (ptr everCrypt_Hash_state_s)
    let everCrypt_Hash_Incremental_hash_state_buf =
      field everCrypt_Hash_Incremental_hash_state "buf" (ptr uint8_t)
    let everCrypt_Hash_Incremental_hash_state_total_len =
      field everCrypt_Hash_Incremental_hash_state "total_len" uint64_t
    let _ = seal everCrypt_Hash_Incremental_hash_state
    let everCrypt_Hash_Incremental_create_in =
      foreign "EverCrypt_Hash_Incremental_create_in"
        (spec_Hash_Definitions_hash_alg @->
           (returning (ptr everCrypt_Hash_Incremental_hash_state)))
    let everCrypt_Hash_Incremental_init =
      foreign "EverCrypt_Hash_Incremental_init"
        ((ptr everCrypt_Hash_Incremental_hash_state) @-> (returning void))
    let everCrypt_Hash_Incremental_update =
      foreign "EverCrypt_Hash_Incremental_update"
        ((ptr everCrypt_Hash_Incremental_hash_state) @->
           (ocaml_bytes @->
              (uint32_t @-> (returning everCrypt_Error_error_code))))
    let everCrypt_Hash_Incremental_alg_of_state =
      foreign "EverCrypt_Hash_Incremental_alg_of_state"
        ((ptr everCrypt_Hash_Incremental_hash_state) @->
           (returning spec_Hash_Definitions_hash_alg))
    let everCrypt_Hash_Incremental_finish =
      foreign "EverCrypt_Hash_Incremental_finish"
        ((ptr everCrypt_Hash_Incremental_hash_state) @->
           (ocaml_bytes @-> (returning void)))
    let everCrypt_Hash_Incremental_free =
      foreign "EverCrypt_Hash_Incremental_free"
        ((ptr everCrypt_Hash_Incremental_hash_state) @-> (returning void))
    let everCrypt_Hash_Incremental_hash_256 =
      foreign "EverCrypt_Hash_Incremental_hash_256"
        (ocaml_bytes @-> (uint32_t @-> (ocaml_bytes @-> (returning void))))
    let everCrypt_Hash_Incremental_hash =
      foreign "EverCrypt_Hash_Incremental_hash"
        (spec_Hash_Definitions_hash_alg @->
           (ocaml_bytes @-> (ocaml_bytes @-> (uint32_t @-> (returning void)))))
  end