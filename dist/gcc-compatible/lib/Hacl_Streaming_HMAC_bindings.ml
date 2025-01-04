open Ctypes
module Bindings(F:Cstubs.FOREIGN) =
  struct
    open F
    module Hacl_Streaming_Types_applied =
      (Hacl_Streaming_Types_bindings.Bindings)(Hacl_Streaming_Types_stubs)
    open Hacl_Streaming_Types_applied
    type hacl_Agile_Hash_impl = Unsigned.UInt8.t
    let hacl_Agile_Hash_impl = typedef uint8_t "Hacl_Agile_Hash_impl"
    let hacl_Agile_Hash_impl_Hacl_Agile_Hash_MD5 = Unsigned.UInt8.of_int 0
    let hacl_Agile_Hash_impl_Hacl_Agile_Hash_SHA1 = Unsigned.UInt8.of_int 1
    let hacl_Agile_Hash_impl_Hacl_Agile_Hash_SHA2_224 =
      Unsigned.UInt8.of_int 2
    let hacl_Agile_Hash_impl_Hacl_Agile_Hash_SHA2_256 =
      Unsigned.UInt8.of_int 3
    let hacl_Agile_Hash_impl_Hacl_Agile_Hash_SHA2_384 =
      Unsigned.UInt8.of_int 4
    let hacl_Agile_Hash_impl_Hacl_Agile_Hash_SHA2_512 =
      Unsigned.UInt8.of_int 5
    let hacl_Agile_Hash_impl_Hacl_Agile_Hash_SHA3_224 =
      Unsigned.UInt8.of_int 6
    let hacl_Agile_Hash_impl_Hacl_Agile_Hash_SHA3_256 =
      Unsigned.UInt8.of_int 7
    let hacl_Agile_Hash_impl_Hacl_Agile_Hash_SHA3_384 =
      Unsigned.UInt8.of_int 8
    let hacl_Agile_Hash_impl_Hacl_Agile_Hash_SHA3_512 =
      Unsigned.UInt8.of_int 9
    let hacl_Agile_Hash_impl_Hacl_Agile_Hash_Blake2S_32 =
      Unsigned.UInt8.of_int 10
    let hacl_Agile_Hash_impl_Hacl_Agile_Hash_Blake2S_128 =
      Unsigned.UInt8.of_int 11
    let hacl_Agile_Hash_impl_Hacl_Agile_Hash_Blake2B_32 =
      Unsigned.UInt8.of_int 12
    let hacl_Agile_Hash_impl_Hacl_Agile_Hash_Blake2B_256 =
      Unsigned.UInt8.of_int 13
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
    type hacl_Agile_Hash_state_s = [ `hacl_Agile_Hash_state_s ] structure
    let (hacl_Agile_Hash_state_s :
      [ `hacl_Agile_Hash_state_s ] structure typ) =
      structure "Hacl_Agile_Hash_state_s_s"
    type hacl_Streaming_HMAC_Definitions_index =
      [ `hacl_Streaming_HMAC_Definitions_index ] structure
    let (hacl_Streaming_HMAC_Definitions_index :
      [ `hacl_Streaming_HMAC_Definitions_index ] structure typ) =
      structure "Hacl_Streaming_HMAC_Definitions_index_s"
    let hacl_Streaming_HMAC_Definitions_index_fst =
      field hacl_Streaming_HMAC_Definitions_index "fst" hacl_Agile_Hash_impl
    let hacl_Streaming_HMAC_Definitions_index_snd =
      field hacl_Streaming_HMAC_Definitions_index "snd" uint32_t
    let _ = seal hacl_Streaming_HMAC_Definitions_index
    type hacl_Streaming_HMAC_Definitions_two_state =
      [ `hacl_Streaming_HMAC_Definitions_two_state ] structure
    let (hacl_Streaming_HMAC_Definitions_two_state :
      [ `hacl_Streaming_HMAC_Definitions_two_state ] structure typ) =
      structure "Hacl_Streaming_HMAC_Definitions_two_state_s"
    let hacl_Streaming_HMAC_Definitions_two_state_fst =
      field hacl_Streaming_HMAC_Definitions_two_state "fst" uint32_t
    let hacl_Streaming_HMAC_Definitions_two_state_snd =
      field hacl_Streaming_HMAC_Definitions_two_state "snd"
        (ptr hacl_Agile_Hash_state_s)
    let hacl_Streaming_HMAC_Definitions_two_state_thd =
      field hacl_Streaming_HMAC_Definitions_two_state "thd"
        (ptr hacl_Agile_Hash_state_s)
    let _ = seal hacl_Streaming_HMAC_Definitions_two_state
    let hacl_Streaming_HMAC_s1 =
      foreign "Hacl_Streaming_HMAC_s1"
        (hacl_Streaming_HMAC_Definitions_index @->
           (hacl_Streaming_HMAC_Definitions_two_state @->
              (returning (ptr hacl_Agile_Hash_state_s))))
    let hacl_Streaming_HMAC_s2 =
      foreign "Hacl_Streaming_HMAC_s2"
        (hacl_Streaming_HMAC_Definitions_index @->
           (hacl_Streaming_HMAC_Definitions_two_state @->
              (returning (ptr hacl_Agile_Hash_state_s))))
    let hacl_Streaming_HMAC_index_of_state =
      foreign "Hacl_Streaming_HMAC_index_of_state"
        (hacl_Streaming_HMAC_Definitions_two_state @->
           (returning hacl_Streaming_HMAC_Definitions_index))
    type hacl_Streaming_HMAC_agile_state =
      [ `hacl_Streaming_HMAC_agile_state ] structure
    let (hacl_Streaming_HMAC_agile_state :
      [ `hacl_Streaming_HMAC_agile_state ] structure typ) =
      structure "Hacl_Streaming_HMAC_agile_state_s"
    let hacl_Streaming_HMAC_agile_state_block_state =
      field hacl_Streaming_HMAC_agile_state "block_state"
        hacl_Streaming_HMAC_Definitions_two_state
    let hacl_Streaming_HMAC_agile_state_buf =
      field hacl_Streaming_HMAC_agile_state "buf" (ptr uint8_t)
    let hacl_Streaming_HMAC_agile_state_total_len =
      field hacl_Streaming_HMAC_agile_state "total_len" uint64_t
    let _ = seal hacl_Streaming_HMAC_agile_state
    let hacl_Streaming_HMAC_malloc_ =
      foreign "Hacl_Streaming_HMAC_malloc_"
        (hacl_Agile_Hash_impl @->
           (ocaml_bytes @->
              (uint32_t @->
                 ((ptr (ptr hacl_Streaming_HMAC_agile_state)) @->
                    (returning hacl_Streaming_Types_error_code)))))
    let hacl_Streaming_HMAC_get_impl =
      foreign "Hacl_Streaming_HMAC_get_impl"
        ((ptr hacl_Streaming_HMAC_agile_state) @->
           (returning hacl_Streaming_HMAC_Definitions_index))
    let hacl_Streaming_HMAC_reset =
      foreign "Hacl_Streaming_HMAC_reset"
        ((ptr hacl_Streaming_HMAC_agile_state) @->
           (ocaml_bytes @->
              (uint32_t @-> (returning hacl_Streaming_Types_error_code))))
    let hacl_Streaming_HMAC_update =
      foreign "Hacl_Streaming_HMAC_update"
        ((ptr hacl_Streaming_HMAC_agile_state) @->
           (ocaml_bytes @->
              (uint32_t @-> (returning hacl_Streaming_Types_error_code))))
    let hacl_Streaming_HMAC_digest =
      foreign "Hacl_Streaming_HMAC_digest"
        ((ptr hacl_Streaming_HMAC_agile_state) @->
           (ocaml_bytes @-> (uint32_t @-> (returning void))))
    let hacl_Streaming_HMAC_free =
      foreign "Hacl_Streaming_HMAC_free"
        ((ptr hacl_Streaming_HMAC_agile_state) @-> (returning void))
    let hacl_Streaming_HMAC_copy =
      foreign "Hacl_Streaming_HMAC_copy"
        ((ptr hacl_Streaming_HMAC_agile_state) @->
           (returning (ptr hacl_Streaming_HMAC_agile_state)))
  end