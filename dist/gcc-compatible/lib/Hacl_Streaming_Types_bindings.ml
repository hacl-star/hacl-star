open Ctypes
module Bindings(F:Cstubs.FOREIGN) =
  struct
    open F
    type hacl_Streaming_MD_state_32 =
      [ `hacl_Streaming_MD_state_32 ] structure
    let (hacl_Streaming_MD_state_32 :
      [ `hacl_Streaming_MD_state_32 ] structure typ) =
      structure "Hacl_Streaming_MD_state_32_s"
    let hacl_Streaming_MD_state_32_block_state =
      field hacl_Streaming_MD_state_32 "block_state" (ptr uint32_t)
    let hacl_Streaming_MD_state_32_buf =
      field hacl_Streaming_MD_state_32 "buf" (ptr uint8_t)
    let hacl_Streaming_MD_state_32_total_len =
      field hacl_Streaming_MD_state_32 "total_len" uint64_t
    let _ = seal hacl_Streaming_MD_state_32
    type hacl_Streaming_MD_state_64 =
      [ `hacl_Streaming_MD_state_64 ] structure
    let (hacl_Streaming_MD_state_64 :
      [ `hacl_Streaming_MD_state_64 ] structure typ) =
      structure "Hacl_Streaming_MD_state_64_s"
    let hacl_Streaming_MD_state_64_block_state =
      field hacl_Streaming_MD_state_64 "block_state" (ptr uint64_t)
    let hacl_Streaming_MD_state_64_buf =
      field hacl_Streaming_MD_state_64 "buf" (ptr uint8_t)
    let hacl_Streaming_MD_state_64_total_len =
      field hacl_Streaming_MD_state_64 "total_len" uint64_t
    let _ = seal hacl_Streaming_MD_state_64
    type k____uint64_t___uint64_t_ = [ `k____uint64_t___uint64_t_ ] structure
    let (k____uint64_t___uint64_t_ :
      [ `k____uint64_t___uint64_t_ ] structure typ) =
      structure "K____uint64_t___uint64_t__s"
    let k____uint64_t___uint64_t__fst =
      field k____uint64_t___uint64_t_ "fst" (ptr uint64_t)
    let k____uint64_t___uint64_t__snd =
      field k____uint64_t___uint64_t_ "snd" (ptr uint64_t)
    let _ = seal k____uint64_t___uint64_t_
    type hacl_Streaming_Blake2_Types_block_state_blake2b_32 =
      [ `hacl_Streaming_Blake2_Types_block_state_blake2b_32 ] structure
    let (hacl_Streaming_Blake2_Types_block_state_blake2b_32 :
      [ `hacl_Streaming_Blake2_Types_block_state_blake2b_32 ] structure typ)
      = structure "Hacl_Streaming_Blake2_Types_block_state_blake2b_32_s"
    let hacl_Streaming_Blake2_Types_block_state_blake2b_32_fst =
      field hacl_Streaming_Blake2_Types_block_state_blake2b_32 "fst" uint8_t
    let hacl_Streaming_Blake2_Types_block_state_blake2b_32_snd =
      field hacl_Streaming_Blake2_Types_block_state_blake2b_32 "snd" uint8_t
    let hacl_Streaming_Blake2_Types_block_state_blake2b_32_thd =
      field hacl_Streaming_Blake2_Types_block_state_blake2b_32 "thd" bool
    let hacl_Streaming_Blake2_Types_block_state_blake2b_32_f3 =
      field hacl_Streaming_Blake2_Types_block_state_blake2b_32 "f3"
        k____uint64_t___uint64_t_
    let _ = seal hacl_Streaming_Blake2_Types_block_state_blake2b_32
    type hacl_Streaming_Blake2_Types_optional_block_state_blake2b_32_tags =
      Unsigned.UInt8.t
    let hacl_Streaming_Blake2_Types_optional_block_state_blake2b_32_tags =
      typedef uint8_t
        "Hacl_Streaming_Blake2_Types_optional_block_state_blake2b_32_tags"
    let hacl_Streaming_Blake2_Types_optional_block_state_blake2b_32_tags_Hacl_Streaming_Blake2_Types_None
      = Unsigned.UInt8.of_int 0
    let hacl_Streaming_Blake2_Types_optional_block_state_blake2b_32_tags_Hacl_Streaming_Blake2_Types_Some
      = Unsigned.UInt8.of_int 1
    type hacl_Streaming_Blake2_Types_optional_block_state_blake2b_32 =
      [ `hacl_Streaming_Blake2_Types_optional_block_state_blake2b_32 ]
        structure
    let (hacl_Streaming_Blake2_Types_optional_block_state_blake2b_32 :
      [ `hacl_Streaming_Blake2_Types_optional_block_state_blake2b_32 ]
        structure typ)
      =
      structure
        "Hacl_Streaming_Blake2_Types_optional_block_state_blake2b_32_s"
    let hacl_Streaming_Blake2_Types_optional_block_state_blake2b_32_tag =
      field hacl_Streaming_Blake2_Types_optional_block_state_blake2b_32 "tag"
        hacl_Streaming_Blake2_Types_optional_block_state_blake2b_32_tags
    let hacl_Streaming_Blake2_Types_optional_block_state_blake2b_32_v =
      field hacl_Streaming_Blake2_Types_optional_block_state_blake2b_32 "v"
        hacl_Streaming_Blake2_Types_block_state_blake2b_32
    let _ = seal hacl_Streaming_Blake2_Types_optional_block_state_blake2b_32
    type k____uint32_t___uint32_t_ = [ `k____uint32_t___uint32_t_ ] structure
    let (k____uint32_t___uint32_t_ :
      [ `k____uint32_t___uint32_t_ ] structure typ) =
      structure "K____uint32_t___uint32_t__s"
    let k____uint32_t___uint32_t__fst =
      field k____uint32_t___uint32_t_ "fst" (ptr uint32_t)
    let k____uint32_t___uint32_t__snd =
      field k____uint32_t___uint32_t_ "snd" (ptr uint32_t)
    let _ = seal k____uint32_t___uint32_t_
    type hacl_Streaming_Blake2_Types_block_state_blake2s_32 =
      [ `hacl_Streaming_Blake2_Types_block_state_blake2s_32 ] structure
    let (hacl_Streaming_Blake2_Types_block_state_blake2s_32 :
      [ `hacl_Streaming_Blake2_Types_block_state_blake2s_32 ] structure typ)
      = structure "Hacl_Streaming_Blake2_Types_block_state_blake2s_32_s"
    let hacl_Streaming_Blake2_Types_block_state_blake2s_32_fst =
      field hacl_Streaming_Blake2_Types_block_state_blake2s_32 "fst" uint8_t
    let hacl_Streaming_Blake2_Types_block_state_blake2s_32_snd =
      field hacl_Streaming_Blake2_Types_block_state_blake2s_32 "snd" uint8_t
    let hacl_Streaming_Blake2_Types_block_state_blake2s_32_thd =
      field hacl_Streaming_Blake2_Types_block_state_blake2s_32 "thd" bool
    let hacl_Streaming_Blake2_Types_block_state_blake2s_32_f3 =
      field hacl_Streaming_Blake2_Types_block_state_blake2s_32 "f3"
        k____uint32_t___uint32_t_
    let _ = seal hacl_Streaming_Blake2_Types_block_state_blake2s_32
    type hacl_Streaming_Blake2_Types_optional_block_state_blake2s_32 =
      [ `hacl_Streaming_Blake2_Types_optional_block_state_blake2s_32 ]
        structure
    let (hacl_Streaming_Blake2_Types_optional_block_state_blake2s_32 :
      [ `hacl_Streaming_Blake2_Types_optional_block_state_blake2s_32 ]
        structure typ)
      =
      structure
        "Hacl_Streaming_Blake2_Types_optional_block_state_blake2s_32_s"
    let hacl_Streaming_Blake2_Types_optional_block_state_blake2s_32_tag =
      field hacl_Streaming_Blake2_Types_optional_block_state_blake2s_32 "tag"
        hacl_Streaming_Blake2_Types_optional_block_state_blake2b_32_tags
    let hacl_Streaming_Blake2_Types_optional_block_state_blake2s_32_v =
      field hacl_Streaming_Blake2_Types_optional_block_state_blake2s_32 "v"
        hacl_Streaming_Blake2_Types_block_state_blake2s_32
    let _ = seal hacl_Streaming_Blake2_Types_optional_block_state_blake2s_32
    type hacl_Streaming_Types_error_code = Unsigned.UInt8.t
    let hacl_Streaming_Types_error_code =
      typedef uint8_t "Hacl_Streaming_Types_error_code"
    let hacl_Streaming_Types_error_code_Hacl_Streaming_Types_Success =
      Unsigned.UInt8.of_int 0
    let hacl_Streaming_Types_error_code_Hacl_Streaming_Types_InvalidAlgorithm
      = Unsigned.UInt8.of_int 1
    let hacl_Streaming_Types_error_code_Hacl_Streaming_Types_InvalidLength =
      Unsigned.UInt8.of_int 2
    let hacl_Streaming_Types_error_code_Hacl_Streaming_Types_MaximumLengthExceeded
      = Unsigned.UInt8.of_int 3
    let hacl_Streaming_Types_error_code_Hacl_Streaming_Types_OutOfMemory =
      Unsigned.UInt8.of_int 4
    type hacl_Streaming_Types_optional_32_tags = Unsigned.UInt8.t
    let hacl_Streaming_Types_optional_32_tags =
      typedef uint8_t "Hacl_Streaming_Types_optional_32_tags"
    let hacl_Streaming_Types_optional_32_tags_Hacl_Streaming_Types_None =
      Unsigned.UInt8.of_int 0
    let hacl_Streaming_Types_optional_32_tags_Hacl_Streaming_Types_Some =
      Unsigned.UInt8.of_int 1
    type hacl_Streaming_Types_optional_32 =
      [ `hacl_Streaming_Types_optional_32 ] structure
    let (hacl_Streaming_Types_optional_32 :
      [ `hacl_Streaming_Types_optional_32 ] structure typ) =
      structure "Hacl_Streaming_Types_optional_32_s"
    let hacl_Streaming_Types_optional_32_tag =
      field hacl_Streaming_Types_optional_32 "tag"
        hacl_Streaming_Types_optional_32_tags
    let hacl_Streaming_Types_optional_32_v =
      field hacl_Streaming_Types_optional_32 "v" (ptr uint32_t)
    let _ = seal hacl_Streaming_Types_optional_32
    type hacl_Streaming_Types_optional_64 =
      [ `hacl_Streaming_Types_optional_64 ] structure
    let (hacl_Streaming_Types_optional_64 :
      [ `hacl_Streaming_Types_optional_64 ] structure typ) =
      structure "Hacl_Streaming_Types_optional_64_s"
    let hacl_Streaming_Types_optional_64_tag =
      field hacl_Streaming_Types_optional_64 "tag"
        hacl_Streaming_Types_optional_32_tags
    let hacl_Streaming_Types_optional_64_v =
      field hacl_Streaming_Types_optional_64 "v" (ptr uint64_t)
    let _ = seal hacl_Streaming_Types_optional_64
    type hacl_Streaming_Types_optional_unit =
      hacl_Streaming_Types_optional_32_tags
    let hacl_Streaming_Types_optional_unit =
      typedef hacl_Streaming_Types_optional_32_tags
        "Hacl_Streaming_Types_optional_unit"
    type hacl_Streaming_Types_two_pointers = k____uint64_t___uint64_t_
    let hacl_Streaming_Types_two_pointers =
      typedef k____uint64_t___uint64_t_ "Hacl_Streaming_Types_two_pointers"
    type spec_Hash_Definitions_hash_alg = Unsigned.UInt8.t
    let spec_Hash_Definitions_hash_alg =
      typedef uint8_t "Spec_Hash_Definitions_hash_alg"
    let spec_Hash_Definitions_hash_alg_Spec_Hash_Definitions_SHA2_224 =
      Unsigned.UInt8.of_int 0
    let spec_Hash_Definitions_hash_alg_Spec_Hash_Definitions_SHA2_256 =
      Unsigned.UInt8.of_int 1
    let spec_Hash_Definitions_hash_alg_Spec_Hash_Definitions_SHA2_384 =
      Unsigned.UInt8.of_int 2
    let spec_Hash_Definitions_hash_alg_Spec_Hash_Definitions_SHA2_512 =
      Unsigned.UInt8.of_int 3
    let spec_Hash_Definitions_hash_alg_Spec_Hash_Definitions_SHA1 =
      Unsigned.UInt8.of_int 4
    let spec_Hash_Definitions_hash_alg_Spec_Hash_Definitions_MD5 =
      Unsigned.UInt8.of_int 5
    let spec_Hash_Definitions_hash_alg_Spec_Hash_Definitions_Blake2S =
      Unsigned.UInt8.of_int 6
    let spec_Hash_Definitions_hash_alg_Spec_Hash_Definitions_Blake2B =
      Unsigned.UInt8.of_int 7
    let spec_Hash_Definitions_hash_alg_Spec_Hash_Definitions_SHA3_256 =
      Unsigned.UInt8.of_int 8
    let spec_Hash_Definitions_hash_alg_Spec_Hash_Definitions_SHA3_224 =
      Unsigned.UInt8.of_int 9
    let spec_Hash_Definitions_hash_alg_Spec_Hash_Definitions_SHA3_384 =
      Unsigned.UInt8.of_int 10
    let spec_Hash_Definitions_hash_alg_Spec_Hash_Definitions_SHA3_512 =
      Unsigned.UInt8.of_int 11
    let spec_Hash_Definitions_hash_alg_Spec_Hash_Definitions_Shake128 =
      Unsigned.UInt8.of_int 12
    let spec_Hash_Definitions_hash_alg_Spec_Hash_Definitions_Shake256 =
      Unsigned.UInt8.of_int 13
  end