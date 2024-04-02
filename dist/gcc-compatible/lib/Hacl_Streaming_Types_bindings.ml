open Ctypes
module Bindings(F:Cstubs.FOREIGN) =
  struct
    open F
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