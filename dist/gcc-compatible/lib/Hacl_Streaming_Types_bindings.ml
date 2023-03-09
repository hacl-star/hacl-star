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
  end