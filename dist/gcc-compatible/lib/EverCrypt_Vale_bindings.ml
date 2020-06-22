open Ctypes
module Bindings(F:Cstubs.FOREIGN) =
  struct
    open F
    type gcm_args = [ `gcm_args ] structure
    let (gcm_args : [ `gcm_args ] structure typ) = structure "gcm_args_s"
    let gcm_args_plain = field gcm_args "plain" (ptr uint8_t)
    let gcm_args_plain_len = field gcm_args "plain_len" uint64_t
    let gcm_args_aad = field gcm_args "aad" (ptr uint8_t)
    let gcm_args_aad_len = field gcm_args "aad_len" uint64_t
    let gcm_args_iv = field gcm_args "iv" (ptr uint8_t)
    let gcm_args_expanded_key = field gcm_args "expanded_key" (ptr uint8_t)
    let gcm_args_cipher = field gcm_args "cipher" (ptr uint8_t)
    let gcm_args_tag = field gcm_args "tag" (ptr uint8_t)
    let _ = seal gcm_args
  end