module EverCrypt.Vale

module N = C.Nullity

open EverCrypt.Helpers

/// This module directly exposes "raw" functions, using attributes to make sure
/// KreMLin generates the right "extern stdcall" declarations. There is no C code to implement this module, the implementations are provided at link-time.

noeq
type gcm_args = {
  plain: uint8_p;
  plain_len: uint64_t;
  aad: uint8_p;
  aad_len: uint64_t;
  iv: uint8_p;
  expanded_key: uint8_p;
  cipher: uint8_p;
  tag: uint8_p;
}

[@ (CCConv "stdcall") ]
val aes_key_expansion: key_ptr:uint8_p -> expanded_key_ptr: uint8_p -> Stack_ unit

[@ (CCConv "stdcall") ]
val gcm_encrypt: N.pointer gcm_args -> Stack_ unit

[@ (CCConv "stdcall") ]
val gcm_decrypt: N.pointer gcm_args -> Stack_ uint32_t
