module EverCrypt.Vale

module B = LowStar.Buffer

open EverCrypt.Helpers

/// This module directly exposes "raw" functions, using attributes to make sure
/// KreMLin generates the right "extern stdcall" declarations. There is no C code to implement this module, the implementations are provided at link-time.

// Can't use the real ASM names because they are capitalized...
// name forwarding is in evercrypt_vale_stubs.c with stdcall calls
val aes128_key_expansion_sbox: key:uint8_p -> w:uint8_p -> sbox:uint8_p -> Stack_ unit
val aes128_encrypt_one_block: cipher:uint8_p -> plain: uint8_p -> w:uint8_p -> sbox: uint8_p -> Stack_ unit

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

// This old is to avoid naming conflicts in KreMLin, since there is already an aes128_key_expansion
// extracted by KreMLin
[@ (CCConv "stdcall") ]
val old_aes128_key_expansion: key_ptr:uint8_p -> expanded_key_ptr: uint8_p -> Stack_ unit

// This old is because calling conventions changed in Vale, we now take a list of arguments instead
// of a pointer to a struct containing all addresses
[@ (CCConv "stdcall") ]
val old_gcm128_encrypt: B.pointer gcm_args -> Stack_ unit

[@ (CCConv "stdcall") ]
val old_gcm128_decrypt: B.pointer gcm_args -> Stack_ uint32_t

// This old is to avoid naming conflicts in KreMLin, since there is already an aes256_key_expansion
// extracted by KreMLin
[@ (CCConv "stdcall") ]
val old_aes256_key_expansion: key_ptr:uint8_p -> expanded_key_ptr: uint8_p -> Stack_ unit

// This old is because calling conventions changed in Vale, we now take a list of arguments
[@ (CCConv "stdcall") ]
val old_gcm256_encrypt: B.pointer gcm_args -> Stack_ unit

[@ (CCConv "stdcall") ]
val old_gcm256_decrypt: B.pointer gcm_args -> Stack_ uint32_t
