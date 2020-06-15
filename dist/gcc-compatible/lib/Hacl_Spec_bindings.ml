open Ctypes
module Bindings(F:Cstubs.FOREIGN) =
  struct
    open F
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
    type spec_Cipher_Expansion_impl = Unsigned.UInt8.t
    let spec_Cipher_Expansion_impl =
      typedef uint8_t "Spec_Cipher_Expansion_impl" 
    let spec_Cipher_Expansion_impl_Spec_Cipher_Expansion_Hacl_CHACHA20 =
      Unsigned.UInt8.of_int 0 
    let spec_Cipher_Expansion_impl_Spec_Cipher_Expansion_Vale_AES128 =
      Unsigned.UInt8.of_int 1 
    let spec_Cipher_Expansion_impl_Spec_Cipher_Expansion_Vale_AES256 =
      Unsigned.UInt8.of_int 2 
    type spec_Agile_Cipher_cipher_alg = Unsigned.UInt8.t
    let spec_Agile_Cipher_cipher_alg =
      typedef uint8_t "Spec_Agile_Cipher_cipher_alg" 
    let spec_Agile_Cipher_cipher_alg_Spec_Agile_Cipher_AES128 =
      Unsigned.UInt8.of_int 0 
    let spec_Agile_Cipher_cipher_alg_Spec_Agile_Cipher_AES256 =
      Unsigned.UInt8.of_int 1 
    let spec_Agile_Cipher_cipher_alg_Spec_Agile_Cipher_CHACHA20 =
      Unsigned.UInt8.of_int 2 
    type spec_Agile_AEAD_alg = Unsigned.UInt8.t
    let spec_Agile_AEAD_alg = typedef uint8_t "Spec_Agile_AEAD_alg" 
    let spec_Agile_AEAD_alg_Spec_Agile_AEAD_AES128_GCM =
      Unsigned.UInt8.of_int 0 
    let spec_Agile_AEAD_alg_Spec_Agile_AEAD_AES256_GCM =
      Unsigned.UInt8.of_int 1 
    let spec_Agile_AEAD_alg_Spec_Agile_AEAD_CHACHA20_POLY1305 =
      Unsigned.UInt8.of_int 2 
    let spec_Agile_AEAD_alg_Spec_Agile_AEAD_AES128_CCM =
      Unsigned.UInt8.of_int 3 
    let spec_Agile_AEAD_alg_Spec_Agile_AEAD_AES256_CCM =
      Unsigned.UInt8.of_int 4 
    let spec_Agile_AEAD_alg_Spec_Agile_AEAD_AES128_CCM8 =
      Unsigned.UInt8.of_int 5 
    let spec_Agile_AEAD_alg_Spec_Agile_AEAD_AES256_CCM8 =
      Unsigned.UInt8.of_int 6 
  end