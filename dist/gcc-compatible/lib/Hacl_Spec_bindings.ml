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
    let spec_Hash_Definitions_hash_alg_Spec_Hash_Definitions_Blake2S =
      Unsigned.UInt8.of_int 6
    let spec_Hash_Definitions_hash_alg_Spec_Hash_Definitions_Blake2B =
      Unsigned.UInt8.of_int 7
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
    type spec_Frodo_Params_frodo_gen_a = Unsigned.UInt8.t
    let spec_Frodo_Params_frodo_gen_a =
      typedef uint8_t "Spec_Frodo_Params_frodo_gen_a"
    let spec_Frodo_Params_frodo_gen_a_Spec_Frodo_Params_SHAKE128 =
      Unsigned.UInt8.of_int 0
    let spec_Frodo_Params_frodo_gen_a_Spec_Frodo_Params_AES128 =
      Unsigned.UInt8.of_int 1
    type spec_FFDHE_ffdhe_alg = Unsigned.UInt8.t
    let spec_FFDHE_ffdhe_alg = typedef uint8_t "Spec_FFDHE_ffdhe_alg"
    let spec_FFDHE_ffdhe_alg_Spec_FFDHE_FFDHE2048 = Unsigned.UInt8.of_int 0
    let spec_FFDHE_ffdhe_alg_Spec_FFDHE_FFDHE3072 = Unsigned.UInt8.of_int 1
    let spec_FFDHE_ffdhe_alg_Spec_FFDHE_FFDHE4096 = Unsigned.UInt8.of_int 2
    let spec_FFDHE_ffdhe_alg_Spec_FFDHE_FFDHE6144 = Unsigned.UInt8.of_int 3
    let spec_FFDHE_ffdhe_alg_Spec_FFDHE_FFDHE8192 = Unsigned.UInt8.of_int 4
    type spec_Blake2_alg = Unsigned.UInt8.t
    let spec_Blake2_alg = typedef uint8_t "Spec_Blake2_alg"
    let spec_Blake2_alg_Spec_Blake2_Blake2S = Unsigned.UInt8.of_int 0
    let spec_Blake2_alg_Spec_Blake2_Blake2B = Unsigned.UInt8.of_int 1
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