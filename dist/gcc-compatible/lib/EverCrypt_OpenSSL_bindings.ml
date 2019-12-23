open Ctypes
module Bindings(F:Cstubs.FOREIGN) =
  struct
    open F
    type everCrypt_OpenSSL_alg = Unsigned.UInt8.t
    let everCrypt_OpenSSL_alg = typedef uint8_t "EverCrypt_OpenSSL_alg" 
    let everCrypt_OpenSSL_alg_EverCrypt_OpenSSL_AES128_GCM =
      Unsigned.UInt8.of_int 0 
    let everCrypt_OpenSSL_alg_EverCrypt_OpenSSL_AES256_GCM =
      Unsigned.UInt8.of_int 1 
    let everCrypt_OpenSSL_alg_EverCrypt_OpenSSL_CHACHA20_POLY1305 =
      Unsigned.UInt8.of_int 2 
    type everCrypt_OpenSSL_ec_curve = Unsigned.UInt8.t
    let everCrypt_OpenSSL_ec_curve =
      typedef uint8_t "EverCrypt_OpenSSL_ec_curve" 
    let everCrypt_OpenSSL_ec_curve_EverCrypt_OpenSSL_ECC_P256 =
      Unsigned.UInt8.of_int 0 
    let everCrypt_OpenSSL_ec_curve_EverCrypt_OpenSSL_ECC_P384 =
      Unsigned.UInt8.of_int 1 
    let everCrypt_OpenSSL_ec_curve_EverCrypt_OpenSSL_ECC_P521 =
      Unsigned.UInt8.of_int 2 
    let everCrypt_OpenSSL_ec_curve_EverCrypt_OpenSSL_ECC_X25519 =
      Unsigned.UInt8.of_int 3 
    let everCrypt_OpenSSL_ec_curve_EverCrypt_OpenSSL_ECC_X448 =
      Unsigned.UInt8.of_int 4 
  end