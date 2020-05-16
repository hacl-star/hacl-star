open Ctypes
module Bindings(F:Cstubs.FOREIGN) =
  struct
    open F
    type everCrypt_Error_error_code = Unsigned.UInt8.t
    let everCrypt_Error_error_code =
      typedef uint8_t "EverCrypt_Error_error_code"
    let everCrypt_Error_error_code_EverCrypt_Error_Success =
      Unsigned.UInt8.of_int 0
    let everCrypt_Error_error_code_EverCrypt_Error_UnsupportedAlgorithm =
      Unsigned.UInt8.of_int 1
    let everCrypt_Error_error_code_EverCrypt_Error_InvalidKey =
      Unsigned.UInt8.of_int 2
    let everCrypt_Error_error_code_EverCrypt_Error_AuthenticationFailure =
      Unsigned.UInt8.of_int 3
    let everCrypt_Error_error_code_EverCrypt_Error_InvalidIVLength =
      Unsigned.UInt8.of_int 4
    let everCrypt_Error_error_code_EverCrypt_Error_DecodeError =
      Unsigned.UInt8.of_int 5
  end