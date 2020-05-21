open Ctypes
module Bindings(F:Cstubs.FOREIGN) =
  struct
    open F
    let everCrypt_StaticConfig_hacl =
      foreign_value "EverCrypt_StaticConfig_hacl" bool
    let everCrypt_StaticConfig_vale =
      foreign_value "EverCrypt_StaticConfig_vale" bool
    let everCrypt_StaticConfig_openssl =
      foreign_value "EverCrypt_StaticConfig_openssl" bool
    let everCrypt_StaticConfig_bcrypt =
      foreign_value "EverCrypt_StaticConfig_bcrypt" bool
  end