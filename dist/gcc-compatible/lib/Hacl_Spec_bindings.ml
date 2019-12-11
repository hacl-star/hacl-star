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
  end