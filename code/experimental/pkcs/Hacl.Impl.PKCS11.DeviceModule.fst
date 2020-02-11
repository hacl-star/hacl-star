module Hacl.Impl.PKCS11.DeviceModule

open Lib.IntTypes
open Lib.Buffer

open Hacl.Impl.PKCS11.KeyType

noeq
type device = 
  |Device: 
    keyBufferLen: size_t -> 
    keys: Hacl.Impl.PKCS11.KeyType.key ->
    device
