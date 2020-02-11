module Hacl.Impl.Creation.GenKey

open Hacl.Impl.PKCS11.Internal.Types
open Hacl.Impl.PKCS11.DeviceModule

val _CKS_GenerateKey: 
  d: device -> 
  hSession: nat ->
  pMechanism: _CK_MECHANISM_TYPE -> 
  pTemplate: nat -> 
  Tot 
    ((handler: nat) & (device))
