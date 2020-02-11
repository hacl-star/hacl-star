module Hacl.Impl.PKCS11.KeyType

open Hacl.Impl.PKCS11.Internal.Object


type key = 
  |Key: element: _object -> key
