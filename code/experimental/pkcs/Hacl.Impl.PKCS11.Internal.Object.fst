module Hacl.Impl.PKCS11.Internal.Object

open Lib.IntTypes
open Lib.Buffer
open FStar.Buffer

open Hacl.Impl.PKCS11.Internal.Types
open Hacl.Impl.PKCS11.Internal.Attribute

type _object = 
  |Object: 
    id: _CK_ULONG -> 
    dataLen: size_t -> 
    data: lbuffer uint8 dataLen ->
    attributes_: attribute -> 
    _object
