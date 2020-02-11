module Hacl.Impl.PKCS11.Internal.Types

open Lib.IntTypes


type _CK_ULONG = uint32

type _CK_ATTRIBUTE_TYPE = _CK_ULONG
type _CK_OBJECT_CLASS = _CK_ULONG
type _CK_MECHANISM_TYPE = _CK_ULONG
type _CK_SESSION_HANDLE = _CK_ULONG

(*/* a BYTE-sized Boolean flag */ typedef CK_BYTE CK_BBOOL; *)
type _CK_BOOL = (a: uint8 {uint_v a == 0 \/ uint_v a == pow2 8 - 1})

type void = 
  |CK_ULONG |CK_BOOL

unfold
let void_t = function
  |CK_ULONG -> _CK_ULONG
  |CK_BOOL -> _CK_BOOL
