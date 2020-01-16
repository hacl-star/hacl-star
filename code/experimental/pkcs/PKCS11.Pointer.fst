module PKCS11.Pointer

module ST = FStar.HyperStack.ST
open FStar.HyperStack.All
open FStar.Mul
open FStar.HyperStack
open FStar.Ghost
open FStar.Buffer

type _CK_VOID_PTR = unit

assume val castToBool: raw: _CK_VOID_PTR -> Stack (buffer bool)
    (requires (fun h -> True))
    (ensures (fun h0 _ h1 -> True))   
