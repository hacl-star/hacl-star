module Lib

open FStar.HyperStack.All
open FStar.Buffer
open FStar.Int.Cast
open FStar.All
open FStar.Mul

module U32 = FStar.UInt32
module U64 = FStar.UInt64

type uint8_p = buffer FStar.UInt8.t
type lbytes (len:U32.t) = b:uint8_p{length b = U32.v len}
type blen = (l:U32.t{U32.v l > 0 /\ U32.v l <= 65536})

type bignum = buffer FStar.UInt64.t
type lbignum (len:U32.t) = b:bignum{length b = U32.v len}
type bnlen = (l:U32.t{U32.v l > 0 /\ U32.v l <= 8192})