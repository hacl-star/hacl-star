module Spec.Cipher16

module S = FStar.Seq
module U32 = FStar.UInt32
module U8 = FStar.UInt8

type alg =
| AES128
| AES256
| CHACHA20

let keylen = function
| AES128 -> 16
| AES256 | CHACHA20 -> 32

let slen = function
| AES128 -> 432
| AES256 -> 496
| CHACHA20 -> 32

type bytes = s:S.seq U8.t
type lbytes (n:nat) = b:bytes{S.length b = n}
type key a = lbytes (keylen a)

val expand: a:alg -> k:key a -> Ghost (lbytes (slen a))
  (requires True)
  (ensures fun b ->
    (match a with
    | CHACHA20 -> b == k
    | _ -> True))

val block: a:alg -> k:key a -> p:lbytes 16 -> GTot (lbytes 16)

