module Poly1305_64

open FStar.Mul
open FStar.ST
open FStar.Ghost
open FStar.Seq
open FStar.HyperStack
open FStar.Endianness
open FStar.Buffer

type uint8_p = Buffer.buffer Hacl.UInt8.t
module U64  = FStar.UInt64

val crypto_onetimeauth:
  output:uint8_p{length output = 16} ->
  input:uint8_p{disjoint input output} ->
  len:U64.t{U64.v len < pow2 32 /\ U64.v len = length input} ->
  k:uint8_p{disjoint output k /\ length k = 32} ->
  Stack unit
    (requires (fun h -> live h output /\ live h input /\ live h k))
    (ensures  (fun h0 _ h1 -> live h1 output /\ modifies_1 output h0 h1 /\ live h0 input /\ live h0 k
      /\ as_seq h1 output == Hacl.Spe.Poly1305_64.crypto_onetimeauth_spec (as_seq h0 input) len (as_seq h0 k)))
let crypto_onetimeauth output input len k = Hacl.Impl.Poly1305_64.crypto_onetimeauth output input len k
