module Poly1305_32

open FStar.HyperStack.All

module ST = FStar.HyperStack.ST

open FStar.Mul
open FStar.HyperStack.ST
open FStar.Ghost
open FStar.Seq
open FStar.Buffer
open FStar.HyperStack

open Hacl.Cast
open Hacl.MAC.Poly1305_32

module H8   = Hacl.UInt8
module Limb = Hacl.Bignum.Limb
module Wide = Hacl.Bignum.Wide
module U8   = FStar.UInt8
module U32  = FStar.UInt32
module U64  = FStar.UInt64

val crypto_onetimeauth:
  output:uint8_p{length output = 16} ->
  input:uint8_p{disjoint input output} ->
  len:U64.t{U64.v len < pow2 32 /\ U64.v len <= length input} ->
  k:uint8_p{disjoint output k /\ length k = 32} ->
  Stack unit
    (requires (fun h -> live h output /\ live h input /\ live h k))
    (ensures  (fun h0 _ h1 -> live h1 output /\ modifies_1 output h0 h1 /\ live h0 input /\ live h0 k
      (* /\ as_seq h1 output == crypto_onetimeauth_spec (as_seq h0 input) len (as_seq h0 k) *)
    ))
let crypto_onetimeauth output input len k = crypto_onetimeauth output input len k
