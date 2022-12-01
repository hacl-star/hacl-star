module Hacl.Impl.Poly1305.Bignum128

open FStar.HyperStack
open FStar.HyperStack.All
open FStar.Mul

open Lib.IntTypes
open Lib.Buffer

module ST = FStar.HyperStack.ST
module LSeq = Lib.Sequence
module BSeq = Lib.ByteSequence

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

inline_for_extraction noextract
val uints64_from_bytes_le: b:lbuffer uint8 16ul ->
  Stack (uint64 & uint64)
  (requires fun h -> live h b)
  (ensures  fun h0 (lo, hi) h1 -> h0 == h1 /\
    v hi * pow2 64 + v lo == BSeq.nat_from_bytes_le (as_seq h0 b))


inline_for_extraction noextract
val uints64_to_bytes_le:
    b:lbuffer uint8 16ul
  -> lo:uint64
  -> hi:uint64 ->
  Stack unit
  (requires fun h -> live h b)
  (ensures  fun h0 _ h1 ->
    modifies (loc b) h0 h1 /\
    as_seq h1 b == BSeq.nat_to_bytes_le 16 (v hi * pow2 64 + v lo))


inline_for_extraction noextract
val mod_add128:
    a:(uint64 & uint64)
  -> b:(uint64 & uint64) ->
  Pure (uint64 & uint64)
  (requires True)
  (ensures (fun (r0, r1) ->
    let (a0, a1) = a in let (b0, b1) = b in
    v r1 * pow2 64 + v r0 == ((v a1 + v b1) * pow2 64 + v a0 + v b0) % pow2 128))
