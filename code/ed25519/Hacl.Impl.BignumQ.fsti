module Hacl.Impl.BignumQ

module ST = FStar.HyperStack.ST
open FStar.HyperStack
open FStar.HyperStack.All
open FStar.Mul

open Lib.IntTypes
open Lib.Buffer

module BSeq = Lib.ByteSequence
module BD = Hacl.Bignum.Definitions

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

val modq: a:lbuffer uint64 8ul -> res:lbuffer uint64 4ul -> Stack unit
  (requires fun h ->
    live h a /\ live h res /\ disjoint a res)
  (ensures  fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    BD.bn_v h1 res == BD.bn_v h0 a % Spec.Ed25519.q)


val mul_add_modq:
    a:lbuffer uint64 4ul
  -> b:lbuffer uint64 4ul
  -> c:lbuffer uint64 4ul
  -> res:lbuffer uint64 4ul ->
  Stack unit
  (requires fun h ->
    live h a /\ live h b /\ live h c /\ live h res /\
    eq_or_disjoint a b /\
    eq_or_disjoint res a /\ eq_or_disjoint res b /\ eq_or_disjoint res c /\
    BD.bn_v h a < Spec.Ed25519.q /\ BD.bn_v h c < Spec.Ed25519.q)
  (ensures  fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    BD.bn_v h1 res ==
    (BD.bn_v h0 c + (BD.bn_v h0 a * BD.bn_v h0 b % Spec.Ed25519.q)) % Spec.Ed25519.q)


val gte_q: s:lbuffer uint64 4ul -> Stack bool
  (requires fun h -> live h s)
  (ensures  fun h0 b h1 -> modifies0 h0 h1 /\
    (b <==> BD.bn_v h0 s >= Spec.Ed25519.q))


val load_32_bytes:
  out:lbuffer uint64 4ul
  -> b:lbuffer uint8 32ul ->
  Stack unit
  (requires fun h -> live h out /\ live h b /\ disjoint out b)
  (ensures  fun h0 _ h1 -> modifies (loc out) h0 h1 /\
    BD.bn_v h1 out == BSeq.nat_from_bytes_le (as_seq h0 b))


val store_32_bytes:
    out:lbuffer uint8 32ul
  -> b:lbuffer uint64 4ul ->
  Stack unit
  (requires fun h ->
    live h out /\ live h b /\ disjoint out b /\
    BD.bn_v h b < Spec.Ed25519.q)
  (ensures  fun h0 _ h1 -> modifies (loc out) h0 h1 /\
    as_seq h1 out == BSeq.nat_to_bytes_le 32 (BD.bn_v h0 b))
