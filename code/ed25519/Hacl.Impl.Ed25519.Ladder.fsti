module Hacl.Impl.Ed25519.Ladder

module ST = FStar.HyperStack.ST
open FStar.HyperStack.All
open FStar.Mul

open Lib.IntTypes
open Lib.Buffer

open Hacl.Bignum25519

module BSeq = Lib.ByteSequence
module F51 = Hacl.Impl.Ed25519.Field51

module S = Spec.Ed25519

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

val point_mul:
    out:point
  -> scalar:lbuffer uint8 32ul
  -> q:point ->
  Stack unit
  (requires fun h ->
    live h scalar /\ live h q /\ live h out /\
    disjoint q out /\ disjoint q scalar /\
    F51.point_inv_t h q /\ F51.inv_ext_point (as_seq h q))
  (ensures  fun h0 _ h1 -> modifies (loc out) h0 h1 /\
    F51.point_inv_t h1 out /\ F51.inv_ext_point (as_seq h1 out) /\
    S.to_aff_point (F51.point_eval h1 out) ==
    S.to_aff_point (S.point_mul (as_seq h0 scalar) (F51.point_eval h0 q)))


val point_mul_g:
    out:point
  -> scalar:lbuffer uint8 32ul ->
  Stack unit
  (requires fun h ->
    live h scalar /\ live h out /\ disjoint out scalar)
  (ensures  fun h0 _ h1 -> modifies (loc out) h0 h1 /\
    F51.point_inv_t h1 out /\ F51.inv_ext_point (as_seq h1 out) /\
    S.to_aff_point (F51.point_eval h1 out) ==
    S.to_aff_point (S.point_mul_g (as_seq h0 scalar)))


val point_negate_mul_double_g_vartime:
    out:point
  -> scalar1:lbuffer uint8 32ul
  -> scalar2:lbuffer uint8 32ul
  -> q2:point ->
  Stack unit
  (requires fun h ->
    live h out /\ live h scalar1 /\
    live h scalar2 /\ live h q2 /\
    disjoint q2 out /\ disjoint scalar1 out /\ disjoint scalar2 out /\
    F51.point_inv_t h q2 /\ F51.inv_ext_point (as_seq h q2))
  (ensures fun h0 _ h1 -> modifies (loc out) h0 h1 /\
    F51.point_inv_t h1 out /\ F51.inv_ext_point (as_seq h1 out) /\
    S.to_aff_point (F51.point_eval h1 out) ==
    S.to_aff_point (S.point_negate_mul_double_g
      (as_seq h0 scalar1) (as_seq h0 scalar2) (F51.point_eval h0 q2)))
