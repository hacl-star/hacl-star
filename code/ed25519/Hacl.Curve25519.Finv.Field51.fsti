module Hacl.Curve25519.Finv.Field51

open FStar.HyperStack
open FStar.HyperStack.All
open FStar.Mul

open Lib.IntTypes
open Lib.Buffer
open Lib.ByteBuffer

open Hacl.Impl.Curve25519.Fields
open Hacl.Impl.Curve25519.Finv

module ST = FStar.HyperStack.ST

module S = Hacl.Spec.Curve25519.Finv
module P = Spec.Curve25519

#reset-options "--max_fuel 0 --using_facts_from '* -FStar.Seq'"

inline_for_extraction noextract
val fsquare_times_51:
  o:felem M51
  -> i:felem M51
  -> tmp:felem_wide M51
  -> n:size_t{v n > 0}
  -> Stack unit
    (requires fun h0 ->
      live h0 o /\ live h0 i /\ live h0 tmp /\
      (disjoint o i \/ o == i) /\
      disjoint o tmp /\
      disjoint tmp i /\
      fsquare_times_inv h0 i)
    (ensures  fun h0 _ h1 ->
      modifies (loc o |+| loc tmp) h0 h1 /\
      fsquare_times_inv h1 o /\
      feval h1 o == S.pow (feval #M51 h0 i) (pow2 (v n)))


inline_for_extraction noextract
val finv_51:
  o:felem M51
  -> i:felem M51
  -> tmp:felem_wide2 M51
  -> Stack unit
    (requires fun h0 ->
      live h0 o /\ live h0 i /\ live h0 tmp /\
      disjoint o i /\
      disjoint o tmp /\
      disjoint tmp i /\
      fsquare_times_inv h0 i)
    (ensures  fun h0 _ h1 ->
      modifies (loc o |+| loc tmp) h0 h1 /\
      fsquare_times_inv h1 o /\
      feval h1 o == P.fpow (feval #M51 h0 i) (pow2 255 - 21))
