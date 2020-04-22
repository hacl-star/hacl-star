module Hacl.Impl.Curve25519.Fields

open FStar.HyperStack
open FStar.HyperStack.All
open FStar.Mul

open Lib.IntTypes
open Lib.Buffer

include Hacl.Impl.Curve25519.Fields.Core

module ST = FStar.HyperStack.ST
module BSeq = Lib.ByteSequence
module LSeq = Lib.Sequence

module P = Spec.Curve25519
module F51 = Hacl.Impl.Curve25519.Field51
module F64 = Hacl.Impl.Curve25519.Field64


#set-options "--z3rlimit 50 --max_fuel 0 --initial_ifuel 1 --max_ifuel 1 --record_options"

inline_for_extraction noextract
val create_felem:
    s:field_spec
  -> StackInline (felem s)
    (requires fun h -> True)
    (ensures  fun h0 f h1 ->
      stack_allocated f h0 h1 (LSeq.create (v (nlimb s)) (limb_zero s)) /\
      as_nat h1 f == 0)
let create_felem s =
  match s with
  | M51 -> (F51.create_felem ()) <: felem s
  | M64 -> (F64.create_felem ()) <: felem s

inline_for_extraction noextract
val load_felem:
    #s:field_spec
  -> f:felem s
  -> u64s:lbuffer uint64 4ul
  -> Stack unit
    (requires fun h ->
      live h f /\ live h u64s /\ disjoint f u64s /\
      v (LSeq.index (as_seq h u64s) 3) < pow2 63)
    (ensures  fun h0 _ h1 ->
      modifies (loc f) h0 h1 /\ state_inv_t h1 f /\
      as_nat h1 f == BSeq.nat_from_intseq_le (as_seq h0 u64s))
let load_felem #s f b =
  match s with
  | M51 -> F51.load_felem f b
  | M64 -> F64.load_felem f b

val store_felem:
    #s:field_spec
  -> b:lbuffer uint64 4ul
  -> f:felem s
  -> Stack unit
    (requires fun h ->
      live h f /\ live h b /\ disjoint f b /\ state_inv_t h f)
    (ensures  fun h0 _ h1 ->
      modifies (loc b |+| loc f) h0 h1 /\
      as_seq h1 b == BSeq.nat_to_intseq_le 4 (feval h0 f))
[@ Meta.Attribute.specialize ]
let store_felem #s b f =
  match s with
  | M51 -> F51.store_felem b f
  | M64 -> F64.store_felem b f

inline_for_extraction noextract
val set_zero:
    #s:field_spec
  -> f:felem s
  -> Stack unit
    (requires fun h -> live h f)
    (ensures  fun h0 _ h1 ->
      modifies (loc f) h0 h1 /\
      as_nat h1 f == 0)
let set_zero #s f =
  match s with
  | M51 -> F51.set_zero f
  | M64 -> F64.set_zero f

inline_for_extraction noextract
val set_one:
    #s:field_spec
  -> f:felem s
  -> Stack unit
    (requires fun h -> live h f)
    (ensures  fun h0 _ h1 ->
      modifies (loc f) h0 h1 /\
      as_nat h1 f == 1)
let set_one #s f =
  match s with
  | M51 -> F51.set_one f
  | M64 -> F64.set_one f

inline_for_extraction noextract
val copy_felem:
    #s:field_spec
  -> f:felem s
  -> f':felem s
  -> Stack unit
    (requires fun h ->
      live h f /\ live h f' /\ disjoint f f')
    (ensures  fun h0 _ h1 ->
      modifies (loc f) h0 h1 /\
      as_seq h1 f == as_seq h0 f')
let copy_felem #s f f' =
  match s with
  | M51 -> F51.copy_felem f f'
  | M64 -> F64.copy_felem f f'

