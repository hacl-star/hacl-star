module Hacl.Impl.Curve25519.Field64

open FStar.HyperStack
open FStar.HyperStack.All
open FStar.Mul

open Lib.Sequence
open Lib.IntTypes
open Lib.Buffer

include Hacl.Impl.Curve25519.Field64.Core

module ST = FStar.HyperStack.ST
module S = Hacl.Spec.Curve25519.Field64.Definition
module Lemmas = Hacl.Spec.Curve25519.Field64.Lemmas
module LSeq = Lib.Sequence
module BSeq = Lib.ByteSequence
module P = NatPrime

#reset-options "--z3rlimit 20"

let felem = lbuffer uint64 4ul
let felem2 = lbuffer uint64 8ul
let felem_wide = lbuffer uint64 8ul

inline_for_extraction
val create_felem:
  unit -> StackInline felem
  (requires fun _ -> True)
  (ensures  fun h0 f h1 ->
    stack_allocated f h0 h1 (Seq.create 4 (u64 0)) /\
    as_nat h1 f == 0)
let create_felem () = create 4ul (u64 0)

inline_for_extraction
val load_felem:
    f:felem
  -> u64s:lbuffer uint64 4ul
  -> Stack unit
    (requires fun h ->
      live h u64s /\ live h f /\ disjoint u64s f)
    (ensures  fun h0 _ h1 ->
      modifies (loc f) h0 h1 /\
      as_nat h1 f == BSeq.nat_from_intseq_le (as_seq h0 u64s))
let load_felem f u64s =
  let h0 = ST.get () in
  Lemmas.lemma_nat_from_uints64_le_4 (as_seq h0 u64s);
  f.(0ul) <- u64s.(0ul);
  f.(1ul) <- u64s.(1ul);
  f.(2ul) <- u64s.(2ul);
  f.(3ul) <- u64s.(3ul)

inline_for_extraction
val store_felem:
    u64s:lbuffer uint64 4ul
  -> f:felem
  -> Stack unit
    (requires fun h ->
      live h f /\ live h u64s /\ disjoint u64s f)
    (ensures  fun h0 _ h1 ->
      modifies (loc u64s |+| loc f) h0 h1)
     // BSeq.nat_from_intseq_le (as_seq h1 u64s) == (as_nat h0 f) % P.prime)
let store_felem u64s f =
  let f3 = f.(3ul) in
  let top_bit = f3 >>. 63ul in
  f.(3ul) <- f3 &. u64 0x7fffffffffffffff;
  let carry = add1 f f (u64 19 *. top_bit) in

  let f3 = f.(3ul) in
  let top_bit = f3 >>. 63ul in
  f.(3ul) <- f3 &. u64 0x7fffffffffffffff;
  let carry = add1 f f (u64 19 *. top_bit) in

  u64s.(0ul) <- f.(0ul);
  u64s.(1ul) <- f.(1ul);
  u64s.(2ul) <- f.(2ul);
  u64s.(3ul) <- f.(3ul)

inline_for_extraction
val set_zero:
  f:felem -> Stack unit
  (requires fun h -> live h f)
  (ensures  fun h0 _ h1 ->
    modifies (loc f) h0 h1 /\
    as_nat h1 f == 0)
let set_zero f =
  f.(0ul) <- u64 0;
  f.(1ul) <- u64 0;
  f.(2ul) <- u64 0;
  f.(3ul) <- u64 0

inline_for_extraction
val set_one:
  f:felem -> Stack unit
  (requires fun h -> live h f)
  (ensures  fun h0 _ h1 ->
    modifies (loc f) h0 h1 /\
    as_nat h1 f == 1)
let set_one f =
  f.(0ul) <- u64 1;
  f.(1ul) <- u64 0;
  f.(2ul) <- u64 0;
  f.(3ul) <- u64 0

inline_for_extraction
val copy_felem:
    f1:felem
  -> f2:felem
  -> Stack unit
    (requires fun h ->
      live h f1 /\ live h f2 /\ disjoint f1 f2)
    (ensures  fun h0 _ h1 ->
      modifies (loc f1) h0 h1 /\
      as_nat h1 f1 == as_nat h0 f2)
let copy_felem f1 f2 =
  f1.(0ul) <- f2.(0ul);
  f1.(1ul) <- f2.(1ul);
  f1.(2ul) <- f2.(2ul);
  f1.(3ul) <- f2.(3ul)
