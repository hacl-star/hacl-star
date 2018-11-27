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
val create_wide:
  unit -> StackInline felem_wide
  (requires fun _ -> True)
  (ensures  fun h0 f h1 ->
    stack_allocated f h0 h1 (Seq.create 8 (u64 0)) /\
    wide_as_nat h1 f == 0)
let create_wide () = create 8ul (u64 0)

inline_for_extraction
val set_bit1:
    f:felem
  -> i:size_t{v i < 255}
  -> Stack unit
    (requires fun h -> live h f)
    (ensures  fun h0 _ h1 -> modifies (loc f) h0 h1)
let set_bit1 f i =
  f.(i /. size 64) <- f.(i /. size 64) |. (u64 1 <<. (i %. size 64))

inline_for_extraction
val set_bit0:
    f:felem
  -> i:size_t{v i < 255}
  -> Stack unit
    (requires fun h -> live h f)
    (ensures  fun h0 _ h1 -> modifies (loc f) h0 h1)
let set_bit0 f i =
  f.(i /. size 64) <- f.(i /. size 64) &. lognot (u64 1 <<. (i %. size 64))

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
  f1.(size 0) <- f2.(size 0);
  f1.(size 1) <- f2.(size 1);
  f1.(size 2) <- f2.(size 2);
  f1.(size 3) <- f2.(size 3)

inline_for_extraction
val load_felem:
    f:felem
  -> u64s:lbuffer uint64 4ul
  -> Stack unit
    (requires fun h -> live h u64s /\ live h f)
    (ensures  fun h0 _ h1 -> modifies (loc f) h0 h1)
let load_felem f u64s =
  f.(0ul) <- u64s.(0ul);
  f.(1ul) <- u64s.(1ul);
  f.(2ul) <- u64s.(2ul);
  f.(3ul) <- u64s.(3ul)

val store_felem:
    u64s:lbuffer uint64 4ul
  -> f:felem
  -> Stack unit
    (requires fun h -> live h f /\ live h u64s)
    (ensures  fun h0 _ h1 -> modifies (loc u64s |+| loc f) h0 h1)
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
