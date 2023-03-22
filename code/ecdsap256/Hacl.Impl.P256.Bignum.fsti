module Hacl.Impl.P256.Bignum

open FStar.Mul
open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer

open Hacl.Spec.P256.Bignum

module LSeq = Lib.Sequence
module BSeq = Lib.ByteSequence

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

inline_for_extraction
let felem = lbuffer uint64 (size 4)
inline_for_extraction
let widefelem = lbuffer uint64 (size 8)

unfold
let as_nat (h:mem) (e:felem) : GTot nat = 
  as_nat4 (as_felem4 (as_seq h e))

unfold
let wide_as_nat (h:mem) (e:widefelem) : GTot nat =
  wide_as_nat4 (as_felem8 (as_seq h e))

///  Create a bignum

inline_for_extraction noextract
val create_felem: unit -> StackInline felem
  (requires fun h -> True)
  (ensures  fun h0 f h1 ->
    stack_allocated f h0 h1 (LSeq.create 4 (u64 0)) /\
    as_nat h1 f == 0)


inline_for_extraction noextract
val create_widefelem: unit -> StackInline widefelem
  (requires fun h -> True)
  (ensures  fun h0 f h1 ->
    stack_allocated f h0 h1 (LSeq.create 8 (u64 0)) /\
    wide_as_nat h1 f == 0)


inline_for_extraction noextract
val bn_make_u64_4: a0:uint64 -> a1:uint64 -> a2:uint64 -> a3:uint64
  -> res:lbuffer uint64 4ul -> Stack unit
  (requires fun h -> live h res)
  (ensures  fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    as_nat h1 res = v a0 + v a1 * pow2 64 + v a2 * pow2 128 + v a3 * pow2 192)


///  Create zero and one

inline_for_extraction noextract
val bn_set_zero4: f:felem -> Stack unit
  (requires fun h -> live h f)
  (ensures fun h0 _ h1 -> modifies (loc f) h0 h1 /\
    as_nat h1 f == 0)


inline_for_extraction noextract
val bn_set_one4: f:felem -> Stack unit
  (requires fun h -> live h f)
  (ensures fun h0 _ h1 -> modifies (loc f) h0 h1 /\
    as_nat h1 f == 1)


///  Comparison

val bn_is_zero_vartime4: f:felem -> Stack bool
  (requires fun h -> live h f)
  (ensures fun h0 r h1 -> modifies0 h0 h1 /\ r == (as_nat h0 f = 0))


val bn_is_zero_mask4: f:felem -> Stack uint64
  (requires fun h -> live h f)
  (ensures fun h0 r h1 -> modifies0 h0 h1 /\
    (if as_nat h0 f = 0 then v r == ones_v U64 else v r == 0))


val bn_is_eq_vartime4: a:felem -> b:felem -> Stack bool
  (requires fun h -> live h a /\ live h b)
  (ensures  fun h0 r h1 -> modifies0 h0 h1 /\
    r == (as_nat h0 a = as_nat h0 b))


val bn_is_eq_mask4: a:felem -> b:felem -> Stack uint64
  (requires fun h -> live h a /\ live h b)
  (ensures fun h0 r h1 -> modifies0 h0 h1 /\
    (if as_nat h0 a = as_nat h0 b then v r == ones_v U64 else v r = 0))


inline_for_extraction noextract
val bn_is_odd4: f:felem -> Stack uint64
  (requires fun h -> live h f)
  (ensures  fun h0 r h1 -> modifies0 h0 h1 /\
    v r = (as_nat h0 f % 2))


///  Conditional copy

val bn_copy_conditional4: res:felem -> x:felem
  -> mask:uint64{v mask = 0 \/ v mask = ones_v U64} -> Stack unit
  (requires fun h -> live h res /\ live h x /\ eq_or_disjoint res x)
  (ensures fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    (if v mask = 0 then as_seq h1 res == as_seq h0 res else as_seq h1 res == as_seq h0 x))


val bn_cmovznz4: cin:uint64 -> x:felem -> y:felem -> res:felem -> Stack unit
  (requires fun h ->
    live h x /\ live h y /\ live h res /\
    disjoint x res /\ eq_or_disjoint y res)
  (ensures fun h0 _ h1 -> modifies1 res h0 h1 /\
    (if v cin = 0 then as_nat h1 res == as_nat h0 x else as_nat h1 res == as_nat h0 y))


///  Addition and subtraction

val bn_add_mod4: x:felem -> y:felem -> n:felem -> res:felem -> Stack unit
  (requires fun h ->
    live h n /\ live h x /\ live h y /\ live h res /\
    disjoint n x /\ disjoint n y /\ disjoint n res /\
    eq_or_disjoint x y /\ eq_or_disjoint x res /\ eq_or_disjoint y res /\
    as_nat h x < as_nat h n /\ as_nat h y < as_nat h n)
  (ensures fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    as_nat h1 res == (as_nat h0 x + as_nat h0 y) % as_nat h0 n)


val bn_sub4: x:felem -> y:felem -> res:felem -> Stack uint64
  (requires fun h ->
    live h x /\ live h y /\ live h res /\
    eq_or_disjoint x y /\ eq_or_disjoint x res /\ eq_or_disjoint y res)
  (ensures fun h0 c h1 -> modifies1 res h0 h1 /\ v c <= 1 /\
    as_nat h1 res - v c * pow2 256 == as_nat h0 x - as_nat h0 y /\
    (if v c = 0 then as_nat h0 x >= as_nat h0 y else as_nat h0 x < as_nat h0 y))


val bn_sub_mod4: x:felem -> y:felem -> n:felem -> res:felem -> Stack unit
  (requires fun h ->
    live h n /\ live h x /\ live h y /\ live h res /\
    disjoint n x /\ disjoint n y /\ disjoint n res /\
    eq_or_disjoint x y /\ eq_or_disjoint x res /\ eq_or_disjoint y res /\
    as_nat h x < as_nat h n /\ as_nat h y < as_nat h n)
  (ensures fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    as_nat h1 res == (as_nat h0 x - as_nat h0 y) % as_nat h0 n)


///  Multiplication

val bn_mul4: f:felem -> r:felem -> res:widefelem -> Stack unit
  (requires fun h ->
    live h res /\ live h f /\ live h r /\
    eq_or_disjoint r f /\ disjoint f res /\ disjoint r res)
  (ensures  fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    wide_as_nat h1 res = as_nat h0 r * as_nat h0 f)


val bn_sqr4: f:felem -> res:widefelem -> Stack unit
  (requires fun h ->
    live h res /\ live h f /\ eq_or_disjoint f res)
  (ensures  fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    wide_as_nat h1 res = as_nat h0 f * as_nat h0 f)


///  pow2-operations

val bn_lshift256: f:felem -> res:lbuffer uint64 8ul -> Stack unit
  (requires fun h ->
    live h f /\ live h res /\ disjoint f res)
  (ensures fun h0 _ h1 -> modifies1 res h0 h1 /\
    wide_as_nat h1 res == as_nat h0 f * pow2 256)


///  Conversion between bignum and bytes representation

val bn_to_bytes_be4: f:felem -> res:lbuffer uint8 32ul -> Stack unit
  (requires fun h ->
    live h f /\ live h res /\ disjoint f res /\
    as_nat h f < pow2 256)
  (ensures fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    as_seq h1 res == BSeq.nat_to_bytes_be 32 (as_nat h0 f))


val bn_from_bytes_be4: b:lbuffer uint8 32ul -> res:felem -> Stack unit
  (requires fun h -> live h b /\ live h res /\ disjoint b res)
  (ensures  fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    as_nat h1 res == BSeq.nat_from_bytes_be (as_seq h0 b))
