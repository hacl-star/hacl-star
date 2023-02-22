module Hacl.Impl.P256.Bignum

open FStar.Mul
open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer

open Hacl.Spec.P256.Felem

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

// TODO: mv
inline_for_extraction noextract
val scalar_bit:
    #buf_type: buftype ->
    s:lbuffer_t buf_type uint8 (size 32)
  -> n:size_t{v n < 256}
  -> Stack uint64
    (requires fun h0 -> live h0 s)
    (ensures  fun h0 r h1 -> h0 == h1 /\
      r == Spec.ECDSA.ith_bit (as_seq h0 s) (v n) /\ v r <= 1)


// TODO: mv
inline_for_extraction noextract
val mul64: x:uint64 -> y:uint64
  -> res:lbuffer uint64 (size 1) -> tmp:lbuffer uint64 (size 1) -> Stack unit
  (requires fun h -> live h res /\ live h tmp /\ disjoint res tmp)
  (ensures fun h0 _ h1 -> modifies (loc res |+| loc tmp) h0 h1 /\ (
    let h0 = Seq.index (as_seq h1 tmp) 0 in
    let res = Seq.index (as_seq h1 res) 0 in
    uint_v res + uint_v h0 * pow2 64 = uint_v x * uint_v y))

///  Create a bignum

inline_for_extraction noextract
val bn_make_u64_4: a0:uint64 -> a1:uint64 -> a2:uint64 -> a3:uint64
  -> res:lbuffer uint64 (size 4) -> Stack unit
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

val bn_is_zero_mask4: f:felem -> Stack uint64
  (requires fun h -> live h f)
  (ensures fun h0 r h1 -> modifies0 h0 h1 /\
    (if as_nat h0 f = 0 then uint_v r == pow2 64 - 1 else uint_v r == 0))


val bn_is_eq_mask4: a:felem -> b:felem -> Stack uint64
  (requires fun h -> live h a /\ live h b)
  (ensures fun h0 r h1 -> modifies0 h0 h1 /\
    (if as_nat h0 a = as_nat h0 b then uint_v r == pow2 64 - 1 else uint_v r = 0))


///  Conditional copy

// NOTE: changed precondition `eq_or_disjoint res x`
val bn_copy_conditional4: res:felem -> x:felem
  -> mask:uint64{uint_v mask = 0 \/ uint_v mask = pow2 64 - 1} -> Stack unit
  (requires fun h -> live h res /\ live h x /\ eq_or_disjoint res x)
  (ensures fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    (if uint_v mask = 0 then as_seq h1 res == as_seq h0 res else as_seq h1 res == as_seq h0 x))


val bn_cmovznz4: cin:uint64 -> x:felem -> y:felem -> res:felem -> Stack unit
  (requires fun h ->
    live h x /\ live h y /\ live h res /\
    disjoint x res /\ eq_or_disjoint y res)
  (ensures fun h0 _ h1 -> modifies1 res h0 h1 /\
    (if uint_v cin = 0 then as_nat h1 res == as_nat h0 x else as_nat h1 res == as_nat h0 y))


///  Addition and subtraction

// NOTE: changed precondition `eq_or_disjoint x y`
val bn_add4: x:felem -> y:felem -> res:felem -> Stack uint64
  (requires fun h ->
    live h x /\ live h y /\ live h res /\
    eq_or_disjoint x y /\ eq_or_disjoint x res /\ eq_or_disjoint y res)
  (ensures fun h0 c h1 -> modifies (loc res) h0 h1 /\ v c <= 1 /\
    as_nat h1 res + v c * pow2 256 == as_nat h0 x + as_nat h0 y)


// TODO: rm, use add4
val bn_add4_variables: x:felem -> cin:uint64{uint_v cin <= 1}
  -> y0:uint64 -> y1:uint64 -> y2:uint64 -> y3:uint64 -> res:felem ->
  Stack uint64
  (requires fun h -> live h x /\ live h res /\ eq_or_disjoint x res)
  (ensures fun h0 c h1 -> modifies (loc res) h0 h1 /\ v c <= 1 /\
    as_nat h1 res + uint_v c * pow2 256 ==
    as_nat h0 x + uint_v y0 + uint_v y1 * pow2 64 +
    uint_v y2 * pow2 128 + uint_v y3 * pow2 192 + uint_v cin)


// NOTE: changed precondition `eq_or_disjoint x y`
val bn_add8: x:widefelem -> y:widefelem -> res:widefelem -> Stack uint64
  (requires fun h ->
    live h x /\ live h y /\ live h res /\
    eq_or_disjoint x y /\ eq_or_disjoint x res /\ eq_or_disjoint y res)
  (ensures fun h0 c h1 -> modifies (loc res) h0 h1 /\ v c <= 1 /\
    wide_as_nat h1 res + v c * pow2 512 == wide_as_nat h0 x + wide_as_nat h0 y)


// NOTE: changed precondition `eq_or_disjoint x y`
val bn_sub4: x:felem -> y:felem -> res:felem -> Stack uint64
  (requires fun h ->
    live h x /\ live h y /\ live h res /\
    eq_or_disjoint x y /\ eq_or_disjoint x res /\ eq_or_disjoint y res)
  (ensures fun h0 c h1 -> modifies1 res h0 h1 /\ v c <= 1 /\
    as_nat h1 res - v c * pow2 256 == as_nat h0 x - as_nat h0 y)


// TODO: rm; use sub4
val bn_sub4_il: x:felem -> y:glbuffer uint64 (size 4) -> res:felem -> Stack uint64
  (requires fun h ->
    live h x /\ live h y /\ live h res /\
    disjoint x res /\ disjoint res y)
  (ensures fun h0 c h1 -> modifies1 res h0 h1 /\ v c <= 1 /\
    as_nat h1 res - v c * pow2 256 == as_nat h0 x - as_nat_il h0 y /\
    (if uint_v c = 0 then as_nat h0 x >= as_nat_il h0 y else as_nat h0 x < as_nat_il h0 y))


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


// TODO: rm glbuffer and use generic bignum
val bn_mul1: a:glbuffer uint64 (size 4) -> b:uint64 -> res:widefelem -> Stack unit
  (requires fun h ->
    live h a /\ live h res /\ wide_as_nat h res = 0)
  (ensures fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    as_nat_il h0 a * uint_v b = wide_as_nat h1 res /\
    wide_as_nat h1 res < pow2 320)


///  pow2-operations

val bn_lshift256: f:felem -> res:lbuffer uint64 (size 8) -> Stack unit
  (requires fun h ->
    live h f /\ live h res /\ disjoint f res)
  (ensures fun h0 _ h1 -> modifies1 res h0 h1 /\
    wide_as_nat h1 res == as_nat h0 f * pow2 256)


val bn_rshift64: f:widefelem -> res:widefelem -> Stack unit
  (requires fun h ->
    live h f /\ live h res /\ eq_or_disjoint f res)
  (ensures fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    wide_as_nat h1 res == wide_as_nat h0 f / pow2 64)


inline_for_extraction noextract
val bn_mod_pow2_64: a:widefelem -> Stack uint64
  (requires fun h -> live h a)
  (ensures fun h0 r h1 -> modifies0 h0 h1 /\
    uint_v r == wide_as_nat h1 a % pow2 64)


///  Conversion between bignum and bytes representation
// TODO: rm Spec.ECDSA here

val bn_to_bytes_be4: f:felem -> res:lbuffer uint8 (32ul) -> Stack unit
  (requires fun h -> live h f /\ live h res /\ disjoint f res)
  (ensures fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    as_seq h1 res == Lib.ByteSequence.uints_to_bytes_be #_ #_ #4 (as_seq h0 f))


// TODO: rm
inline_for_extraction noextract
val changeEndian: i:felem -> Stack unit
  (requires fun h -> live h i)
  (ensures  fun h0 _ h1 -> modifies1 i h0 h1 /\
    as_seq h1 i == Spec.ECDSA.changeEndian (as_seq h0 i) /\
    as_nat h1 i < pow2 256)


val bn_from_bytes_be4: b:lbuffer uint8 (size 32) -> res:felem -> Stack unit
  (requires fun h -> live h b /\ live h res /\ disjoint b res)
  (ensures  fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    as_seq h1 res == Spec.ECDSA.changeEndian (Lib.ByteSequence.uints_from_bytes_be (as_seq h0 b)))
