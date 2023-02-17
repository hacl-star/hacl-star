module Hacl.Impl.P256.LowLevel

open FStar.Mul
open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer
open Lib.ByteBuffer

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
  -> result:lbuffer uint64 (size 1) -> temp:lbuffer uint64 (size 1) -> Stack unit
  (requires fun h -> live h result /\ live h temp /\ disjoint result temp)
  (ensures fun h0 _ h1 -> modifies (loc result |+| loc temp) h0 h1 /\ (
    let h0 = Seq.index (as_seq h1 temp) 0 in
    let result = Seq.index (as_seq h1 result) 0 in
    uint_v result + uint_v h0 * pow2 64 = uint_v x * uint_v y))


///  Create zero and one

inline_for_extraction noextract
val uploadZeroImpl: f:felem -> Stack unit
  (requires fun h -> live h f)
  (ensures fun h0 _ h1 -> modifies (loc f) h0 h1 /\
    as_nat h1 f == 0)


inline_for_extraction noextract
val uploadOneImpl: f:felem -> Stack unit
  (requires fun h -> live h f)
  (ensures fun h0 _ h1 -> modifies (loc f) h0 h1 /\
    as_nat h1 f == 1)


///  Comparison

val isZero_uint64_CT: f:felem -> Stack uint64
  (requires fun h -> live h f)
  (ensures fun h0 r h1 -> modifies0 h0 h1 /\
    (if as_nat h0 f = 0 then uint_v r == pow2 64 - 1 else uint_v r == 0))


val compare_felem: a:felem -> b:felem -> Stack uint64
  (requires fun h -> live h a /\ live h b)
  (ensures fun h0 r h1 -> modifies0 h0 h1 /\
    (if as_nat h0 a = as_nat h0 b then uint_v r == pow2 64 - 1 else uint_v r = 0))


///  Conditional copy

// NOTE: changed precondition `eq_or_disjoint out x`
val copy_conditional: out:felem -> x:felem
  -> mask:uint64{uint_v mask = 0 \/ uint_v mask = pow2 64 - 1} -> Stack unit
  (requires fun h -> live h out /\ live h x /\ eq_or_disjoint out x)
  (ensures fun h0 _ h1 -> modifies (loc out) h0 h1 /\
    (if uint_v mask = 0 then as_seq h1 out == as_seq h0 out else as_seq h1 out == as_seq h0 x))


val cmovznz4: cin:uint64 -> x:felem -> y:felem -> out:felem -> Stack unit
  (requires fun h ->
    live h x /\ live h y /\ live h out /\
    disjoint x out /\ eq_or_disjoint y out)
  (ensures fun h0 _ h1 -> modifies1 out h0 h1 /\
    (if uint_v cin = 0 then as_nat h1 out == as_nat h0 x else as_nat h1 out == as_nat h0 y))


///  Addition and subtraction

// NOTE: changed precondition `eq_or_disjoint x y`
val add4: x:felem -> y:felem -> out:felem -> Stack uint64
  (requires fun h ->
    live h x /\ live h y /\ live h out /\
    eq_or_disjoint x y /\ eq_or_disjoint x out /\ eq_or_disjoint y out)
  (ensures fun h0 c h1 -> modifies (loc out) h0 h1 /\ v c <= 1 /\
    as_nat h1 out + v c * pow2 256 == as_nat h0 x + as_nat h0 y)


// TODO: rm, use add4
val add4_variables: x:felem -> cin:uint64{uint_v cin <= 1}
  -> y0:uint64 -> y1:uint64 -> y2:uint64 -> y3:uint64 -> result:felem ->
  Stack uint64
  (requires fun h -> live h x /\ live h result /\ eq_or_disjoint x result)
  (ensures fun h0 c h1 -> modifies (loc result) h0 h1 /\ v c <= 1 /\
    as_nat h1 result  + uint_v c * pow2 256 ==
    as_nat h0 x + uint_v y0 + uint_v y1 * pow2 64 +
    uint_v y2 * pow2 128 + uint_v y3 * pow2 192 + uint_v cin)


// NOTE: changed precondition `eq_or_disjoint x y`
val add8: x:widefelem -> y:widefelem -> out:widefelem -> Stack uint64
  (requires fun h ->
    live h x /\ live h y /\ live h out /\
    eq_or_disjoint x y /\ eq_or_disjoint x out /\ eq_or_disjoint y out)
  (ensures fun h0 c h1 -> modifies (loc out) h0 h1 /\ v c <= 1 /\
    wide_as_nat h1 out + v c * pow2 512 == wide_as_nat h0 x + wide_as_nat h0 y)


// NOTE: changed precondition `eq_or_disjoint x y`
val sub4: x:felem -> y:felem -> out:felem -> Stack uint64
  (requires fun h ->
    live h x /\ live h y /\ live h out /\
    eq_or_disjoint x y /\ eq_or_disjoint x out /\ eq_or_disjoint y out)
  (ensures fun h0 c h1 -> modifies1 out h0 h1 /\ v c <= 1 /\
    as_nat h1 out - v c * pow2 256 == as_nat h0 x - as_nat h0 y)


// TODO: rm; use sub4
val sub4_il: x:felem -> y:glbuffer uint64 (size 4) -> result:felem -> Stack uint64
  (requires fun h ->
    live h x /\ live h y /\ live h result /\
    disjoint x result /\ disjoint result y)
  (ensures fun h0 c h1 -> modifies1 result h0 h1 /\ v c <= 1 /\
    as_nat h1 result - v c * pow2 256 == as_nat h0 x - as_nat_il h0 y /\
    (if uint_v c = 0 then as_nat h0 x >= as_nat_il h0 y else as_nat h0 x < as_nat_il h0 y))


///  Multiplication

val mul: f:felem -> r:felem -> out:widefelem -> Stack unit
  (requires fun h ->
    live h out /\ live h f /\ live h r /\
    eq_or_disjoint r f /\ disjoint f out /\ disjoint r out)
  (ensures  fun h0 _ h1 -> modifies (loc out) h0 h1 /\
    wide_as_nat h1 out = as_nat h0 r * as_nat h0 f)


val sq: f:felem -> out:widefelem -> Stack unit
  (requires fun h ->
    live h out /\ live h f /\ eq_or_disjoint f out)
  (ensures  fun h0 _ h1 -> modifies (loc out) h0 h1 /\
    wide_as_nat h1 out = as_nat h0 f * as_nat h0 f)


// TODO: rm glbuffer and use generic bignum
val shortened_mul: a:glbuffer uint64 (size 4) -> b:uint64 -> result:widefelem -> Stack unit
  (requires fun h ->
    live h a /\ live h result /\ wide_as_nat h result = 0)
  (ensures fun h0 _ h1 -> modifies (loc result) h0 h1 /\
    as_nat_il h0 a * uint_v b = wide_as_nat h1 result /\
    wide_as_nat h1 result < pow2 320)


///  pow2-operations

val shift_256_impl: i:felem -> o:lbuffer uint64 (size 8) -> Stack unit
  (requires fun h ->
    live h i /\ live h o /\ disjoint i o)
  (ensures fun h0 _ h1 -> modifies1 o h0 h1 /\
    wide_as_nat h1 o == as_nat h0 i * pow2 256)


val shift8: t:widefelem -> out:widefelem -> Stack unit
  (requires fun h ->
    live h t /\ live h out /\ eq_or_disjoint t out)
  (ensures fun h0 _ h1 -> modifies (loc out) h0 h1 /\
    wide_as_nat h0 t / pow2 64 = wide_as_nat h1 out)


inline_for_extraction noextract
val mod64: a:widefelem -> Stack uint64
  (requires fun h -> live h a)
  (ensures fun h0 r h1 -> modifies0 h0 h1 /\
    wide_as_nat h1 a % pow2 64 = uint_v r)


///  Conversion between bignum and bytes representation

val toUint8: i:felem -> o:lbuffer uint8 (32ul) -> Stack unit
  (requires fun h -> live h i /\ live h o /\ disjoint i o)
  (ensures fun h0 _ h1 -> modifies (loc o) h0 h1 /\
    as_seq h1 o == Lib.ByteSequence.uints_to_bytes_be #_ #_ #4 (as_seq h0 i))


inline_for_extraction noextract
val changeEndian: i:felem -> Stack unit
  (requires fun h -> live h i)
  (ensures  fun h0 _ h1 -> modifies1 i h0 h1 /\
    as_seq h1 i == Spec.ECDSA.changeEndian (as_seq h0 i) /\
    as_nat h1 i < pow2 256)


val toUint64ChangeEndian: i:lbuffer uint8 (size 32) -> o:felem -> Stack unit
  (requires fun h -> live h i /\ live h o /\ disjoint i o)
  (ensures  fun h0 _ h1 -> modifies (loc o) h0 h1 /\
    as_seq h1 o == Spec.ECDSA.changeEndian (Lib.ByteSequence.uints_from_bytes_be (as_seq h0 i)))
