module Hacl.Impl.P256.Bignum

open FStar.Mul
open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer

module LSeq = Lib.Sequence
module BSeq = Lib.ByteSequence
module BD = Hacl.Spec.Bignum.Definitions

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

let limb_t = BD.limb_t
let limb l = BD.limb l

[@@strict_on_arguments [0]]
unfold
let limb_zero l : BD.limb l =
  match l with
  | U64 -> u64 0
  | U32 -> u32 0

[@@strict_on_arguments [0]]
unfold
let limb_one l : BD.limb l =
  match l with
  | U64 -> u64 1
  | U32 -> u32 1

[@@strict_on_arguments [0]]
unfold
let nlimbs (l:limb_t) =
  match l with
  | U64 -> 4ul
  | U32 -> 8ul

inline_for_extraction
let felem (l:limb_t) = lbuffer (limb l) (nlimbs l)
inline_for_extraction
let widefelem (l:limb_t) = lbuffer (limb l) (2ul *. nlimbs l)

unfold
let as_nat #l (h:mem) (e:felem l) : GTot nat =
  BD.bn_v (as_seq h e)

unfold
let wide_as_nat #l (h:mem) (e:widefelem l) : GTot nat =
  BD.bn_v (as_seq h e)

///  Create a bignum

inline_for_extraction noextract
val felem_make_u64_4: #l:limb_t -> res:felem l -> a0:uint64 -> a1:uint64 -> a2:uint64 -> a3:uint64 -> Stack unit
  (requires fun h -> live h res)
  (ensures  fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    as_nat h1 res = v a0 + v a1 * pow2 64 + v a2 * pow2 128 + v a3 * pow2 192)

inline_for_extraction noextract
val create_felem: l:limb_t -> StackInline (felem l)
  (requires fun h -> True)
  (ensures  fun h0 f h1 ->
    stack_allocated f h0 h1 (LSeq.create (v (nlimbs l)) (uint #l 0)) /\
    as_nat h1 f == 0)


inline_for_extraction noextract
val create_widefelem: l:limb_t -> StackInline (widefelem l)
  (requires fun h -> True)
  (ensures  fun h0 f h1 ->
    stack_allocated f h0 h1 (LSeq.create (v (2ul *. nlimbs l)) (uint #l 0)) /\
    wide_as_nat h1 f == 0)


///  Create zero and one

inline_for_extraction noextract
val felem_set_zero: #l:limb_t -> f:felem l -> Stack unit
  (requires fun h -> live h f)
  (ensures fun h0 _ h1 -> modifies (loc f) h0 h1 /\
    as_nat h1 f == 0)


inline_for_extraction noextract
val felem_set_one: #l:limb_t -> f:felem l -> Stack unit
  (requires fun h -> live h f)
  (ensures fun h0 _ h1 -> modifies (loc f) h0 h1 /\
    as_nat h1 f == 1)


///  Comparison

val felem_is_zero_mask: #l:limb_t -> f:felem l -> Stack (limb l)
  (requires fun h -> live h f)
  (ensures fun h0 r h1 -> modifies0 h0 h1 /\
    (if as_nat h0 f = 0 then v r == ones_v l else v r == 0))


val felem_is_zero_vartime: #l:limb_t -> f:felem l -> Stack bool
  (requires fun h -> live h f)
  (ensures fun h0 r h1 -> modifies0 h0 h1 /\ r == (as_nat h0 f = 0))


val felem_is_eq_mask: #l:limb_t -> x:felem l -> y:felem l -> Stack (limb l)
  (requires fun h -> live h x /\ live h y)
  (ensures fun h0 r h1 -> modifies0 h0 h1 /\
    (if as_nat h0 x = as_nat h0 y then v r == ones_v U64 else v r = 0))


val felem_is_eq_vartime: #l:limb_t -> x:felem l -> y:felem l -> Stack bool
  (requires fun h -> live h x /\ live h y)
  (ensures  fun h0 r h1 -> modifies0 h0 h1 /\
    r == (as_nat h0 x = as_nat h0 y))


inline_for_extraction noextract
val felem_is_odd: #l:limb_t -> f:felem l -> Stack (limb l)
  (requires fun h -> live h f)
  (ensures  fun h0 r h1 -> modifies0 h0 h1 /\
    v r = (as_nat h0 f % 2))


///  Conditional copy

val felem_cmovznz: #l:limb_t -> res:felem l -> cin:limb l -> x:felem l -> y:felem l -> Stack unit
  (requires fun h ->
    live h x /\ live h y /\ live h res /\
    eq_or_disjoint res x /\ eq_or_disjoint res y /\ eq_or_disjoint x y)
  (ensures fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    (if v cin = 0 then as_nat h1 res == as_nat h0 x else as_nat h1 res == as_nat h0 y))


///  Addition and subtraction

val felem_add_mod: #l:limb_t -> res:felem l -> n:felem l -> x:felem l -> y:felem l -> Stack unit
  (requires fun h ->
    live h n /\ live h x /\ live h y /\ live h res /\
    disjoint n x /\ disjoint n y /\ disjoint n res /\
    eq_or_disjoint x y /\ eq_or_disjoint x res /\ eq_or_disjoint y res /\
    as_nat h x < as_nat h n /\ as_nat h y < as_nat h n)
  (ensures fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    as_nat h1 res == (as_nat h0 x + as_nat h0 y) % as_nat h0 n)


val felem_sub: #l:limb_t -> res:felem l -> x:felem l -> y:felem l -> Stack (limb l)
  (requires fun h ->
    live h x /\ live h y /\ live h res /\
    eq_or_disjoint x y /\ eq_or_disjoint x res /\ eq_or_disjoint y res)
  (ensures fun h0 c h1 -> modifies (loc res) h0 h1 /\ v c <= 1 /\
    as_nat h1 res - v c * pow2 256 == as_nat h0 x - as_nat h0 y /\
    (if v c = 0 then as_nat h0 x >= as_nat h0 y else as_nat h0 x < as_nat h0 y))


val felem_sub_mod: #l:limb_t -> res:felem l -> n:felem l -> x:felem l -> y:felem l -> Stack unit
  (requires fun h ->
    live h n /\ live h x /\ live h y /\ live h res /\
    disjoint n x /\ disjoint n y /\ disjoint n res /\
    eq_or_disjoint x y /\ eq_or_disjoint x res /\ eq_or_disjoint y res /\
    as_nat h x < as_nat h n /\ as_nat h y < as_nat h n)
  (ensures fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    as_nat h1 res == (as_nat h0 x - as_nat h0 y) % as_nat h0 n)


///  Multiplication

val felem_mul: #l:limb_t -> res:widefelem l -> x:felem l -> y:felem l -> Stack unit
  (requires fun h ->
    live h res /\ live h x /\ live h y /\
    eq_or_disjoint x y /\ disjoint x res /\ disjoint y res)
  (ensures  fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    wide_as_nat h1 res = as_nat h0 x * as_nat h0 y)


val felem_sqr: #l:limb_t -> res:widefelem l -> x:felem l -> Stack unit
  (requires fun h ->
    live h res /\ live h x /\ eq_or_disjoint x res)
  (ensures  fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    wide_as_nat h1 res = as_nat h0 x * as_nat h0 x)


///  Conversion between bignum and bytes representation

val felem_to_bytes_be: #l:limb_t -> res:lbuffer uint8 32ul -> f:felem l -> Stack unit
  (requires fun h ->
    live h f /\ live h res /\ disjoint f res /\
    as_nat h f < pow2 256)
  (ensures fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    as_seq h1 res == BSeq.nat_to_bytes_be 32 (as_nat h0 f))


val felem_from_bytes_be: #l:limb_t -> res:felem l -> b:lbuffer uint8 32ul -> Stack unit
  (requires fun h -> live h b /\ live h res /\ disjoint b res)
  (ensures  fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    as_nat h1 res == BSeq.nat_from_bytes_be (as_seq h0 b))


val felem2_to_bytes_be: #l:limb_t -> res:lbuffer uint8 64ul -> x:felem l -> y:felem l -> Stack unit
  (requires fun h ->
    live h x /\ live h y /\ live h res /\
    disjoint x res /\ disjoint y res /\
    as_nat h x < pow2 256 /\ as_nat h y < pow2 256)
  (ensures fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    as_seq h1 res == LSeq.concat #uint8 #32 #32
      (BSeq.nat_to_bytes_be 32 (as_nat h0 x)) (BSeq.nat_to_bytes_be 32 (as_nat h0 y)))

