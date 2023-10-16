module Hacl.Impl.PCurves.Bignum

open FStar.Mul
open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer

module S = Spec.PCurves
module LSeq = Lib.Sequence
module BSeq = Lib.ByteSequence
module BD = Hacl.Spec.Bignum.Definitions

module BM = Hacl.Bignum.Montgomery
module SM = Hacl.Spec.Bignum.Montgomery

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

module BN = Hacl.Bignum

inline_for_extraction
let felem {| cp:S.curve_params |} = lbuffer uint64 cp.bn_limbs

inline_for_extraction
let widefelem {| cp:S.curve_params |} = lbuffer uint64 (2ul *. cp.bn_limbs)

unfold
let as_nat {| c:S.curve_params |} (h:mem) (e:felem) : GTot nat =
  BD.bn_v (as_seq h e)

unfold
let wide_as_nat {| S.curve_params |} (h:mem) (e:widefelem) : GTot nat =
  BD.bn_v (as_seq h e)

noextract
val bn_v_is_as_nat4: a:LSeq.lseq uint64 4 ->
  Lemma (let (s0, s1, s2, s3) = LSeq.(a.[0], a.[1], a.[2], a.[3]) in
    BD.bn_v a == v s0 + v s1 * pow2 64 + v s2 * pow2 128 + v s3 * pow2 192)

noextract
val bn_v_is_as_nat6: a:Lib.Sequence.lseq uint64 6 ->
  Lemma (let (s0, s1, s2, s3, s4, s5) =
  Lib.Sequence.(a.[0], a.[1], a.[2], a.[3], a.[4], a.[5]) in
    BD.bn_v a == v s0 + v s1 * pow2 64 + v s2 * pow2 128 +
                 v s3 * pow2 192 + v s4 * pow2 256 + v s5 * pow2 320)


///  Create a bignum

[@(strict_on_arguments [0])]
inline_for_extraction noextract
val create_felem: {| c:S.curve_params |} -> StackInline felem
  (requires fun h -> True)
  (ensures  fun h0 f h1 ->
    stack_allocated f h0 h1 (LSeq.create (v c.bn_limbs) (u64 0)) /\
    as_nat h1 f == 0)

[@(strict_on_arguments [0])]
inline_for_extraction noextract
val create_widefelem: {| c:S.curve_params |} -> StackInline widefelem
  (requires fun h -> True)
  (ensures  fun h0 f h1 ->
    stack_allocated f h0 h1 (LSeq.create (2 * v c.bn_limbs) (u64 0)) /\
    wide_as_nat h1 f == 0)


[@(strict_on_arguments [0])]
inline_for_extraction noextract
val bn_make_u64_4: {| c:S.curve_params |} -> res:felem -> a0:uint64 -> a1:uint64 -> a2:uint64 -> a3:uint64{c.bn_limbs == 4ul} -> Stack unit
  (requires fun h -> live h res)
  (ensures  fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    as_nat h1 res = v a0 + v a1 * pow2 64 + v a2 * pow2 128 + v a3 * pow2 192)

[@(strict_on_arguments [0])]
inline_for_extraction noextract
val bn_make_u64_6: {| c:S.curve_params |} -> res:felem -> a0:uint64 -> a1:uint64 -> a2:uint64 -> a3:uint64 -> a4:uint64 -> a5:uint64{c.bn_limbs == 6ul} -> Stack unit
  (requires fun h -> live h res)
  (ensures  fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    as_nat h1 res = v a0 + v a1 * pow2 64 + v a2 * pow2 128 + v a3 * pow2 192 + v a4 * pow2 256 + v a5 * pow2 320)



///  Create zero and one

[@(strict_on_arguments [0])]
inline_for_extraction noextract
val bn_set_zero: {| c:S.curve_params |} -> f:felem -> Stack unit
  (requires fun h -> live h f)
  (ensures fun h0 _ h1 -> modifies (loc f) h0 h1 /\
    as_nat h1 f == 0)


[@(strict_on_arguments [0])]
inline_for_extraction noextract
val bn_set_one: {| c:S.curve_params |} -> f:felem -> Stack unit
  (requires fun h -> live h f)
  (ensures fun h0 _ h1 -> modifies (loc f) h0 h1 /\
    as_nat h1 f == 1)


///  Comparison


inline_for_extraction noextract
let bn_is_eq_mask_t {| c:S.curve_params |} = x:felem -> y:felem -> Stack uint64
  (requires fun h -> live h x /\ live h y)
  (ensures fun h0 r h1 -> modifies0 h0 h1 /\
    (if as_nat h0 x = as_nat h0 y then v r == ones_v U64 else v r = 0))

[@(strict_on_arguments [0])]
inline_for_extraction noextract
val bn_is_eq_mask_g: {| c:S.curve_params |} -> bn_is_eq_mask_t



///  Conditional copy

inline_for_extraction noextract
let bn_cmovznz_t {| c:S.curve_params |} = res:felem -> cin:uint64 -> x:felem -> y:felem -> Stack unit
  (requires fun h ->
    live h x /\ live h y /\ live h res /\
    eq_or_disjoint res x /\ eq_or_disjoint res y /\ eq_or_disjoint x y)
  (ensures fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    (if v cin = 0 then as_nat h1 res == as_nat h0 x else as_nat h1 res == as_nat h0 y))

[@(strict_on_arguments [0])]
inline_for_extraction noextract
val bn_cmovznz_g: {| c:S.curve_params |} -> bn_cmovznz_t


///  Addition and subtraction

inline_for_extraction noextract
let bn_add_mod_t {| c:S.curve_params |} = res:felem -> n:felem -> x:felem -> y:felem -> Stack unit
  (requires fun h ->
    live h n /\ live h x /\ live h y /\ live h res /\
    disjoint n x /\ disjoint n y /\ disjoint n res /\
    eq_or_disjoint x y /\ eq_or_disjoint x res /\ eq_or_disjoint y res /\
    as_nat h x < as_nat h n /\ as_nat h y < as_nat h n)
  (ensures fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    as_nat h1 res == (as_nat h0 x + as_nat h0 y) % as_nat h0 n)

[@(strict_on_arguments [0])]
inline_for_extraction noextract
val bn_add_mod_g: {| c:S.curve_params |} -> bn_add_mod_t

inline_for_extraction noextract
let bn_sub_t {| cp:S.curve_params |} = res:felem -> x:felem -> y:felem -> Stack uint64
  (requires fun h ->
    live h x /\ live h y /\ live h res /\
    eq_or_disjoint x y /\ eq_or_disjoint x res /\ eq_or_disjoint y res)
  (ensures fun h0 c h1 -> modifies (loc res) h0 h1 /\ v c <= 1 /\
    as_nat h1 res - v c * pow2 (64 * v cp.bn_limbs) == as_nat h0 x - as_nat h0 y /\
    (if v c = 0 then as_nat h0 x >= as_nat h0 y else as_nat h0 x < as_nat h0 y))

[@(strict_on_arguments [0])]
inline_for_extraction noextract
val bn_sub_g: {| cp:S.curve_params |} -> bn_sub_t

inline_for_extraction noextract
let bn_sub_mod_t {| c:S.curve_params |} = res:felem -> n:felem -> x:felem -> y:felem -> Stack unit
  (requires fun h ->
    live h n /\ live h x /\ live h y /\ live h res /\
    disjoint n x /\ disjoint n y /\ disjoint n res /\
    eq_or_disjoint x y /\ eq_or_disjoint x res /\ eq_or_disjoint y res /\
    as_nat h x < as_nat h n /\ as_nat h y < as_nat h n)
  (ensures fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    as_nat h1 res == (as_nat h0 x - as_nat h0 y) % as_nat h0 n)

[@(strict_on_arguments [0])]
inline_for_extraction noextract
val bn_sub_mod_g: {| c:S.curve_params |} -> bn_sub_mod_t

///  Multiplication


inline_for_extraction noextract
let bn_mul_t {| c:S.curve_params |} = res:widefelem -> x:felem -> y:felem -> Stack unit
  (requires fun h ->
    live h res /\ live h x /\ live h y /\
    eq_or_disjoint x y /\ disjoint x res /\ disjoint y res)
  (ensures  fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    wide_as_nat h1 res = as_nat h0 x * as_nat h0 y)

[@(strict_on_arguments [0])]
inline_for_extraction noextract
val bn_mul_g: {| c:S.curve_params |} -> bn_mul_t

inline_for_extraction noextract
let bn_sqr_t {| c:S.curve_params |} = res:widefelem -> x:felem -> Stack unit
  (requires fun h ->
    live h res /\ live h x /\ eq_or_disjoint x res)
  (ensures  fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    wide_as_nat h1 res = as_nat h0 x * as_nat h0 x)

[@(strict_on_arguments [0])]
inline_for_extraction noextract
val bn_sqr_g: {| c:S.curve_params |} -> bn_sqr_t

///  Conversion between bignum and bytes representation

inline_for_extraction noextract
let bn_to_bytes_be_t {| c:S.curve_params |} = res:lbuffer uint8 (size c.bytes) -> f:felem -> Stack unit
  (requires fun h ->
    live h f /\ live h res /\ disjoint f res /\
    as_nat h f < pow2 (8 * c.bytes))
  (ensures fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    as_seq h1 res == BSeq.nat_to_bytes_be c.bytes (as_nat h0 f))

[@(strict_on_arguments [0])]
inline_for_extraction noextract
val bn_to_bytes_be_g: {| c:S.curve_params |} -> bn_to_bytes_be_t

inline_for_extraction noextract
let bn_from_bytes_be_t {| c:S.curve_params |} = res:felem -> b:lbuffer uint8 (size c.bytes) -> Stack unit
  (requires fun h -> live h b /\ live h res /\ disjoint b res)
  (ensures  fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    as_nat h1 res == BSeq.nat_from_bytes_be (as_seq h0 b))

[@(strict_on_arguments [0])]
inline_for_extraction noextract
val bn_from_bytes_be_g: {| c:S.curve_params |} -> bn_from_bytes_be_t

inline_for_extraction noextract
let bn_mont_reduction_t {| cp:S.curve_params |} =
  mont_mu:uint64 -> res:felem -> x:widefelem -> n:felem -> Stack unit
  (requires fun h ->
    live h x /\ live h n /\ live h res /\
    disjoint x res /\ disjoint n res /\ disjoint x n /\
    wide_as_nat h x < as_nat h n * as_nat h n)
  (ensures fun h0 _ h1 -> modifies (loc res |+| loc x) h0 h1 /\
    as_seq h1 res == 
    SM.bn_mont_reduction (as_seq h0 n) mont_mu (as_seq h0 x))

[@(strict_on_arguments [0])]
inline_for_extraction noextract
val bn_mont_reduction_g {| cp:S.curve_params |} : bn_mont_reduction_t

inline_for_extraction noextract
let unsafe_bool_of_limb (m:uint64) : b:bool{b <==> v m = v (ones U64 SEC)} =
  let open Lib.RawIntTypes in
  FStar.UInt64.(u64_to_UInt64 m =^ u64_to_UInt64 (ones U64 SEC))

[@(strict_on_arguments [0])]
inline_for_extraction noextract
class bn_ops {| S.curve_params |} = {
  bn_is_eq_mask: bn_is_eq_mask_t;
  bn_cmovznz: bn_cmovznz_t;
  bn_add_mod: bn_add_mod_t;
  bn_sub: bn_sub_t;
  bn_sub_mod: bn_sub_mod_t;
  bn_mul: bn_mul_t;
  bn_sqr: bn_sqr_t;
  bn_to_bytes_be: bn_to_bytes_be_t;
  bn_from_bytes_be: bn_from_bytes_be_t;
  bn_mont_reduction: bn_mont_reduction_t
}

[@(strict_on_arguments [0;1])]
inline_for_extraction noextract
val bn_is_zero_mask {| c:S.curve_params |} {| bn_ops |}:
  f:felem -> Stack uint64
  (requires fun h -> live h f)
  (ensures fun h0 r h1 -> modifies0 h0 h1 /\
    (if as_nat h0 f = 0 then v r == ones_v U64 else v r == 0))


[@(strict_on_arguments [0;1])]
inline_for_extraction noextract
val bn_is_zero_vartime {| c:S.curve_params |} {| bn_ops |}:
  f:felem -> Stack bool
  (requires fun h -> live h f)
  (ensures fun h0 r h1 -> modifies0 h0 h1 /\ r == (as_nat h0 f = 0))

[@(strict_on_arguments [0;1])]
inline_for_extraction noextract
val bn_is_eq_vartime {| c:S.curve_params |} {| bn_ops |}:
  x:felem -> y:felem -> Stack bool
  (requires fun h -> live h x /\ live h y)
  (ensures  fun h0 r h1 -> modifies0 h0 h1 /\
    r == (as_nat h0 x = as_nat h0 y))


[@(strict_on_arguments [0;1])]
inline_for_extraction noextract
val bn_is_odd {| c:S.curve_params |} {| bn_ops |}:
  f:felem -> Stack uint64
  (requires fun h -> live h f)
  (ensures  fun h0 r h1 -> modifies0 h0 h1 /\
    v r = (as_nat h0 f % 2))

[@(strict_on_arguments [0;1])]
inline_for_extraction noextract
val bn2_to_bytes_be {| c:S.curve_params |} {| bn_ops |}:
  res:lbuffer uint8 (2ul *. size c.bytes) -> x:felem -> y:felem -> Stack unit
  (requires fun h ->
    live h x /\ live h y /\ live h res /\
    disjoint x res /\ disjoint y res /\
    as_nat h x < pow2 (8*c.bytes) /\
    as_nat h y < pow2 (8*c.bytes))
  (ensures fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    as_seq h1 res == LSeq.concat #uint8 #c.bytes #c.bytes
      (BSeq.nat_to_bytes_be c.bytes (as_nat h0 x)) (BSeq.nat_to_bytes_be c.bytes (as_nat h0 y)))
