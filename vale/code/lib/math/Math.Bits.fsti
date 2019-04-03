module Math.Bits
open FStar.BV
open FStar.UInt
open FStar.Mul

[@"opaque_to_smt"] let b_i2b (#n:pos) (num:uint_t n) : bv_t n = int2bv num
[@"opaque_to_smt"] let b_b2i (#n:pos) (vec:bv_t n) : uint_t n = bv2int vec
[@"opaque_to_smt"] let b_uext (#n #m:pos) (a:bv_t n) : normalize (bv_t (m + n)) = bv_uext #n #m a
[@"opaque_to_smt"] let b_and (#n:pos) (a:bv_t n) (b:bv_t n) : bv_t n = bvand a b
[@"opaque_to_smt"] let b_or  (#n:pos) (a:bv_t n) (b:bv_t n) : bv_t n = bvor a b
[@"opaque_to_smt"] let b_xor (#n:pos) (a:bv_t n) (b:bv_t n) : bv_t n = bvxor a b
[@"opaque_to_smt"] let b_not (#n:pos) (a:bv_t n) : bv_t n = bvnot a
[@"opaque_to_smt"] let b_shl (#n:pos) (a:bv_t n) (s:nat) : bv_t n = bvshl a s
[@"opaque_to_smt"] let b_shr (#n:pos) (a:bv_t n) (s:nat) : bv_t n = bvshr a s
[@"opaque_to_smt"] let b_add (#n:pos) (a:bv_t n) (b:bv_t n) : bv_t n = bvadd a b
[@"opaque_to_smt"] let b_sub (#n:pos) (a:bv_t n) (b:bv_t n) : bv_t n = bvsub a b
[@"opaque_to_smt"] let b_mul (#n:pos) (a:bv_t n) (b:uint_t n) : bv_t n = bvmul a b
[@"opaque_to_smt"] let b_div (#n:pos) (a:bv_t n) (b:uint_t n{b <> 0}) : bv_t n = bvdiv a b
[@"opaque_to_smt"] let b_mod (#n:pos) (a:bv_t n) (b:uint_t n{b <> 0}) : bv_t n = bvmod a b
// TODO: b_ult, when F*'s SMT encoding fully supports it

private val lemma_pow2_le (m n:nat) : Lemma (requires m <= n) (ensures pow2 m <= pow2 n)
let uext (#n #m:pos) (a:uint_t n) : normalize (uint_t (m + n)) = lemma_pow2_le n (n + m); a

val lemma_i2b_eq (#n:pos) (a b:uint_t n) : Lemma
  (requires b_i2b a == b_i2b b)
  (ensures a == b)

val lemma_i2b_uext (#n m:pos) (a:uint_t n) : Lemma
  (b_i2b (uext #n #m a) == b_uext #n #m (b_i2b #n a))

val lemma_i2b_and (#n:pos) (a b:uint_t n) : Lemma
  (b_i2b #n (logand #n a b) == b_and #n (b_i2b a) (b_i2b b))

val lemma_i2b_or (#n:pos) (a b:uint_t n) : Lemma
  (b_i2b #n (logor #n a b) == b_or #n (b_i2b a) (b_i2b b))

val lemma_i2b_xor (#n:pos) (a b:uint_t n) : Lemma
  (b_i2b #n (logxor #n a b) == b_xor #n (b_i2b a) (b_i2b b))

// TODO, when FStar.BV supports int2bv_lognot:
//val lemma_i2b_not (#n:pos) (a:uint_t n) : Lemma
//  (b_i2b #n (lognot #n a) == b_not #n (b_i2b a))

// TODO (fix FStar.BV): b should be nat, not uint_t n
val lemma_i2b_shl (#n:pos) (a:uint_t n) (b:uint_t n) : Lemma
  (b_i2b #n (shift_left #n a b) == b_shl #n (b_i2b a) b)

// TODO (fix FStar.BV): b should be nat, not uint_t n
val lemma_i2b_shr (#n:pos) (a:uint_t n) (b:uint_t n) : Lemma
  (b_i2b #n (shift_right #n a b) == b_shr #n (b_i2b a) b)

val lemma_i2b_add (#n:pos) (a b:uint_t n) : Lemma
  (b_i2b #n (add_mod #n a b) == b_add #n (b_i2b a) (b_i2b b))

val lemma_i2b_sub (#n:pos) (a b:uint_t n) : Lemma
  (b_i2b #n (sub_mod #n a b) == b_sub #n (b_i2b a) (b_i2b b))

val lemma_i2b_mul (#n:pos) (a b:uint_t n) : Lemma
  (b_i2b #n (mul_mod #n a b) == b_mul #n (b_i2b a) b)

val lemma_i2b_div (#n:pos) (a:uint_t n) (b:uint_t n{b <> 0}) : Lemma
  (b_i2b #n (udiv #n a b) == b_div #n (b_i2b a) b)

val lemma_i2b_mod (#n:pos) (a:uint_t n) (b:uint_t n{b <> 0}) : Lemma
  (b_i2b #n (mod #n a b) == b_mod #n (b_i2b a) b)

val add_hide (#n:pos) (a b:uint_t n) : Pure (uint_t n)
  (requires True)
  (ensures fun x -> a + b < pow2 n ==> x == a + b)

val sub_hide (#n:pos) (a b:uint_t n) : Pure (uint_t n)
  (requires True)
  (ensures fun x -> 0 <= a - b ==> x == a - b)

val mul_hide (#n:pos) (a b:uint_t n) : Pure (uint_t n)
  (requires True)
  (ensures fun x -> 0 <= a * b /\ (a * b < pow2 n ==> x == a * b))

let lemmas_i2b_all =
  (forall (#n:pos) (m:pos) (a:uint_t n) (mn:pos).{:pattern (b_i2b #mn (uext #n #m a))} mn == m + n ==> b_i2b #mn (uext #n #m a) == b_uext #n #m (b_i2b #n a)) /\
  (forall (#n:pos) (a b:uint_t n).{:pattern (b_i2b #n (logand a b))} b_i2b #n (logand #n a b) == b_and #n (b_i2b a) (b_i2b b)) /\
  (forall (#n:pos) (a b:uint_t n).{:pattern (b_i2b #n (logor a b))} b_i2b #n (logor #n a b) == b_or #n (b_i2b a) (b_i2b b)) /\
  (forall (#n:pos) (a b:uint_t n).{:pattern (b_i2b #n (logxor a b))} b_i2b #n (logxor #n a b) == b_xor #n (b_i2b a) (b_i2b b)) /\
  // TODO: shl and shr should take a nat (see comment above)
  (forall (#n:pos) (a b:uint_t n).{:pattern (b_i2b #n (shift_left a b))} b_i2b #n (shift_left #n a b) == b_shl #n (b_i2b a) b) /\
  (forall (#n:pos) (a b:uint_t n).{:pattern (b_i2b #n (shift_right a b))} b_i2b #n (shift_right #n a b) == b_shr #n (b_i2b a) b) /\
  (forall (#n:pos) (a b:uint_t n).{:pattern (b_i2b #n (add_hide a b))} b_i2b #n (add_hide #n a b) == b_add #n (b_i2b a) (b_i2b b)) /\
  (forall (#n:pos) (a b:uint_t n).{:pattern (b_i2b #n (sub_hide a b))} b_i2b #n (sub_hide #n a b) == b_sub #n (b_i2b a) (b_i2b b)) /\
  (forall (#n:pos) (a b:uint_t n).{:pattern (b_i2b #n (mul_hide a b))} b_i2b #n (mul_hide #n a b) == b_mul #n (b_i2b a) b) /\
  (forall (#n:pos) (a b:uint_t n).{:pattern (b_i2b #n (add_mod a b))} b_i2b #n (add_mod #n a b) == b_add #n (b_i2b a) (b_i2b b)) /\
  (forall (#n:pos) (a b:uint_t n).{:pattern (b_i2b #n (sub_mod a b))} b_i2b #n (sub_mod #n a b) == b_sub #n (b_i2b a) (b_i2b b)) /\
  (forall (#n:pos) (a b:uint_t n).{:pattern (b_i2b #n (mul_mod a b))} b_i2b #n (mul_mod #n a b) == b_mul #n (b_i2b a) b) /\
  (forall (#n:pos) (a:uint_t n) (b:uint_t n{b <> 0}).{:pattern (b_i2b #n (udiv a b))} b_i2b #n (udiv #n a b) == b_div #n (b_i2b a) b) /\
  (forall (#n:pos) (a:uint_t n) (b:uint_t n{b <> 0}).{:pattern (b_i2b #n (mod a b))} b_i2b #n (mod #n a b) == b_mod #n (b_i2b a) b) /\
  True

val lemma_i2b_all (_:unit) : Lemma lemmas_i2b_all

val lemma_i2b_with_all (n:pos) (p:Type0) : Lemma
  (requires lemmas_i2b_all ==> p)
  (ensures p)

val lemma_i2b_equal (#n:pos) (x y:uint_t n) : Lemma
  (requires lemmas_i2b_all ==> b_i2b x == b_i2b y)
  (ensures x == y)


unfold let is_bv8 (#n:nat{n >= 8}) (a:bv_t n) = lemma_pow2_le 8 n; a == b_and a (b_i2b 0xff)
unfold let is_bv16 (#n:nat{n >= 16}) (a:bv_t n) = lemma_pow2_le 16 n; a == b_and a (b_i2b 0xffff)
unfold let is_bv32 (#n:nat{n >= 32}) (a:bv_t n) = lemma_pow2_le 32 n; a == b_and a (b_i2b 0xffffffff)
unfold let is_bv64 (#n:nat{n >= 64}) (a:bv_t n) = lemma_pow2_le 64 n; a == b_and a (b_i2b 0xffffffffffffffff)

// REVIEW: equality on bv_t doesn't always work; this is an alternate way to prove equality
unfold let bveq (#n:pos) (a b:bv_t n) = bvxor a b == bvxor a a

val lemma_bveq (#n:pos) (a b:bv_t n) : Lemma
  (requires bveq #n a b)
  (ensures a == b)

val lemma_to_is_bv8 (a:uint_t 32) : Lemma
  (requires a < 0x100)
  (ensures is_bv8 (b_i2b a))

// TODO, when bvult is fully supported:
//val lemma_of_is_bv8 (a:uint_t 32) : Lemma
//  (requires is_bv8 (b_i2b a))
//  (ensures a < 0x100)
