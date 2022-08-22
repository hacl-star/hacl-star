module Spec.Exponentiation

open FStar.Mul

open Lib.IntTypes
open Lib.Sequence

module S = Lib.Exponentiation
module Loops = Lib.LoopCombinators

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

(**
 This is a specification for generic exponentiation defined as
 a repeated application of a commutative monoid operation.

  • Modular Exponentiation: repeated modular multiplication
  • Elliptic Curve Scalar Multiplication: repeated point addition

 In hacl-star, in order to obtain a verified C implementation,
 we split our proofs into three steps:

  • high-level specification (lib/Lib.Exponentiation)
  • low-level specification (specs/Spec.Exponentiation)
  • low-star implementation (code/bignum/Hacl.Impl.Exponentiation)

 For example, to efficiently compute the EC scalar multiplication
 for Ed25519, we use point addition and doubling formulas in
 projective coordinates (see specs/Spec.Ed25519).

  • we first prove that (points on the curve, aff_point_add) forms
    a commutative monoid (`mk_ed25519_comm_monoid`)
  • we then prove the relation between point addition and doubling
    formulas in projective and affine coordinates (`mk_ed25519_concrete_ops`)
  • finally, we can obtain any implementation of exponentiation,
    e.g., a double fixed-window method, by providing the corresponding
    instance of the `concrete_ops` type class (`point_mul_double`)

 Another example is using Montgomery arithmetic (code/bignum) to compute
 a modular exponentiation (lib/Lib.NatMod).
*)

inline_for_extraction
class to_comm_monoid (t:Type) = {
  a_spec: Type;
  comm_monoid: S.comm_monoid a_spec;
  refl: x:t -> a_spec;
}


inline_for_extraction
let one_st (t:Type) (to:to_comm_monoid t) = unit -> Pure t
  (requires True)
  (ensures  fun one ->
    to.refl one == to.comm_monoid.S.one)


inline_for_extraction
let mul_st (t:Type) (to:to_comm_monoid t) = x:t -> y:t -> Pure t
  (requires True)
  (ensures  fun xy ->
    to.refl xy == to.comm_monoid.S.mul (to.refl x) (to.refl y))


inline_for_extraction
let sqr_st (t:Type) (to:to_comm_monoid t) = x:t -> Pure t
  (requires True)
  (ensures  fun xy ->
    to.refl xy == to.comm_monoid.S.mul (to.refl x) (to.refl x))


inline_for_extraction
class concrete_ops (t:Type) = {
  to: to_comm_monoid t;
  one: one_st t to;
  mul: mul_st t to;
  sqr: sqr_st t to;
}


let exp_rl_f (#t:Type) (k:concrete_ops t)
  (bBits:nat) (b:nat{b < pow2 bBits})
  (i:nat{i < bBits}) ((acc, c) : tuple2 t t) : tuple2 t t
 =
  let acc = if (S.get_ith_bit bBits b i = 0) then acc else k.mul acc c in
  let c = k.sqr c in
  (acc, c)


let exp_rl (#t:Type) (k:concrete_ops t) (a:t) (bBits:nat) (b:nat{b < pow2 bBits}) : t =
  let one = k.one () in
  let (acc, c) = Loops.repeati bBits (exp_rl_f k bBits b) (one, a) in
  acc


val exp_rl_lemma: #t:Type -> k:concrete_ops t -> a:t -> bBits:nat -> b:nat{b < pow2 bBits} ->
  Lemma (k.to.refl (exp_rl k a bBits b) == S.exp_rl k.to.comm_monoid (k.to.refl a) bBits b)


let exp_mont_ladder_swap_f (#t:Type) (k:concrete_ops t)
  (bBits:nat) (b:nat{b < pow2 bBits})
  (i:nat{i < bBits}) ((r0, r1, privbit) : tuple3 t t nat) : tuple3 t t nat
 =
  let bit = S.get_ith_bit bBits b (bBits - 1 - i) in
  let sw = (bit + privbit) % 2 in
  let r0, r1 = S.cswap sw r0 r1 in
  let r0, r1 = (k.sqr r0, k.mul r1 r0) in
  (r0, r1, bit)


let exp_mont_ladder_swap (#t:Type) (k:concrete_ops t) (a:t) (bBits:nat) (b:nat{b < pow2 bBits}) : t =
  let (r0, r1, sw) = Loops.repeati bBits (exp_mont_ladder_swap_f k bBits b) (one (), a, 0) in
  let (r0, r1) = S.cswap sw r0 r1 in
  r0


val exp_mont_ladder_swap_lemma: #t:Type -> k:concrete_ops t -> a:t -> bBits:nat -> b:nat{b < pow2 bBits} ->
  Lemma (k.to.refl (exp_mont_ladder_swap k a bBits b) == S.exp_mont_ladder_swap k.to.comm_monoid (k.to.refl a) bBits b)


let exp_pow2 (#t:Type) (k:concrete_ops t) (a:t) (b:nat) : t =
  Loops.repeat b k.sqr a


val exp_pow2_lemma: #t:Type -> k:concrete_ops t -> a:t -> b:nat ->
  Lemma (k.to.refl (exp_pow2 k a b) == S.exp_pow2 k.to.comm_monoid (k.to.refl a) b)


[@(strict_on_arguments [3])]
let rec pow (#t:Type) (k:concrete_ops t) (a:t) (b:nat) : t =
  if b = 0 then k.one ()
  else k.mul a (pow k a (b - 1))


val pow_eq0: #t:Type -> k:concrete_ops t -> a:t ->
  Lemma (pow k a 0 == k.one ())

val pow_unfold: #t:Type -> k:concrete_ops t -> a:t -> i:pos ->
  Lemma (pow k a i == k.mul a (pow k a (i - 1)))

val pow_lemma: #t:Type -> k:concrete_ops t -> a:t -> b:nat ->
  Lemma (k.to.refl (pow k a b) == S.pow k.to.comm_monoid (k.to.refl a) b)


let exp_fw_acc0 (#t:Type0) (k:concrete_ops t) (a:t)
  (bBits:nat) (b:nat{b < pow2 bBits}) (l:pos{bBits % l <> 0}) : t
 =
  let bits_c = S.get_ith_lbits bBits b (bBits / l * l) l in
  pow k a bits_c


let mul_acc_pow_a_bits_l (#t:Type) (k:concrete_ops t) (a:t)
  (bBits:nat) (b:nat{b < pow2 bBits}) (l:pos) (i:nat{i < bBits / l}) (acc:t) : t
 =
  let bits_l = S.get_bits_l bBits b l i in
  k.mul acc (pow k a bits_l)


let exp_fw_f (#t:Type) (k:concrete_ops t) (a:t)
  (bBits:nat) (b:nat{b < pow2 bBits}) (l:pos)
  (i:nat{i < bBits / l}) (acc:t) : t
 =
  let acc1 = exp_pow2 k acc l in
  mul_acc_pow_a_bits_l k a bBits b l i acc1


let exp_fw (#t:Type) (k:concrete_ops t) (a:t) (bBits:nat) (b:nat{b < pow2 bBits}) (l:pos) : t =
  let acc0 = if bBits % l = 0 then one () else exp_fw_acc0 k a bBits b l in
  Loops.repeati (bBits / l) (exp_fw_f k a bBits b l) acc0


val exp_fw_lemma: #t:Type -> k:concrete_ops t -> a:t -> bBits:nat -> b:nat{b < pow2 bBits} -> l:pos ->
  Lemma (k.to.refl (exp_fw k a bBits b l) == S.exp_fw k.to.comm_monoid (k.to.refl a) bBits b l)


///  Multi-Exponentiation

// Double exponentiation [a1^b1 `mul` a2^b2]
//-------------------------------------------

let exp_double_fw_acc0 (#t:Type) (k:concrete_ops t)
  (a1:t) (bBits:nat) (b1:nat{b1 < pow2 bBits})
  (a2:t) (b2:nat{b2 < pow2 bBits}) (l:pos{bBits % l <> 0}) : t
 =
  let acc_a1 = exp_fw_acc0 k a1 bBits b1 l in
  let acc_a2 = exp_fw_acc0 k a2 bBits b2 l in
  k.mul acc_a1 acc_a2


let exp_double_fw_f (#t:Type) (k:concrete_ops t)
  (a1:t) (bBits:nat) (b1:nat{b1 < pow2 bBits})
  (a2:t) (b2:nat{b2 < pow2 bBits}) (l:pos)
  (i:nat{i < bBits / l}) (acc:t) : t
 =
  let acc1 = exp_fw_f k a2 bBits b2 l i acc in
  mul_acc_pow_a_bits_l k a1 bBits b1 l i acc1


let exp_double_fw (#t:Type) (k:concrete_ops t)
  (a1:t) (bBits:nat) (b1:nat{b1 < pow2 bBits})
  (a2:t) (b2:nat{b2 < pow2 bBits}) (l:pos) : t
 =
  let acc0 =
    if bBits % l = 0 then one ()
    else exp_double_fw_acc0 k a1 bBits b1 a2 b2 l in

  Loops.repeati (bBits / l)
    (exp_double_fw_f k a1 bBits b1 a2 b2 l) acc0


val exp_double_fw_lemma: #t:Type -> k:concrete_ops t
  -> a1:t -> bBits:nat -> b1:nat{b1 < pow2 bBits}
  -> a2:t -> b2:nat{b2 < pow2 bBits} -> l:pos ->
  Lemma (k.to.refl (exp_double_fw k a1 bBits b1 a2 b2 l) ==
    S.exp_double_fw k.to.comm_monoid (k.to.refl a1) bBits b1 (k.to.refl a2) b2 l)

// [a1^b1 `mul` a2^b2 `mul` a3^b3 `mul` a4^b4]
//----------------------------------------------

let exp_four_fw_acc0 (#t:Type) (k:concrete_ops t)
  (a1:t) (bBits:nat) (b1:nat{b1 < pow2 bBits})
  (a2:t) (b2:nat{b2 < pow2 bBits})
  (a3:t) (b3:nat{b3 < pow2 bBits})
  (a4:t) (b4:nat{b4 < pow2 bBits})
  (l:pos{bBits % l <> 0}) : t
 =
  let acc_a1 = exp_fw_acc0 k a1 bBits b1 l in
  let acc_a2 = exp_fw_acc0 k a2 bBits b2 l in
  let acc_a3 = exp_fw_acc0 k a3 bBits b3 l in
  let acc_a4 = exp_fw_acc0 k a4 bBits b4 l in
  let acc = k.mul acc_a1 acc_a2 in
  let acc = k.mul acc acc_a3 in
  let acc = k.mul acc acc_a4 in
  acc


let exp_four_fw_f (#t:Type) (k:concrete_ops t)
  (a1:t) (bBits:nat) (b1:nat{b1 < pow2 bBits})
  (a2:t) (b2:nat{b2 < pow2 bBits})
  (a3:t) (b3:nat{b3 < pow2 bBits})
  (a4:t) (b4:nat{b4 < pow2 bBits})
  (l:pos) (i:nat{i < bBits / l}) (acc:t) : t
 =
  let acc = exp_fw_f k a4 bBits b4 l i acc in
  let acc = mul_acc_pow_a_bits_l k a3 bBits b3 l i acc in
  let acc = mul_acc_pow_a_bits_l k a2 bBits b2 l i acc in
  let acc = mul_acc_pow_a_bits_l k a1 bBits b1 l i acc in
  acc


let exp_four_fw (#t:Type) (k:concrete_ops t)
  (a1:t) (bBits:nat) (b1:nat{b1 < pow2 bBits})
  (a2:t) (b2:nat{b2 < pow2 bBits})
  (a3:t) (b3:nat{b3 < pow2 bBits})
  (a4:t) (b4:nat{b4 < pow2 bBits})
  (l:pos) : t
 =
  let acc0 =
    if bBits % l = 0 then one ()
    else exp_four_fw_acc0 k a1 bBits b1 a2 b2 a3 b3 a4 b4 l in

  Loops.repeati (bBits / l)
    (exp_four_fw_f k a1 bBits b1 a2 b2 a3 b3 a4 b4 l) acc0


val exp_four_fw_lemma: #t:Type -> k:concrete_ops t
  -> a1:t -> bBits:nat -> b1:nat{b1 < pow2 bBits}
  -> a2:t -> b2:nat{b2 < pow2 bBits}
  -> a3:t -> b3:nat{b3 < pow2 bBits}
  -> a4:t -> b4:nat{b4 < pow2 bBits}
  -> l:pos ->
  Lemma (k.to.refl (exp_four_fw k a1 bBits b1 a2 b2 a3 b3 a4 b4 l) ==
    S.exp_four_fw k.to.comm_monoid (k.to.refl a1) bBits b1 (k.to.refl a2)
      b2 (k.to.refl a3) b3 (k.to.refl a4) b4 l)
