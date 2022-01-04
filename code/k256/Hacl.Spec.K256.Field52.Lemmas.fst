module Hacl.Spec.K256.Field52.Lemmas

open FStar.Mul
open Lib.IntTypes

module S = Spec.K256

include Hacl.Spec.K256.Field52.Definitions
include Hacl.Spec.K256.Field52

module LD = Hacl.Spec.K256.Field52.Definitions.Lemmas
module L1 = Hacl.Spec.K256.Field52.Lemmas1
module L2 = Hacl.Spec.K256.Field52.Lemmas2

#set-options "--z3rlimit 100 --fuel 0 --ifuel 0"

let load_felem5_lemma s =
  L1.load_felem5_lemma s


let store_felem5_lemma f =
  L1.store_felem5_lemma f


let add5_lemma m1 m2 f1 f2 =
  L1.add5_lemma m1 m2 f1 f2


let fadd5_lemma m1 m2 f1 f2 =
  let r = add5 f1 f2 in
  add5_lemma m1 m2 f1 f2;
  assert (as_nat5 r == as_nat5 f1 + as_nat5 f2);
  Math.Lemmas.modulo_distributivity (as_nat5 f1) (as_nat5 f2) S.prime


let mul15_lemma m1 m2 f c =
  L1.mul15_lemma m1 m2 f c


let fmul15_lemma m1 m2 f c =
  let r = mul15 f c in
  mul15_lemma m1 m2 f c;
  assert (as_nat5 r == v c * as_nat5 f);
  Math.Lemmas.lemma_mod_mul_distr_r (v c) (as_nat5 f) S.prime


#push-options "--ifuel 1"
let is_felem_zero_vartime5_lemma f = ()


let is_felem_ge_prime_vartime5_lemma f =
  let p =
   (u64 0xffffefffffc2f,
    u64 0xfffffffffffff,
    u64 0xfffffffffffff,
    u64 0xfffffffffffff,
    u64 0xffffffffffff) in
  assert_norm (S.prime = as_nat5 p);
  assert_norm (0xffffefffffc2f <= max52);
  assert_norm (0xfffffffffffff <= max52);
  assert_norm (0xffffffffffff <= max48);
  assert (felem_fits5 p (1,1,1,1,1));
  //LD.lemma_as_nat_decompose f;
  //LD.lemma_as_nat_decompose p;
  LD.lemma_as_nat_bound f;
  LD.lemma_as_nat_bound p


let is_felem_lt_vartime5_lemma f1 f2 = ()


let is_felem_lt_prime_minus_order_vartime5_lemma f =
  assert_norm (S.prime - S.q =
    0xda1722fc9baee + 0x1950b75fc4402 * pow52 + 0x1455123 * pow104)


let is_felem_eq_vartime5_lemma f1 f2 =
  if as_nat5 f1 = as_nat5 f2 then LD.as_nat_inj f1 f2
#pop-options


let normalize_weak5_lemma m f =
  let r = normalize_weak5 f in
  let (r0,r1,r2,r3,r4) = r in
  let (t0,t1,t2,t3,t4) = f in
  L2.normalize_weak5_lemma m f;
  assert (as_nat5 r == as_nat5 f - v t4 / pow2 48 * S.prime);
  Math.Lemmas.lemma_mod_sub (as_nat5 f) S.prime (v t4 / pow2 48)


let normalize5_lemma m f =
  L2.normalize5_lemma m f
