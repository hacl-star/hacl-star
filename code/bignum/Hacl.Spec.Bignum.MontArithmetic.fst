module Hacl.Spec.Bignum.MontArithmetic

open FStar.Mul

open Lib.IntTypes
open Lib.Sequence

open Hacl.Spec.Bignum.Definitions

module M = Hacl.Spec.Montgomery.Lemmas
module BM = Hacl.Spec.Bignum.Montgomery
module BN = Hacl.Spec.Bignum
module BB = Hacl.Spec.Bignum.Base
module BL = Hacl.Spec.Bignum.Lib
module BIL = Hacl.Spec.Bignum.ModInvLimb

module E = Hacl.Spec.Exponentiation.Lemmas
module ME = Hacl.Spec.Bignum.MontExponentiation

module Euclid = FStar.Math.Euclid
module BI = Hacl.Spec.Bignum.ModInv

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

//////////////////////////////////////////

val mul_zero_lemma: n:pos{Euclid.is_prime n} -> x:int -> y:int ->
  Lemma (x * y % n == 0 <==> (x % n == 0 \/ y % n == 0))
let mul_zero_lemma n x y =
  assert (0 % n = 0);
  if x % n = 0 then
    Math.Lemmas.lemma_mod_mul_distr_l x y n
  else
    if y % n = 0 then
      Math.Lemmas.lemma_mod_mul_distr_r x y n
    else
      if x * y % n = 0 then
        Math.Fermat.mod_mult_congr n x 0 y
      else ()


val mul_nonzero_lemma: n:pos{Euclid.is_prime n} -> x:int -> y:int -> Lemma
  (requires x % n <> 0 /\ y % n <> 0)
  (ensures  x * y % n <> 0)
let mul_nonzero_lemma n x y =
  mul_zero_lemma n x y


val from_mont_lemma_nonzero: pbits:pos -> rLen:pos -> n:pos -> mu:nat -> aM:nat -> Lemma
  (requires
    M.mont_pre pbits rLen n mu /\
    0 < aM /\ aM < n /\
    Euclid.is_prime n)
  (ensures
   (let a = M.from_mont pbits rLen n mu aM in
    0 < a /\ a < n))

let from_mont_lemma_nonzero pbits rLen n mu aM =
  let r = pow2 (pbits * rLen) in
  let d, _ = M.eea_pow2_odd (pbits * rLen) n in

  let a = M.from_mont pbits rLen n mu aM in
  M.from_mont_lemma pbits rLen n mu aM;
  assert (a == aM * d % n);
  assert (d <> 0);

  Math.Lemmas.small_mod aM n;
  assert (aM % n <> 0);

  let d1 = -d in
  assert (0 < d1 /\ d1 < n);
  Math.Lemmas.lemma_mod_sub_1 d1 n;
  assert ((-d1) % n == n - (d1 % n));
  assert (d % n <> 0);

  mul_nonzero_lemma n aM d;
  assert (a <> 0)

///////////////////////////////////////////////


let bn_field_get_len #t k = k.len


let bn_field_check_modulus #t #len n =
  let m = BM.bn_check_modulus n in
  BB.unsafe_bool_of_limb m


let bn_field_init #t #len n =
  let nBits = bits t * BL.bn_get_top_index n in
  BL.bn_low_bound_bits_lemma n;

  BM.bn_precomp_r2_mod_n_lemma nBits n;
  let r2 = BM.bn_precomp_r2_mod_n nBits n in
  assert (bn_v r2 == pow2 (2 * bits t * len) % bn_v n);

  let mu = BIL.mod_inv_limb n.[0] in
  BIL.bn_mod_inv_limb_lemma n;
  assert ((1 + bn_v n * v mu) % pow2 (bits t) == 0);

  bn_eval_bound n len;

  { len = len; n = n; mu = mu; r2 = r2 }


let bn_to_field #t k a =
  BM.bn_to_mont_lemma k.n k.mu k.r2 a;
  BM.bn_to_mont k.n k.mu k.r2 a


let bn_from_field #t k aM =
  BM.bn_from_mont_lemma k.n k.mu aM;
  BM.bn_from_mont k.n k.mu aM


let bn_from_to_field_lemma #t k a =
  bn_eval_bound a k.len;
  M.from_to_mont_lemma (bits t) k.len (bn_v k.n) (v k.mu) (bn_v a)


let bn_field_add #t k aM bM =
  BN.bn_add_mod_n_lemma k.n aM bM;
  M.from_mont_add_lemma (bits t) k.len (bn_v k.n) (v k.mu) (bn_v aM) (bn_v bM);
  BN.bn_add_mod_n k.n aM bM


let bn_field_sub #t k aM bM =
  BN.bn_sub_mod_n_lemma k.n aM bM;
  M.from_mont_sub_lemma (bits t) k.len (bn_v k.n) (v k.mu) (bn_v aM) (bn_v bM);
  BN.bn_sub_mod_n k.n aM bM


let bn_field_mul #t k aM bM =
  BM.bn_mont_mul_lemma k.n k.mu aM bM;
  M.from_mont_mul_lemma (bits t) k.len (bn_v k.n) (v k.mu) (bn_v aM) (bn_v bM);
  BM.bn_mont_mul k.n k.mu aM bM


let bn_field_sqr #t k aM =
  BM.bn_mont_sqr_lemma k.n k.mu aM;
  M.from_mont_mul_lemma (bits t) k.len (bn_v k.n) (v k.mu) (bn_v aM) (bn_v aM);
  BM.bn_mont_sqr k.n k.mu aM


let bn_field_one #t k =
  BM.bn_mont_one_lemma k.n k.mu k.r2;
  M.from_mont_one_lemma (bits t) k.len (bn_v k.n) (v k.mu);
  BM.bn_mont_one k.n k.mu r2


let bn_field_exp_consttime #t k aM bBits b =
  E.from_mont_exp_lemma (bits t) k.len (bn_v k.n) (v k.mu) (bn_v aM) (bn_v b);
  ME.bn_exp_mont_consttime k.n k.mu aM bBits b


let bn_field_exp_vartime #t k aM bBits b =
  E.from_mont_exp_lemma (bits t) k.len (bn_v k.n) (v k.mu) (bn_v aM) (bn_v b);
  ME.bn_exp_mont_vartime k.n k.mu aM bBits b


let bn_field_inv #t k aM =
  let n2 = BI.bn_mod_inv_prime_n2 k.n in
  assert (bn_v n2 == bn_v k.n - 2);
  let aInvM = bn_field_exp_vartime #t k aM (k.len * bits t) n2 in
  assert (bn_v (bn_from_field k aInvM) == Lib.NatMod.pow_mod #(bn_v k.n) (bn_v (bn_from_field k aM)) (bn_v n2));
  from_mont_lemma_nonzero (bits t) k.len (bn_v k.n) (v k.mu) (bn_v aM);
  assert (0 < bn_v (bn_from_field k aM));
  BI.mod_inv_prime_lemma (bn_v k.n) (bn_v (bn_from_field k aM));
  aInvM
