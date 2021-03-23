module Hacl.Spec.Bignum.GenericField

open FStar.Mul

open Lib.IntTypes
open Lib.Sequence

open Hacl.Spec.Bignum.Definitions

module M = Hacl.Spec.Montgomery.Lemmas
module BM = Hacl.Spec.Bignum.Montgomery
module BN = Hacl.Spec.Bignum

//module LE = Lib.Exponentiation
//module E = Hacl.Spec.Exponentiation.Lemmas
//module BE = Hacl.Spec.Bignum.Exponentiation
//module Euclid = FStar.Math.Euclid
//module BI = Hacl.Spec.Bignum.ModInv

//friend Hacl.Spec.Bignum.Exponentiation

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

let bn_field_get_len #t k = k.len


let bn_field_init #t nBits n =
  let len = blocks nBits (bits t) in
  assert (nBits <= len * bits t);

  BM.bn_precomp_r2_mod_n_lemma (nBits - 1) n;
  let r2 = BM.bn_precomp_r2_mod_n (nBits - 1) n in
  assert (bn_v r2 == pow2 (2 * bits t * len) % bn_v n);

  let mu = Hacl.Spec.Bignum.ModInvLimb.mod_inv_limb n.[0] in
  Hacl.Spec.Bignum.ModInvLimb.bn_mod_inv_limb_lemma n;
  assert ((1 + bn_v n * v mu) % pow2 (bits t) == 0);

  bn_eval_bound n len;

  { nBits = nBits; len = len; n = n; mu = mu; r2 = r2 }


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


let bn_field_inv #t k aM = admit()
