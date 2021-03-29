module Hacl.Spec.Bignum.ModInv

open FStar.Mul

open Lib.IntTypes
open Lib.Sequence
open Lib.LoopCombinators

open Hacl.Spec.Bignum.Definitions
open Hacl.Spec.Bignum

module Fermat = FStar.Math.Fermat
module Euclid = FStar.Math.Euclid

module BE = Hacl.Spec.Bignum.Exponentiation
module BM = Hacl.Spec.Bignum.Montgomery
module BN = Hacl.Spec.Bignum

#reset-options "--z3rlimit 50 --fuel 0 --ifuel 0"

#push-options "--fuel 1"
val pow_eq: a:nat -> n:nat -> Lemma (Fermat.pow a n == Lib.NatMod.pow a n)
let rec pow_eq a n =
  if n = 0 then ()
  else pow_eq a (n - 1)
#pop-options

val mod_inv_prime_lemma: n:nat{2 < n /\ Euclid.is_prime n} -> a:pos{a < n} ->
  Lemma (Lib.NatMod.pow_mod #n a (n - 2) * a % n = 1)

let mod_inv_prime_lemma n a =
  Math.Lemmas.small_mod a n;
  assert (a == a % n);
  assert (a <> 0 /\ a % n <> 0);

  calc (==) {
    Lib.NatMod.pow_mod #n a (n - 2) * a % n;
    (==) { Lib.NatMod.lemma_pow_mod #n a (n - 2) }
    Lib.NatMod.pow a (n - 2) % n * a % n;
    (==) { Math.Lemmas.lemma_mod_mul_distr_l (Lib.NatMod.pow a (n - 2)) a n }
    Lib.NatMod.pow a (n - 2) * a % n;
    (==) { Lib.NatMod.lemma_pow1 a; Lib.NatMod.lemma_pow_add a (n - 2) 1 }
    Lib.NatMod.pow a (n - 1) % n;
    (==) { pow_eq a (n - 1) }
    Fermat.pow a (n - 1) % n;
    (==) { Fermat.fermat_alt n a }
    1;
    }

//pow2 nBits < bn_v n /\ Euclid.is_prime (bn_v n) are still needed to be checked
val bn_check_mod_inv_prime:
    #t:limb_t
  -> #len:BN.bn_len t
  -> n:lbignum t len
  -> a:lbignum t len ->
  res:limb t{
    let b =
      bn_v n % 2 = 1 && 1 < bn_v n &&
      0 < bn_v a && bn_v a < bn_v n in
    v res == (if b then v (ones t SEC) else v (zeros t SEC))}

let bn_check_mod_inv_prime #t #len n a =
  let m0 = BM.bn_check_modulus n in
  let m1 = BN.bn_is_zero_mask a in
  BN.bn_is_zero_mask_lemma a;
  let m1' = lognot m1 in
  lognot_lemma m1;
  let m2 = BN.bn_lt_mask a n in
  BN.bn_lt_mask_lemma a n;
  logand_ones (m0 &. m1');
  logand_zeros (m0 &. m1');
  logand_ones m0;
  logand_zeros m0;
  m0 &. m1' &. m2


val bn_mod_inv_prime_n2:
    #t:limb_t
  -> #len:size_pos
  -> n:lbignum t len ->
  Pure (lbignum t len)
  (requires 1 < bn_v n)
  (ensures fun res ->
    bn_v res == bn_v n - 2)

let bn_mod_inv_prime_n2 #t #len n =
  let c, n2 = bn_sub1 n (uint #t 2) in
  bn_sub1_lemma n (uint #t 2);
  assert (bn_v n2 - v c * pow2 (bits t * len) == bn_v n - 2);
  bn_eval_bound n2 len;
  bn_eval_bound n len;
  assert (v c = 0);
  assert (bn_v n2 == bn_v n - 2);
  n2


let bn_mod_inv_prime_pre
  (#t:limb_t)
  (#len:BN.bn_len t)
  (n:lbignum t len)
  (a:lbignum t len)
 =
  bn_v n % 2 = 1 /\ 1 < bn_v n /\
  0 < bn_v a /\ bn_v a < bn_v n /\
  Euclid.is_prime (bn_v n)


val bn_mod_inv_prime_precomp:
    #t:limb_t
  -> #len:BN.bn_len t
  -> n:lbignum t len
  -> mu:limb t
  -> r2:lbignum t len
  -> a:lbignum t len ->
  Pure (lbignum t len)
  (requires
    bn_mod_inv_prime_pre n a /\
    bn_v r2 == pow2 (2 * bits t * len) % bn_v n /\
    (1 + bn_v n * v mu) % pow2 (bits t) == 0)
  (ensures fun res ->
    bn_v res * bn_v a % bn_v n = 1)

let bn_mod_inv_prime_precomp #t #len n mu r2 a =
  let n2 = bn_mod_inv_prime_n2 n in
  bn_eval_bound n len;
  let res = BE.bn_mod_exp_vartime_precompr2 len n r2 a (bits t * len) n2 in
  assert (bn_v res == Lib.NatMod.pow_mod #(bn_v n) (bn_v a) (bn_v n2));
  mod_inv_prime_lemma (bn_v n) (bn_v a);
  res


val bn_mod_inv_prime:
    #t:limb_t
  -> #len:BN.bn_len t
  -> nBits:size_nat
  -> n:lbignum t len
  -> a:lbignum t len ->
  Pure (lbignum t len)
  (requires
    bn_mod_inv_prime_pre n a /\
    nBits / bits t < len /\ pow2 nBits < bn_v n)
  (ensures fun res ->
    bn_v res * bn_v a % bn_v n = 1)

let bn_mod_inv_prime #t #len nBits n a =
  let r2, mu = BM.bn_mont_precomp nBits n in
  let res = bn_mod_inv_prime_precomp #t #len n mu r2 a in
  mod_inv_prime_lemma (bn_v n) (bn_v a);
  res
