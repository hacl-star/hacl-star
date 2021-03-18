module Hacl.Spec.Bignum.GenericField

open FStar.Mul

open Lib.IntTypes
open Lib.Sequence

open Hacl.Spec.Bignum.Definitions

module Euclid = FStar.Math.Euclid
module LE = Lib.Exponentiation
module M = Hacl.Spec.Montgomery.Lemmas
module E = Hacl.Spec.Exponentiation.Lemmas
module BE = Hacl.Spec.Bignum.Exponentiation
module BM = Hacl.Spec.Bignum.Montgomery
module BN = Hacl.Spec.Bignum
module BB = Hacl.Spec.Bignum.Base
module BIL = Hacl.Spec.Bignum.ModInvLimb
module BI = Hacl.Spec.Bignum.ModInv


friend Hacl.Spec.Bignum.Exponentiation

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

//////////////////////////////////////////

val mul_zero_lemma: n:pos{Euclid.is_prime n} -> x:int -> y:int ->
  Lemma (x * y % n == 0 <==> (x % n == 0 \/ y % n == 0))
let mul_zero_lemma n x y =
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


val from_mont_add_lemma: #t:limb_t -> k:bn_mont_ctx t{bn_mont_ctx_inv k} -> aM:lbignum t k.len -> bM:lbignum t k.len -> Lemma
  (requires bn_v aM < bn_v k.n /\ bn_v bM < bn_v k.n)
  (ensures
   (let cM = (bn_v aM + bn_v bM) % bn_v k.n in
    let c = M.from_mont (bits t) k.len (bn_v k.n) (v k.mu) cM in
    let a = M.from_mont (bits t) k.len (bn_v k.n) (v k.mu) (bn_v aM) in
    let b = M.from_mont (bits t) k.len (bn_v k.n) (v k.mu) (bn_v bM) in
    c == (a + b) % bn_v k.n))

let from_mont_add_lemma #t k aM bM =
  let r = pow2 (bits t * k.len) in
  let d, _ = M.eea_pow2_odd (bits t * k.len) (bn_v k.n) in
  bn_eval_bound k.n k.len;
  M.mont_preconditions (bits t) k.len (bn_v k.n) (v k.mu);
  assert (r * d % bn_v k.n == 1 /\ bn_v k.n < r /\ (1 + bn_v k.n * v k.mu) % pow2 (bits t) == 0);

  let cM = (bn_v aM + bn_v bM) % bn_v k.n in
  let c = M.from_mont (bits t) k.len (bn_v k.n) (v k.mu) cM in
  let a = M.from_mont (bits t) k.len (bn_v k.n) (v k.mu) (bn_v aM) in
  let b = M.from_mont (bits t) k.len (bn_v k.n) (v k.mu) (bn_v bM) in

  M.from_mont_lemma (bits t) k.len (bn_v k.n) d (v k.mu) cM;
  assert (c == cM * d % bn_v k.n);

  calc (==) { //c
    cM * d % bn_v k.n;
    (==) { }
    (bn_v aM + bn_v bM) % bn_v k.n * d % bn_v k.n;
    (==) { Math.Lemmas.lemma_mod_mul_distr_l (bn_v aM + bn_v bM) d (bn_v k.n) }
    (bn_v aM + bn_v bM) * d % bn_v k.n;
    (==) { Math.Lemmas.distributivity_add_left (bn_v aM) (bn_v bM) d }
    (bn_v aM * d + bn_v bM * d) % bn_v k.n;
    (==) { Math.Lemmas.modulo_distributivity (bn_v aM * d) (bn_v bM * d) (bn_v k.n) }
    (bn_v aM * d % bn_v k.n + bn_v bM * d % bn_v k.n) % bn_v k.n;
    };

  M.from_mont_lemma (bits t) k.len (bn_v k.n) d (v k.mu) (bn_v aM);
  M.from_mont_lemma (bits t) k.len (bn_v k.n) d (v k.mu) (bn_v bM)


val from_mont_sub_lemma: #t:limb_t -> k:bn_mont_ctx t{bn_mont_ctx_inv k} -> aM:lbignum t k.len -> bM:lbignum t k.len -> Lemma
  (requires bn_v aM < bn_v k.n /\ bn_v bM < bn_v k.n)
  (ensures
   (let cM = (bn_v aM - bn_v bM) % bn_v k.n in
    let c = M.from_mont (bits t) k.len (bn_v k.n) (v k.mu) cM in
    let a = M.from_mont (bits t) k.len (bn_v k.n) (v k.mu) (bn_v aM) in
    let b = M.from_mont (bits t) k.len (bn_v k.n) (v k.mu) (bn_v bM) in
    c == (a - b) % bn_v k.n))

let from_mont_sub_lemma #t k aM bM =
  let r = pow2 (bits t * k.len) in
  let d, _ = M.eea_pow2_odd (bits t * k.len) (bn_v k.n) in
  bn_eval_bound k.n k.len;
  M.mont_preconditions (bits t) k.len (bn_v k.n) (v k.mu);
  assert (r * d % bn_v k.n == 1 /\ bn_v k.n < r /\ (1 + bn_v k.n * v k.mu) % pow2 (bits t) == 0);

  let cM = (bn_v aM - bn_v bM) % bn_v k.n in
  let c = M.from_mont (bits t) k.len (bn_v k.n) (v k.mu) cM in
  let a = M.from_mont (bits t) k.len (bn_v k.n) (v k.mu) (bn_v aM) in
  let b = M.from_mont (bits t) k.len (bn_v k.n) (v k.mu) (bn_v bM) in

  M.from_mont_lemma (bits t) k.len (bn_v k.n) d (v k.mu) cM;
  assert (c == cM * d % bn_v k.n);

  calc (==) { //c
    cM * d % bn_v k.n;
    (==) { }
    (bn_v aM - bn_v bM) % bn_v k.n * d % bn_v k.n;
    (==) { Math.Lemmas.lemma_mod_mul_distr_l (bn_v aM - bn_v bM) d (bn_v k.n) }
    (bn_v aM - bn_v bM) * d % bn_v k.n;
    (==) { Math.Lemmas.distributivity_sub_left (bn_v aM) (bn_v bM) d }
    (bn_v aM * d - bn_v bM * d) % bn_v k.n;
    (==) { Math.Lemmas.lemma_mod_plus_distr_l (bn_v aM * d) (- bn_v bM * d) (bn_v k.n) }
    (bn_v aM * d % bn_v k.n - bn_v bM * d) % bn_v k.n;
    (==) { Math.Lemmas.lemma_mod_sub_distr (bn_v aM * d % bn_v k.n) (bn_v bM * d) (bn_v k.n) }
    (bn_v aM * d % bn_v k.n - bn_v bM * d % bn_v k.n) % bn_v k.n;
    };

  M.from_mont_lemma (bits t) k.len (bn_v k.n) d (v k.mu) (bn_v aM);
  M.from_mont_lemma (bits t) k.len (bn_v k.n) d (v k.mu) (bn_v bM)


val from_mont_mul_lemma: #t:limb_t -> k:bn_mont_ctx t{bn_mont_ctx_inv k} -> aM:lbignum t k.len -> bM:lbignum t k.len -> Lemma
  (requires bn_v aM < bn_v k.n /\ bn_v bM < bn_v k.n)
  (ensures
   (let cM = M.mont_mul (bits t) k.len (bn_v k.n) (v k.mu) (bn_v aM) (bn_v bM) in
    let c = M.from_mont (bits t) k.len (bn_v k.n) (v k.mu) cM in
    let a = M.from_mont (bits t) k.len (bn_v k.n) (v k.mu) (bn_v aM) in
    let b = M.from_mont (bits t) k.len (bn_v k.n) (v k.mu) (bn_v bM) in
    c == a * b % bn_v k.n))

let from_mont_mul_lemma #t k aM bM =
  let r = pow2 (bits t * k.len) in
  let d, _ = M.eea_pow2_odd (bits t * k.len) (bn_v k.n) in
  bn_eval_bound k.n k.len;
  M.mont_preconditions (bits t) k.len (bn_v k.n) (v k.mu);
  assert (r * d % bn_v k.n == 1 /\ bn_v k.n < r /\ (1 + bn_v k.n * v k.mu) % pow2 (bits t) == 0);

  let cM = M.mont_mul (bits t) k.len (bn_v k.n) (v k.mu) (bn_v aM) (bn_v bM) in
  let c = M.from_mont (bits t) k.len (bn_v k.n) (v k.mu) cM in
  let a = M.from_mont (bits t) k.len (bn_v k.n) (v k.mu) (bn_v aM) in
  let b = M.from_mont (bits t) k.len (bn_v k.n) (v k.mu) (bn_v bM) in

  M.mont_mul_lemma (bits t) k.len (bn_v k.n) d (v k.mu) (bn_v aM) (bn_v bM);
  assert (cM == bn_v aM * bn_v bM * d % bn_v k.n);

  M.from_mont_lemma (bits t) k.len (bn_v k.n) d (v k.mu) cM;

  calc (==) { //c
    cM * d % bn_v k.n;
    (==) { }
    (bn_v aM * bn_v bM * d % bn_v k.n) * d % bn_v k.n;
    (==) { Math.Lemmas.lemma_mod_mul_distr_l (bn_v aM * bn_v bM * d) d (bn_v k.n) }
    bn_v aM * bn_v bM * d * d % bn_v k.n;
    (==) { Math.Lemmas.paren_mul_right (bn_v aM) (bn_v bM) d }
    bn_v aM * (bn_v bM * d) * d % bn_v k.n;
    (==) {
      Math.Lemmas.paren_mul_right (bn_v aM) (bn_v bM * d) d;
      Math.Lemmas.swap_mul (bn_v bM * d) d;
      Math.Lemmas.paren_mul_right (bn_v aM) d (bn_v bM * d) }
    bn_v aM * d * (bn_v bM * d) % bn_v k.n;
    (==) { Math.Lemmas.lemma_mod_mul_distr_l (bn_v aM * d) (bn_v bM * d) (bn_v k.n) }
    (bn_v aM * d % bn_v k.n) * (bn_v bM * d) % bn_v k.n;
    (==) { Math.Lemmas.lemma_mod_mul_distr_r (bn_v aM * d % bn_v k.n) (bn_v bM * d) (bn_v k.n) }
    (bn_v aM * d % bn_v k.n) * (bn_v bM * d % bn_v k.n) % bn_v k.n;
    };

  M.from_mont_lemma (bits t) k.len (bn_v k.n) d (v k.mu) (bn_v aM);
  M.from_mont_lemma (bits t) k.len (bn_v k.n) d (v k.mu) (bn_v bM)


val from_mont_one_lemma: #t:limb_t -> k:bn_mont_ctx t{bn_mont_ctx_inv k} -> Lemma
   (let oneM = M.mont_one (bits t) k.len (bn_v k.n) (v k.mu) in
    let one = M.from_mont (bits t) k.len (bn_v k.n) (v k.mu) oneM in
    one == 1)

let from_mont_one_lemma #t k =
  let r = pow2 (bits t * k.len) in
  let d, _ = M.eea_pow2_odd (bits t * k.len) (bn_v k.n) in
  bn_eval_bound k.n k.len;
  M.mont_preconditions (bits t) k.len (bn_v k.n) (v k.mu);
  assert (r * d % bn_v k.n == 1 /\ bn_v k.n < r /\ (1 + bn_v k.n * v k.mu) % pow2 (bits t) == 0);

  let oneM = M.mont_one (bits t) k.len (bn_v k.n) (v k.mu) in
  M.mont_one_lemma (bits t) k.len (bn_v k.n) d (v k.mu);
  assert (oneM == r % bn_v k.n);
  let one = M.from_mont (bits t) k.len (bn_v k.n) (v k.mu) oneM in
  M.from_mont_lemma (bits t) k.len (bn_v k.n) d (v k.mu) oneM;
  assert (one == oneM * d % bn_v k.n);
  assert (one == (r % bn_v k.n) * d % bn_v k.n);
  M.lemma_mont_id (bn_v k.n) r d 1;
  assert (one == 1 % bn_v k.n);
  Math.Lemmas.small_mod 1 (bn_v k.n)


val from_mont_exp_lemma: #t:limb_t -> k:bn_mont_ctx t{bn_mont_ctx_inv k} -> aM:lbignum t k.len -> b:pos -> Lemma
  (requires bn_v aM < bn_v k.n)
  (ensures
   (let cM = LE.pow (BE.mk_bn_mont_comm_monoid k.n k.mu) aM b in
    let c = M.from_mont (bits t) k.len (bn_v k.n) (v k.mu) (bn_v cM) in
    let a = M.from_mont (bits t) k.len (bn_v k.n) (v k.mu) (bn_v aM) in
    c == Lib.NatMod.pow a b % bn_v k.n))

let from_mont_exp_lemma #t k aM b =
  let ke = BE.mk_bn_mont_comm_monoid k.n k.mu in
  let cM = LE.pow ke aM b in
  BE.lemma_bn_mont_pre_is_mont_pre k.n k.mu;
  BE.pow_bn_mont_is_pow_nat_mont_ll k.n k.mu aM b;
  assert (bn_v cM == LE.pow (E.mk_nat_mont_ll_comm_monoid (bits t) k.len (bn_v k.n) (v k.mu)) (bn_v aM) b);

  let r = pow2 (bits t * k.len) in
  let d, _ = M.eea_pow2_odd (bits t * k.len) (bn_v k.n) in
  M.mont_preconditions_d (bits t) k.len (bn_v k.n);
  E.pow_nat_mont_ll_is_pow_nat_mont (bits t) k.len (bn_v k.n) (v k.mu) (bn_v aM) b;
  assert (bn_v cM == LE.pow (E.mk_nat_mont_comm_monoid (bn_v k.n) r d) (bn_v aM) b);
  E.pow_nat_mont_is_pow (bn_v k.n) r d (bn_v aM) b;
  assert (bn_v cM == Lib.NatMod.pow (bn_v aM) b * (1 * r % bn_v k.n) * Lib.NatMod.pow d b % bn_v k.n);

  let tmp1 = Lib.NatMod.pow (bn_v aM) b in
  let tmp2 = Lib.NatMod.pow d b in
  let tmp3 = Lib.NatMod.pow (bn_v aM * d % bn_v k.n) b in

  calc (==) { //cM
    tmp1 * (1 * r % bn_v k.n) * tmp2 % bn_v k.n;
    (==) {
      Math.Lemmas.paren_mul_right tmp1 (1 * r % bn_v k.n) tmp2;
      Math.Lemmas.swap_mul (1 * r % bn_v k.n) tmp2;
      Math.Lemmas.paren_mul_right tmp1 tmp2 (1 * r % bn_v k.n) }
    tmp1 * tmp2 * (1 * r % bn_v k.n) % bn_v k.n;
    (==) { Math.Lemmas.lemma_mod_mul_distr_r (tmp1 * tmp2) (1 * r) (bn_v k.n) }
    tmp1 * tmp2 * r % bn_v k.n;
    (==) { Lib.NatMod.lemma_pow_mul_base (bn_v aM) d b }
    Lib.NatMod.pow (bn_v aM * d) b * r % bn_v k.n;
    (==) { Math.Lemmas.lemma_mod_mul_distr_l (Lib.NatMod.pow (bn_v aM * d) b) r (bn_v k.n) }
    Lib.NatMod.pow (bn_v aM * d) b % bn_v k.n * r % bn_v k.n;
    (==) { Lib.NatMod.lemma_pow_mod_base (bn_v aM * d) b (bn_v k.n) }
    tmp3 % bn_v k.n * r % bn_v k.n;
    (==) { Math.Lemmas.lemma_mod_mul_distr_l tmp3 r (bn_v k.n) }
    tmp3 * r % bn_v k.n;
    };

  assert (bn_v cM == tmp3 * r % bn_v k.n);
  let c = M.from_mont (bits t) k.len (bn_v k.n) (v k.mu) (bn_v cM) in
  M.from_mont_lemma (bits t) k.len (bn_v k.n) d (v k.mu) (bn_v cM);
  //assert (c == bn_v cM * d % bn_v k.n);
  calc (==) { //c
    bn_v cM * d % bn_v k.n;
    (==) { }
    tmp3 * r % bn_v k.n * d % bn_v k.n;
    (==) { M.lemma_mont_id (bn_v k.n) r d tmp3 }
    tmp3 % bn_v k.n;
    };

  M.from_mont_lemma (bits t) k.len (bn_v k.n) d (v k.mu) (bn_v aM)


val from_mont_lemma_nonzero: #t:limb_t -> k:bn_mont_ctx t{bn_mont_ctx_inv k} -> aM:lbignum t k.len -> Lemma
  (requires 0 < bn_v aM /\ bn_v aM < bn_v k.n)
  (ensures
   (let a = M.from_mont (bits t) k.len (bn_v k.n) (v k.mu) (bn_v aM) in
    a <> 0 /\ a < bn_v k.n))

let from_mont_lemma_nonzero #t k aM =
  let r = pow2 (bits t * k.len) in
  let d, k1 = M.eea_pow2_odd (bits t * k.len) (bn_v k.n) in
  bn_eval_bound k.n k.len;
  M.mont_preconditions (bits t) k.len (bn_v k.n) (v k.mu);

  let a = M.from_mont (bits t) k.len (bn_v k.n) (v k.mu) (bn_v aM) in
  M.from_mont_lemma (bits t) k.len (bn_v k.n) d (v k.mu) (bn_v aM);
  assert (bn_v aM < bn_v k.n);
  Math.Lemmas.small_mod (bn_v aM) (bn_v k.n);
  assert (bn_v aM % bn_v k.n <> 0);

  let d1 = -d in
  assert (0 < d1 /\ d1 < bn_v k.n);
  Math.Lemmas.lemma_mod_sub_1 d1 (bn_v k.n);
  assert (d % bn_v k.n == bn_v k.n - (d1 % bn_v k.n));
  assert (d % bn_v k.n <> 0);
  mul_nonzero_lemma (bn_v k.n) (bn_v aM) d;
  assert (bn_v aM * d % bn_v k.n <> 0)


val bn_field_inv_lemma: #t:limb_t -> k:bn_mont_ctx t{bn_mont_ctx_inv k} -> aM:lbignum t k.len -> Lemma
  (requires 0 < bn_v aM /\ bn_v aM < bn_v k.n)
  (ensures (let n2 = bn_v k.n - 2 in
    let ke = BE.mk_bn_mont_comm_monoid k.n k.mu in
    let aInvM = LE.exp_fw ke aM k.nBits n2 4 in
    let aInv = M.from_mont (bits t) k.len (bn_v k.n) (v k.mu) (bn_v aInvM) in
    let a = M.from_mont (bits t) k.len (bn_v k.n) (v k.mu) (bn_v aM) in
    aInv * a % bn_v k.n == 1))

let bn_field_inv_lemma #t k aM =
  let n2 = bn_v k.n - 2 in
  let ke = BE.mk_bn_mont_comm_monoid k.n k.mu in
  let accM = LE.exp_fw ke aM k.nBits n2 4 in
  LE.exp_fw_lemma ke aM k.nBits n2 4;
  assert (accM == LE.pow ke aM n2);
  from_mont_exp_lemma #t k aM n2;

  let acc = M.from_mont (bits t) k.len (bn_v k.n) (v k.mu) (bn_v accM) in
  let a = M.from_mont (bits t) k.len (bn_v k.n) (v k.mu) (bn_v aM) in
  from_mont_lemma_nonzero #t k aM;
  assert (0 < a /\ a < bn_v k.n);
  Lib.NatMod.lemma_pow_mod #(bn_v k.n) a n2;
  assert (acc == Lib.NatMod.pow_mod #(bn_v k.n) a n2);
  BI.mod_inv_prime_lemma (bn_v k.n) a;
  assert (Lib.NatMod.pow_mod #(bn_v k.n) a n2 * a % bn_v k.n == 1)

///////////////////////////////////////

let bn_field_get_len #t k = k.len


let bn_field_init #t #len nBits n =
  BM.bn_precomp_r2_mod_n_lemma (nBits - 1) n;
  let r2 = BM.bn_precomp_r2_mod_n (nBits - 1) n in
  assert (bn_v r2 == pow2 (2 * bits t * len) % bn_v n);

  let mu = BIL.mod_inv_limb n.[0] in
  BIL.bn_mod_inv_limb_lemma n;
  assert ((1 + (bn_v n % pow2 (bits t)) * v mu) % pow2 (bits t) == 0);

  { nBits = nBits; len = len; n = n; mu = mu; r2 = r2 }


let bn_to_field #t k a =
  let aM = BM.bn_to_mont k.n k.mu k.r2 a in
  BM.bn_to_mont_lemma k.n k.mu k.r2 a;
  aM


let bn_from_field #t k aM =
  let a = BM.bn_from_mont k.n k.mu aM in
  BM.bn_from_mont_lemma k.n k.mu aM;
  a


let bn_from_to_field_lemma #t k a =
  let aM = bn_to_field k a in
  let r = pow2 (bits t * k.len) in
  let d, _ = M.eea_pow2_odd (bits t * k.len) (bn_v k.n) in
  bn_eval_bound k.n k.len;
  M.mont_preconditions (bits t) k.len (bn_v k.n) (v k.mu);
  assert (r * d % bn_v k.n == 1 /\ bn_v k.n < r /\ (1 + bn_v k.n * v k.mu) % pow2 (bits t) == 0);

  M.from_mont_lemma (bits t) k.len (bn_v k.n) d (v k.mu) (bn_v aM);
  assert (bn_v (bn_from_field k aM) == bn_v aM * d % bn_v k.n);
  M.to_mont_lemma (bits t) k.len (bn_v k.n) d (v k.mu) (bn_v a);
  assert (bn_v aM == bn_v a * r % bn_v k.n);
  M.lemma_mont_id (bn_v k.n) (pow2 (bits t * k.len)) d (bn_v a);
  assert (bn_v (bn_from_field k aM) == bn_v a % bn_v k.n);
  Math.Lemmas.small_mod (bn_v a) (bn_v k.n);
  assert (bn_v (bn_from_field k aM) == bn_v a)


let bn_field_add #t k aM bM =
  let cM = BN.bn_add_mod_n k.n aM bM in
  BN.bn_add_mod_n_lemma k.n aM bM;
  assert (bn_v cM == (bn_v aM + bn_v bM) % bn_v k.n);
  from_mont_add_lemma #t k aM bM;
  cM


let bn_field_sub #t k aM bM =
  let cM = BN.bn_sub_mod_n k.n aM bM in
  BN.bn_sub_mod_n_lemma k.n aM bM;
  assert (bn_v cM == (bn_v aM - bn_v bM) % bn_v k.n);
  from_mont_sub_lemma #t k aM bM;
  cM


let bn_field_mul #t k aM bM =
  let cM = BM.bn_mont_mul k.n k.mu aM bM in
  BM.bn_mont_mul_lemma k.n k.mu aM bM;
  from_mont_mul_lemma #t k aM bM;
  cM


let bn_field_sqr #t k aM =
  let cM = BM.bn_mont_sqr k.n k.mu aM in
  BM.bn_mont_sqr_lemma k.n k.mu aM;
  from_mont_mul_lemma #t k aM aM;
  cM


let bn_field_one #t k =
  let oneM = BM.bn_mont_one k.n k.mu r2 in
  BM.bn_mont_one_lemma k.n k.mu k.r2;
  from_mont_one_lemma #t k;
  oneM


let bn_field_inv #t k aM =
  let c, n2 = BN.bn_sub1 k.n (uint #t 2) in
  BN.bn_sub1_lemma k.n (uint #t 2);
  assert (bn_v n2 - v c * pow2 (bits t * k.len) == bn_v k.n - 2);
  bn_eval_bound n2 k.len;
  bn_eval_bound k.n k.len;
  assert (v c = 0);
  assert (bn_v n2 == bn_v k.n - 2);

  bn_field_inv_lemma #t k aM;
  let ke = BE.mk_bn_mont_comm_monoid k.n k.mu in
  let aInvM = LE.exp_fw ke aM k.nBits (bn_v n2) 4 in
  aInvM
