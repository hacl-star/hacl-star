module Hacl.Spec.Bignum.AlmostMontExponentiation

open FStar.Mul

open Lib.IntTypes
open Lib.Sequence

open Hacl.Spec.Bignum.Definitions

module LE = Lib.Exponentiation
module SE = Spec.Exponentiation

module E = Hacl.Spec.Exponentiation.Lemmas
module M = Hacl.Spec.Montgomery.Lemmas
module AM = Hacl.Spec.AlmostMontgomery.Lemmas

module BN = Hacl.Spec.Bignum
module BM = Hacl.Spec.Bignum.Montgomery
module BA = Hacl.Spec.Bignum.AlmostMontgomery
module ME = Hacl.Spec.Bignum.MontExponentiation

#reset-options "--z3rlimit 50 --fuel 0 --ifuel 0"

let amm_refl
  (#t:limb_t) (#len:BN.bn_len t)
  (n:lbignum t len{0 < bn_v n})
  (x:lbignum t len) : Lib.NatMod.nat_mod (bn_v n)
 =
  bn_v x % bn_v n

let mk_to_nat_mont_ll_comm_monoid
  (#t:limb_t)
  (#len:BN.bn_len t)
  (n:lbignum t len)
  (mu:limb t{BM.bn_mont_pre n mu})
  : SE.to_comm_monoid (lbignum t len) =
{
  SE.a_spec = Lib.NatMod.nat_mod (bn_v n);
  SE.comm_monoid = E.mk_nat_mont_ll_comm_monoid (bits t) len (bn_v n) (v mu);
  SE.refl = amm_refl n;
 }


val bn_almost_mont_one:
    #t:limb_t
  -> #len:BN.bn_len t
  -> n:lbignum t len
  -> mu:limb t{BM.bn_mont_pre n mu} ->
  SE.one_st (lbignum t len) (mk_to_nat_mont_ll_comm_monoid n mu)

let bn_almost_mont_one #t #len n mu _ =
  let one = ME.bn_mont_one n mu () in
  assert (bn_v one == E.mont_one_ll (bits t) len (bn_v n) (v mu));
  Math.Lemmas.small_mod (bn_v one) (bn_v n);
  assert (amm_refl n one == E.mont_one_ll (bits t) len (bn_v n) (v mu));
  one


val bn_almost_mont_mul:
    #t:limb_t
  -> #len:BN.bn_len t
  -> n:lbignum t len
  -> mu:limb t{BM.bn_mont_pre n mu} ->
  SE.mul_st (lbignum t len) (mk_to_nat_mont_ll_comm_monoid n mu)

let bn_almost_mont_mul #t #len n mu aM bM =
  let c = BA.bn_almost_mont_mul n mu aM bM in
  BA.bn_almost_mont_mul_lemma n mu aM bM;
  bn_eval_bound aM len;
  bn_eval_bound bM len;
  AM.almost_mont_mul_is_mont_mul_lemma (bits t) len (bn_v n) (v mu) (bn_v aM) (bn_v bM);
  c


val bn_almost_mont_sqr:
    #t:limb_t
  -> #len:BN.bn_len t
  -> n:lbignum t len
  -> mu:limb t{BM.bn_mont_pre n mu} ->
  SE.sqr_st (lbignum t len) (mk_to_nat_mont_ll_comm_monoid n mu)

let bn_almost_mont_sqr #t #len n mu aM =
  let c = BA.bn_almost_mont_sqr n mu aM in
  BA.bn_almost_mont_sqr_lemma n mu aM;
  bn_eval_bound aM len;
  AM.almost_mont_mul_is_mont_mul_lemma (bits t) len (bn_v n) (v mu) (bn_v aM) (bn_v aM);
  c


let mk_bn_almost_mont_concrete_ops
  (#t:limb_t)
  (#len:BN.bn_len t)
  (n:lbignum t len)
  (mu:limb t{BM.bn_mont_pre n mu})
  : SE.concrete_ops (lbignum t len) =
{
  SE.to = mk_to_nat_mont_ll_comm_monoid n mu;
  SE.one = bn_almost_mont_one #t #len n mu;
  SE.mul = bn_almost_mont_mul #t #len n mu;
  SE.sqr = bn_almost_mont_sqr #t #len n mu;
}

///////////////////////////////////////////////////////////////////////////////

noextract
let bn_exp_almost_mont_st (t:limb_t) (len:BN.bn_len t) =
    n:lbignum t len
  -> mu:limb t{BM.bn_mont_pre n mu}
  -> aM:ME.bn_mont_t n
  -> bBits:size_pos
  -> b:lbignum t (blocks bBits (bits t)){bn_v b < pow2 bBits} ->
  Pure (lbignum t len)
  (requires True)
  (ensures  fun resM ->
    let k = E.mk_nat_mont_ll_comm_monoid (bits t) len (bn_v n) (v mu) in
    bn_v resM % bn_v n == LE.pow k (bn_v aM) (bn_v b))


// no diff between vartime and consttime at the spec level
val bn_exp_almost_mont_bm_vartime: #t:limb_t -> #len:BN.bn_len t -> bn_exp_almost_mont_st t len
let bn_exp_almost_mont_bm_vartime #t #len n mu aM bBits b =
  let k1 = mk_bn_almost_mont_concrete_ops n mu in
  let k = k1.SE.to.SE.comm_monoid in

  let resM = SE.exp_rl k1 aM bBits (bn_v b) in
  //assert (bn_v resM % bn_v n == LE.exp_rl k (bn_v aM % bn_v n) bBits (bn_v b));
  LE.exp_rl_lemma k (bn_v aM % bn_v n) bBits (bn_v b);
  //assert (bn_v resM % bn_v n == LE.pow k (bn_v aM % bn_v n) (bn_v b));
  E.pow_nat_mont_ll_mod_base (bits t) len (bn_v n) (v mu) (bn_v aM) (bn_v b);
  resM


val bn_exp_almost_mont_bm_consttime: #t:limb_t -> #len:BN.bn_len t -> bn_exp_almost_mont_st t len
let bn_exp_almost_mont_bm_consttime #t #len n mu aM bBits b =
  let k1 = mk_bn_almost_mont_concrete_ops n mu in
  let k = k1.SE.to.SE.comm_monoid in

  LE.exp_mont_ladder_swap_lemma k (bn_v aM % bn_v n) bBits (bn_v b);
  LE.exp_mont_ladder_lemma k (bn_v aM % bn_v n) bBits (bn_v b);
  E.pow_nat_mont_ll_mod_base (bits t) len (bn_v n) (v mu) (bn_v aM) (bn_v b);
  SE.exp_mont_ladder_swap k1 aM bBits (bn_v b)


val bn_exp_almost_mont_fw:
    #t:limb_t
  -> #len:BN.bn_len t
  -> l:size_pos{l < bits t /\ pow2 l * len <= max_size_t} ->
  bn_exp_almost_mont_st t len

let bn_exp_almost_mont_fw #t #len l n mu aM bBits b =
  let k1 = mk_bn_almost_mont_concrete_ops n mu in
  LE.exp_fw_lemma k1.SE.to.SE.comm_monoid (bn_v aM % bn_v n) bBits (bn_v b) l;
  E.pow_nat_mont_ll_mod_base (bits t) len (bn_v n) (v mu) (bn_v aM) (bn_v b);
  SE.exp_fw k1 aM bBits (bn_v b) l


val bn_exp_almost_mont_vartime: #t:limb_t -> #len:BN.bn_len t -> bn_exp_almost_mont_st t len
let bn_exp_almost_mont_vartime #t #len n mu aM bBits b =
  if bBits < ME.bn_exp_mont_vartime_threshold then
    bn_exp_almost_mont_bm_vartime n mu aM bBits b
  else
    bn_exp_almost_mont_fw 4 n mu aM bBits b


val bn_exp_almost_mont_consttime: #t:limb_t -> #len:BN.bn_len t -> bn_exp_almost_mont_st t len
let bn_exp_almost_mont_consttime #t #len n mu aM bBits b =
  if bBits < ME.bn_exp_mont_consttime_threshold then
    bn_exp_almost_mont_bm_consttime n mu aM bBits b
  else
    bn_exp_almost_mont_fw 4 n mu aM bBits b
