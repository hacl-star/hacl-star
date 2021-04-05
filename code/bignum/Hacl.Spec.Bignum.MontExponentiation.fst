module Hacl.Spec.Bignum.MontExponentiation

open FStar.Mul

open Lib.IntTypes
open Lib.Sequence

open Hacl.Spec.Bignum.Definitions

module LE = Lib.Exponentiation
module SE = Spec.Exponentiation

module E = Hacl.Spec.Exponentiation.Lemmas
module M = Hacl.Spec.Montgomery.Lemmas

module BN = Hacl.Spec.Bignum
module BM = Hacl.Spec.Bignum.Montgomery

#reset-options "--z3rlimit 50 --fuel 0 --ifuel 0"

// All operations are performed in the Montgomery domain!

unfold
let bn_mont_t (#t:limb_t) (#len:BN.bn_len t) (n:lbignum t len) =
  x:lbignum t len{bn_v x < bn_v n}

let mk_to_nat_mont_ll_comm_monoid
  (#t:limb_t)
  (#len:BN.bn_len t)
  (n:lbignum t len)
  (mu:limb t{BM.bn_mont_pre n mu})
  : SE.to_comm_monoid (bn_mont_t n) =
{
  SE.a_spec = Lib.NatMod.nat_mod (bn_v n);
  SE.comm_monoid = E.mk_nat_mont_ll_comm_monoid (bits t) len (bn_v n) (v mu);
  SE.refl = (fun (x:bn_mont_t n) -> bn_v x);
 }


val bn_mont_one:
    #t:limb_t
  -> #len:BN.bn_len t
  -> n:lbignum t len
  -> mu:limb t{BM.bn_mont_pre n mu} ->
  SE.one_st (bn_mont_t n) (mk_to_nat_mont_ll_comm_monoid n mu)

let bn_mont_one #t #len n mu _ =
  BM.bn_precomp_r2_mod_n_lemma 0 n;
  let r2 = BM.bn_precomp_r2_mod_n 0 n in
  BM.bn_mont_one_lemma n mu r2;
  BM.bn_mont_one n mu r2


val bn_mont_mul:
    #t:limb_t
  -> #len:BN.bn_len t
  -> n:lbignum t len
  -> mu:limb t{BM.bn_mont_pre n mu} ->
  SE.mul_st (bn_mont_t n) (mk_to_nat_mont_ll_comm_monoid n mu)

let bn_mont_mul #t #len n mu aM bM =
  BM.bn_mont_mul_lemma n mu aM bM;
  BM.bn_mont_mul n mu aM bM


val bn_mont_sqr:
    #t:limb_t
  -> #len:BN.bn_len t
  -> n:lbignum t len
  -> mu:limb t{BM.bn_mont_pre n mu} ->
  SE.sqr_st (bn_mont_t n) (mk_to_nat_mont_ll_comm_monoid n mu)

let bn_mont_sqr #t #len n mu aM =
  BM.bn_mont_sqr_lemma n mu aM;
  BM.bn_mont_sqr n mu aM


let mk_bn_mont_concrete_ops
  (#t:limb_t)
  (#len:BN.bn_len t)
  (n:lbignum t len)
  (mu:limb t{BM.bn_mont_pre n mu})
  : SE.concrete_ops (bn_mont_t n) =
{
  SE.to = mk_to_nat_mont_ll_comm_monoid n mu;
  SE.one = bn_mont_one #t #len n mu;
  SE.mul = bn_mont_mul #t #len n mu;
  SE.sqr = bn_mont_sqr #t #len n mu;
}

///////////////////////////////////////////////////////////////////////////////

//TODO: set _threshold properly and
//add `bn_get_window_size` (consttime and vartime)
inline_for_extraction noextract
let bn_exp_mont_vartime_threshold = 200

inline_for_extraction noextract
let bn_exp_mont_consttime_threshold = 200


noextract
let bn_exp_mont_st (t:limb_t) (len:BN.bn_len t) =
    n:lbignum t len
  -> mu:limb t{BM.bn_mont_pre n mu}
  -> aM:bn_mont_t n
  -> bBits:size_pos
  -> b:lbignum t (blocks bBits (bits t)){bn_v b < pow2 bBits} ->
  Pure (bn_mont_t n)
  (requires True)
  (ensures  fun resM ->
    let k = E.mk_nat_mont_ll_comm_monoid (bits t) len (bn_v n) (v mu) in
    bn_v resM == LE.pow k (bn_v aM) (bn_v b))


// no diff between vartime and consttime at the spec level
val bn_exp_mont_bm_vartime: #t:limb_t -> #len:BN.bn_len t -> bn_exp_mont_st t len
let bn_exp_mont_bm_vartime #t #len n mu aM bBits b =
  let k1 = mk_bn_mont_concrete_ops n mu in
  LE.exp_rl_lemma k1.SE.to.SE.comm_monoid (bn_v aM) bBits (bn_v b);
  SE.exp_rl k1 aM bBits (bn_v b)


val bn_exp_mont_bm_consttime: #t:limb_t -> #len:BN.bn_len t -> bn_exp_mont_st t len
let bn_exp_mont_bm_consttime #t #len n mu aM bBits b =
  let k1 = mk_bn_mont_concrete_ops n mu in
  LE.exp_mont_ladder_swap_lemma k1.SE.to.SE.comm_monoid (bn_v aM) bBits (bn_v b);
  LE.exp_mont_ladder_lemma k1.SE.to.SE.comm_monoid (bn_v aM) bBits (bn_v b);
  SE.exp_mont_ladder_swap k1 aM bBits (bn_v b)


val bn_exp_mont_fw:
    #t:limb_t
  -> #len:BN.bn_len t
  -> l:size_pos{l < bits t /\ pow2 l * len <= max_size_t} ->
  bn_exp_mont_st t len

let bn_exp_mont_fw #t #len l n mu aM bBits b =
  let k1 = mk_bn_mont_concrete_ops n mu in
  LE.exp_fw_lemma k1.SE.to.SE.comm_monoid (bn_v aM) bBits (bn_v b) l;
  SE.exp_fw k1 aM bBits (bn_v b) l


val bn_exp_mont_vartime: #t:limb_t -> #len:BN.bn_len t -> bn_exp_mont_st t len
let bn_exp_mont_vartime #t #len n mu aM bBits b =
  if bBits < bn_exp_mont_vartime_threshold then
    bn_exp_mont_bm_vartime n mu aM bBits b
  else
    bn_exp_mont_fw 4 n mu aM bBits b


val bn_exp_mont_consttime: #t:limb_t -> #len:BN.bn_len t -> bn_exp_mont_st t len
let bn_exp_mont_consttime #t #len n mu aM bBits b =
  if bBits < bn_exp_mont_consttime_threshold then
    bn_exp_mont_bm_consttime n mu aM bBits b
  else
    bn_exp_mont_fw 4 n mu aM bBits b
