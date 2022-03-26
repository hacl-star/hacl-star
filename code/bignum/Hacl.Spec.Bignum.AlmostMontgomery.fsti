module Hacl.Spec.Bignum.AlmostMontgomery

open FStar.Mul

open Lib.IntTypes
open Lib.Sequence

open Hacl.Spec.Bignum.Definitions
module AM = Hacl.Spec.AlmostMontgomery.Lemmas
module BM = Hacl.Spec.Bignum.Montgomery

#reset-options "--z3rlimit 50 --fuel 0 --ifuel 0"

///  Almost Montgomery Multiplication

val bn_almost_mont_reduction:
    #t:limb_t
  -> #nLen:size_pos{nLen + nLen <= max_size_t}
  -> n:lbignum t nLen
  -> mu:limb t
  -> c:lbignum t (nLen + nLen) ->
  lbignum t nLen


val bn_almost_mont_mul:
    #t:limb_t
  -> #nLen:size_pos{nLen + nLen <= max_size_t}
  -> n:lbignum t nLen
  -> mu:limb t
  -> aM:lbignum t nLen
  -> bM:lbignum t nLen ->
  lbignum t nLen


val bn_almost_mont_sqr:
    #t:limb_t
  -> #nLen:size_pos{nLen + nLen <= max_size_t}
  -> n:lbignum t nLen
  -> mu:limb t
  -> aM:lbignum t nLen ->
  lbignum t nLen


val bn_almost_mont_reduction_lemma:
    #t:limb_t
  -> #nLen:size_pos{nLen + nLen <= max_size_t}
  -> n:lbignum t nLen
  -> mu:limb t
  -> c:lbignum t (nLen + nLen) -> Lemma
  (requires BM.bn_mont_pre n mu)
  (ensures
    bn_v (bn_almost_mont_reduction n mu c) ==
    AM.almost_mont_reduction (bits t) nLen (bn_v n) (v mu) (bn_v c))


val bn_almost_mont_mul_lemma:
    #t:limb_t
  -> #nLen:size_pos{nLen + nLen <= max_size_t}
  -> n:lbignum t nLen
  -> mu:limb t
  -> aM:lbignum t nLen
  -> bM:lbignum t nLen -> Lemma
  (requires BM.bn_mont_pre n mu)
  (ensures
    bn_v (bn_almost_mont_mul n mu aM bM) ==
    AM.almost_mont_mul (bits t) nLen (bn_v n) (v mu) (bn_v aM) (bn_v bM))


val bn_almost_mont_sqr_lemma:
    #t:limb_t
  -> #nLen:size_pos{nLen + nLen <= max_size_t}
  -> n:lbignum t nLen
  -> mu:limb t
  -> aM:lbignum t nLen -> Lemma
  (requires BM.bn_mont_pre n mu)
  (ensures
    bn_v (bn_almost_mont_sqr n mu aM) ==
    AM.almost_mont_mul (bits t) nLen (bn_v n) (v mu) (bn_v aM) (bn_v aM))
