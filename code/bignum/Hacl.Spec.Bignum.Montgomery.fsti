module Hacl.Spec.Bignum.Montgomery

open FStar.Mul

open Lib.IntTypes
open Lib.Sequence

open Hacl.Spec.Bignum.Definitions
module M = Hacl.Spec.Montgomery.Lemmas


#reset-options "--z3rlimit 50 --fuel 0 --ifuel 0"

///
///  Precomputed constants for Montgomery arithmetic
///

val precomp_r2_mod_n:
    #nLen:size_pos{128 * nLen <= max_size_t}
  -> modBits:size_pos{nLen == blocks modBits 64}
  -> n:lbignum nLen ->
  lbignum nLen

val precomp_r2_mod_n_lemma: #nLen:size_pos -> modBits:size_pos -> n:lbignum nLen -> Lemma
  (requires
    0 < bn_v n /\ pow2 (modBits - 1) < bn_v n /\
    128 * nLen <= max_size_t /\ nLen == blocks modBits 64)
  (ensures  bn_v (precomp_r2_mod_n modBits n) == pow2 (128 * nLen) % bn_v n)

///
///  Conversion functions to/from the Montgomery domen and the Montgomery reduction
///

val mont_reduction:
    #nLen:size_pos{nLen + nLen <= max_size_t}
  -> n:lbignum nLen
  -> mu:uint64
  -> c:lbignum (nLen + nLen) ->
  lbignum nLen


val to_mont:
    #nLen:size_pos{nLen + nLen <= max_size_t}
  -> n:lbignum nLen
  -> mu:uint64
  -> r2:lbignum nLen
  -> a:lbignum nLen ->
  lbignum nLen


val from_mont:
    #nLen:size_pos{nLen + nLen <= max_size_t}
  -> n:lbignum nLen
  -> mu:uint64
  -> aM:lbignum nLen ->
  lbignum nLen


val mont_mul:
    #nLen:size_pos{nLen + nLen <= max_size_t}
  -> n:lbignum nLen
  -> mu:uint64
  -> aM:lbignum nLen
  -> bM:lbignum nLen ->
  lbignum nLen


val mont_sqr:
    #nLen:size_pos{nLen + nLen <= max_size_t}
  -> n:lbignum nLen
  -> mu:uint64
  -> aM:lbignum nLen ->
  lbignum nLen

///
///  Lemmas
///

val mont_reduction_lemma:
    #nLen:size_pos{nLen + nLen <= max_size_t}
  -> n:lbignum nLen
  -> mu:uint64
  -> c:lbignum (nLen + nLen) -> Lemma
  (requires
    (1 + (bn_v n % pow2 64) * v mu) % pow2 64 == 0 /\
    bn_v n % 2 = 1 /\ 1 < bn_v n /\ bn_v n < pow2 (64 * nLen) /\
    bn_v c < bn_v n * bn_v n)
  (ensures
    (let res = bn_v (mont_reduction #nLen n mu c) in
    res == M.mont_reduction nLen (bn_v n) (v mu) (bn_v c) /\
    res < bn_v n))


val to_mont_lemma:
    #nLen:size_pos{nLen + nLen <= max_size_t}
  -> n:lbignum nLen
  -> mu:uint64
  -> r2:lbignum nLen
  -> a:lbignum nLen -> Lemma
  (requires
    (1 + (bn_v n % pow2 64) * v mu) % pow2 64 == 0 /\
    bn_v n % 2 = 1 /\ 1 < bn_v n /\ bn_v n < pow2 (64 * nLen) /\
    bn_v a < bn_v n /\ bn_v r2 == pow2 (128 * nLen) % bn_v n)
  (ensures
   (let aM = bn_v (to_mont #nLen n mu r2 a) in
    aM == M.to_mont nLen (bn_v n) (v mu) (bn_v a) /\
    aM < bn_v n))


val from_mont_lemma:
    #nLen:size_pos{nLen + nLen <= max_size_t}
  -> n:lbignum nLen
  -> mu:uint64
  -> aM:lbignum nLen -> Lemma
  (requires
    (1 + (bn_v n % pow2 64) * v mu) % pow2 64 == 0 /\
    bn_v n % 2 = 1 /\ 1 < bn_v n /\ bn_v n < pow2 (64 * nLen) /\
    bn_v aM < bn_v n)
  (ensures
   (let a = bn_v (from_mont #nLen n mu aM) in
    a == M.from_mont nLen (bn_v n) (v mu) (bn_v aM) /\
    a < bn_v n))


val mont_mul_lemma:
    #nLen:size_pos{nLen + nLen <= max_size_t}
  -> n:lbignum nLen
  -> mu:uint64
  -> aM:lbignum nLen
  -> bM:lbignum nLen -> Lemma
  (requires
    (1 + (bn_v n % pow2 64) * v mu) % pow2 64 == 0 /\
    bn_v n % 2 = 1 /\ 1 < bn_v n /\ bn_v n < pow2 (64 * nLen) /\
    bn_v aM < bn_v n /\ bn_v bM < bn_v n)
  (ensures
    (let res = bn_v (mont_mul #nLen n mu aM bM) in
    res == M.mont_mul nLen (bn_v n) (v mu) (bn_v aM) (bn_v bM) /\
    res < bn_v n))


val mont_sqr_lemma:
    #nLen:size_pos{nLen + nLen <= max_size_t}
  -> n:lbignum nLen
  -> mu:uint64
  -> aM:lbignum nLen -> Lemma
  (requires
    (1 + (bn_v n % pow2 64) * v mu) % pow2 64 == 0 /\
    bn_v n % 2 = 1 /\ 1 < bn_v n /\ bn_v n < pow2 (64 * nLen) /\
    bn_v aM < bn_v n)
  (ensures
    (let res = bn_v (mont_sqr #nLen n mu aM) in
    res == M.mont_mul nLen (bn_v n) (v mu) (bn_v aM) (bn_v aM) /\
    res < bn_v n))
