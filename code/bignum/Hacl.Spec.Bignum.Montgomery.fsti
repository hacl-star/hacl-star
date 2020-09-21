module Hacl.Spec.Bignum.Montgomery

open FStar.Mul

open Lib.IntTypes
open Lib.Sequence

open Hacl.Spec.Bignum.Definitions
module M = Hacl.Spec.Montgomery.Lemmas

#reset-options "--z3rlimit 50 --fuel 0 --ifuel 0"

///
///  check a modulus for Montgomery arithmetic
///

val check_modulus: #t:limb_t -> #nLen:size_pos{2 * bits t * nLen <= max_size_t} -> n:lbignum t nLen ->
  res:limb t{v res == (if (bn_v n % 2 = 1 && 1 < bn_v n) then v (ones t SEC) else v (zeros t SEC))}

///
///  Precomputed constants for Montgomery arithmetic
///

val precomp_r2_mod_n: #t:limb_t -> #nLen:size_pos{2 * bits t * nLen <= max_size_t} -> n:lbignum t nLen -> lbignum t nLen

val precomp_r2_mod_n_lemma: #t:limb_t -> #nLen:size_pos -> n:lbignum t nLen -> Lemma
  (requires 1 < bn_v n /\ bn_v n % 2 = 1 /\ 2 * bits t * nLen <= max_size_t)
  (ensures  bn_v (precomp_r2_mod_n n) == pow2 (2 * bits t * nLen) % bn_v n)

///
///  Conversion functions to/from the Montgomery domen and the Montgomery reduction
///

val mont_reduction:
    #t:limb_t
  -> #nLen:size_pos{nLen + nLen <= max_size_t}
  -> n:lbignum t nLen
  -> mu:limb t
  -> c:lbignum t (nLen + nLen) ->
  lbignum t nLen


val to_mont:
    #t:limb_t
  -> #nLen:size_pos{nLen + nLen <= max_size_t}
  -> n:lbignum t nLen
  -> mu:limb t
  -> r2:lbignum t nLen
  -> a:lbignum t nLen ->
  lbignum t nLen


val from_mont:
    #t:limb_t
  -> #nLen:size_pos{nLen + nLen <= max_size_t}
  -> n:lbignum t nLen
  -> mu:limb t
  -> aM:lbignum t nLen ->
  lbignum t nLen


val mont_mul:
    #t:limb_t
  -> #nLen:size_pos{nLen + nLen <= max_size_t}
  -> n:lbignum t nLen
  -> mu:limb t
  -> aM:lbignum t nLen
  -> bM:lbignum t nLen ->
  lbignum t nLen


val mont_sqr:
    #t:limb_t
  -> #nLen:size_pos{nLen + nLen <= max_size_t}
  -> n:lbignum t nLen
  -> mu:limb t
  -> aM:lbignum t nLen ->
  lbignum t nLen

///
///  Lemmas
///

val mont_reduction_lemma:
    #t:limb_t
  -> #nLen:size_pos{nLen + nLen <= max_size_t}
  -> n:lbignum t nLen
  -> mu:limb t
  -> c:lbignum t (nLen + nLen) -> Lemma
  (requires
    (1 + (bn_v n % pow2 (bits t)) * v mu) % pow2 (bits t) == 0 /\
    bn_v n % 2 = 1 /\ 1 < bn_v n /\
    bn_v c < bn_v n * bn_v n)
  (ensures
    (let res = bn_v (mont_reduction n mu c) in
    res == M.mont_reduction (bits t) nLen (bn_v n) (v mu) (bn_v c) /\
    res < bn_v n))


val to_mont_lemma:
    #t:limb_t
  -> #nLen:size_pos{nLen + nLen <= max_size_t}
  -> n:lbignum t nLen
  -> mu:limb t
  -> r2:lbignum t nLen
  -> a:lbignum t nLen -> Lemma
  (requires
    (1 + (bn_v n % pow2 (bits t)) * v mu) % pow2 (bits t) == 0 /\
    bn_v n % 2 = 1 /\ 1 < bn_v n /\
    bn_v a < bn_v n /\ bn_v r2 == pow2 (2 * bits t * nLen) % bn_v n)
  (ensures
   (let aM = bn_v (to_mont n mu r2 a) in
    aM == M.to_mont (bits t) nLen (bn_v n) (v mu) (bn_v a) /\
    aM < bn_v n))


val from_mont_lemma:
    #t:limb_t
  -> #nLen:size_pos{nLen + nLen <= max_size_t}
  -> n:lbignum t nLen
  -> mu:limb t
  -> aM:lbignum t nLen -> Lemma
  (requires
    (1 + (bn_v n % pow2 (bits t)) * v mu) % pow2 (bits t) == 0 /\
    bn_v n % 2 = 1 /\ 1 < bn_v n /\
    bn_v aM < bn_v n)
  (ensures
   (let a = bn_v (from_mont n mu aM) in
    a == M.from_mont (bits t) nLen (bn_v n) (v mu) (bn_v aM) /\
    a < bn_v n))


val mont_mul_lemma:
    #t:limb_t
  -> #nLen:size_pos{nLen + nLen <= max_size_t}
  -> n:lbignum t nLen
  -> mu:limb t
  -> aM:lbignum t nLen
  -> bM:lbignum t nLen -> Lemma
  (requires
    (1 + (bn_v n % pow2 (bits t)) * v mu) % pow2 (bits t) == 0 /\
    bn_v n % 2 = 1 /\ 1 < bn_v n /\
    bn_v aM < bn_v n /\ bn_v bM < bn_v n)
  (ensures
    (let res = bn_v (mont_mul n mu aM bM) in
    res == M.mont_mul (bits t) nLen (bn_v n) (v mu) (bn_v aM) (bn_v bM) /\
    res < bn_v n))


val mont_sqr_lemma:
    #t:limb_t
  -> #nLen:size_pos{nLen + nLen <= max_size_t}
  -> n:lbignum t nLen
  -> mu:limb t
  -> aM:lbignum t nLen -> Lemma
  (requires
    (1 + (bn_v n % pow2 (bits t)) * v mu) % pow2 (bits t) == 0 /\
    bn_v n % 2 = 1 /\ 1 < bn_v n /\
    bn_v aM < bn_v n)
  (ensures
    (let res = bn_v (mont_sqr n mu aM) in
    res == M.mont_mul (bits t) nLen (bn_v n) (v mu) (bn_v aM) (bn_v aM) /\
    res < bn_v n))
