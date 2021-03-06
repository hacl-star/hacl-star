module Hacl.Spec.Bignum.Montgomery

open FStar.Mul

open Lib.IntTypes
open Lib.Sequence

open Hacl.Spec.Bignum.Definitions
module M = Hacl.Spec.Montgomery.Lemmas

#reset-options "--z3rlimit 50 --fuel 0 --ifuel 0"

let bn_mont_pre (#t:limb_t) (#nLen:size_pos) (n:lbignum t nLen) (mu:limb t) =
  (1 + (bn_v n % pow2 (bits t)) * v mu) % pow2 (bits t) == 0 /\
  bn_v n % 2 = 1 /\ 1 < bn_v n


///  Check a modulus for Montgomery arithmetic
val bn_check_modulus: #t:limb_t -> #nLen:size_pos{2 * bits t * nLen <= max_size_t} -> n:lbignum t nLen ->
  res:limb t{v res == (if (bn_v n % 2 = 1 && 1 < bn_v n) then v (ones t SEC) else v (zeros t SEC))}


///  Precomputed constants for Montgomery arithmetic
val bn_precomp_r2_mod_n:
    #t:limb_t
  -> #nLen:size_pos{2 * bits t * nLen <= max_size_t}
  -> nBits:size_nat{nBits / bits t < nLen}
  -> n:lbignum t nLen ->
  lbignum t nLen

val bn_precomp_r2_mod_n_lemma: #t:limb_t -> #nLen:size_pos -> nBits:size_nat -> n:lbignum t nLen -> Lemma
  (requires
    1 < bn_v n /\ bn_v n % 2 = 1 /\ 2 * bits t * nLen <= max_size_t /\
    pow2 nBits < bn_v n /\ nBits / bits t < nLen)
  (ensures  bn_v (bn_precomp_r2_mod_n nBits n) == pow2 (2 * bits t * nLen) % bn_v n)


///  Conversion functions to/from the Montgomery domen and the Montgomery reduction
val bn_mont_reduction:
    #t:limb_t
  -> #nLen:size_pos{nLen + nLen <= max_size_t}
  -> n:lbignum t nLen
  -> mu:limb t
  -> c:lbignum t (nLen + nLen) ->
  lbignum t nLen


val bn_to_mont:
    #t:limb_t
  -> #nLen:size_pos{nLen + nLen <= max_size_t}
  -> n:lbignum t nLen
  -> mu:limb t
  -> r2:lbignum t nLen
  -> a:lbignum t nLen ->
  lbignum t nLen


val bn_from_mont:
    #t:limb_t
  -> #nLen:size_pos{nLen + nLen <= max_size_t}
  -> n:lbignum t nLen
  -> mu:limb t
  -> aM:lbignum t nLen ->
  lbignum t nLen


val bn_mont_mul:
    #t:limb_t
  -> #nLen:size_pos{nLen + nLen <= max_size_t}
  -> n:lbignum t nLen
  -> mu:limb t
  -> aM:lbignum t nLen
  -> bM:lbignum t nLen ->
  lbignum t nLen


val bn_mont_sqr:
    #t:limb_t
  -> #nLen:size_pos{nLen + nLen <= max_size_t}
  -> n:lbignum t nLen
  -> mu:limb t
  -> aM:lbignum t nLen ->
  lbignum t nLen


val bn_mont_one:
    #t:limb_t
  -> #nLen:size_pos{nLen + nLen <= max_size_t}
  -> n:lbignum t nLen
  -> mu:limb t
  -> r2:lbignum t nLen ->
  lbignum t nLen


val bn_mont_reduction_lemma:
    #t:limb_t
  -> #nLen:size_pos{nLen + nLen <= max_size_t}
  -> n:lbignum t nLen
  -> mu:limb t
  -> c:lbignum t (nLen + nLen) -> Lemma
  (requires
    bn_mont_pre n mu /\ bn_v c < bn_v n * bn_v n)
  (ensures
    (let res = bn_v (bn_mont_reduction n mu c) in
    res == M.mont_reduction (bits t) nLen (bn_v n) (v mu) (bn_v c) /\
    res < bn_v n))


val bn_to_mont_lemma:
    #t:limb_t
  -> #nLen:size_pos{nLen + nLen <= max_size_t}
  -> n:lbignum t nLen
  -> mu:limb t
  -> r2:lbignum t nLen
  -> a:lbignum t nLen -> Lemma
  (requires
    bn_mont_pre n mu /\ bn_v a < bn_v n /\
    bn_v r2 == pow2 (2 * bits t * nLen) % bn_v n)
  (ensures
   (let aM = bn_v (bn_to_mont n mu r2 a) in
    aM == M.to_mont (bits t) nLen (bn_v n) (v mu) (bn_v a) /\
    aM < bn_v n))


val bn_from_mont_lemma:
    #t:limb_t
  -> #nLen:size_pos{nLen + nLen <= max_size_t}
  -> n:lbignum t nLen
  -> mu:limb t
  -> aM:lbignum t nLen -> Lemma
  (requires
    bn_mont_pre n mu /\ bn_v aM < bn_v n)
  (ensures
   (let a = bn_v (bn_from_mont n mu aM) in
    a == M.from_mont (bits t) nLen (bn_v n) (v mu) (bn_v aM) /\
    a < bn_v n))


val bn_mont_mul_lemma:
    #t:limb_t
  -> #nLen:size_pos{nLen + nLen <= max_size_t}
  -> n:lbignum t nLen
  -> mu:limb t
  -> aM:lbignum t nLen
  -> bM:lbignum t nLen -> Lemma
  (requires
    bn_mont_pre n mu /\
    bn_v aM < bn_v n /\ bn_v bM < bn_v n)
  (ensures
    (let res = bn_v (bn_mont_mul n mu aM bM) in
    res == M.mont_mul (bits t) nLen (bn_v n) (v mu) (bn_v aM) (bn_v bM) /\
    res < bn_v n))


val bn_mont_sqr_lemma:
    #t:limb_t
  -> #nLen:size_pos{nLen + nLen <= max_size_t}
  -> n:lbignum t nLen
  -> mu:limb t
  -> aM:lbignum t nLen -> Lemma
  (requires
    bn_mont_pre n mu /\ bn_v aM < bn_v n)
  (ensures
    (let res = bn_v (bn_mont_sqr n mu aM) in
    res == M.mont_mul (bits t) nLen (bn_v n) (v mu) (bn_v aM) (bn_v aM) /\
    res < bn_v n))


val bn_mont_one_lemma:
    #t:limb_t
  -> #nLen:size_pos{nLen + nLen <= max_size_t}
  -> n:lbignum t nLen
  -> mu:limb t
  -> r2:lbignum t nLen -> Lemma
  (requires
    bn_mont_pre n mu /\
    bn_v r2 == pow2 (2 * bits t * nLen) % bn_v n)
  (ensures
    (let oneM = bn_v (bn_mont_one n mu r2) in
    oneM == M.mont_one (bits t) nLen (bn_v n) (v mu) /\
    oneM < bn_v n))
