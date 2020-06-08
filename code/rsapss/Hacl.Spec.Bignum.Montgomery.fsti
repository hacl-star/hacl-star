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
val mod_inv_u64: n0:uint64 -> uint64

val mod_inv_u64_lemma: n0:uint64 -> Lemma
  (requires v n0 % 2 == 1)
  (ensures (1 + v n0 * v (mod_inv_u64 n0)) % pow2 64 == 0)

val precomp_r2_mod_n:
    #nLen:size_pos{128 * (nLen + 1) <= max_size_t}
  -> modBits:size_pos{nLen == blocks modBits 64}
  -> n:lbignum nLen ->
  lbignum nLen

val precomp_r2_mod_n_lemma: #nLen:size_pos -> modBits:size_pos -> n:lbignum nLen -> Lemma
  (requires
    0 < bn_v n /\ pow2 (modBits - 1) < bn_v n /\
    128 * (nLen + 1) <= max_size_t /\ nLen == blocks modBits 64)
  (ensures  bn_v (precomp_r2_mod_n modBits n) == pow2 (128 * (nLen + 1)) % bn_v n)

///
///  Conversion functions to/from the Montgomery domen and the Montgomery reduction
///

val mont_reduction:
    #nLen:size_nat
  -> #rLen:size_nat{rLen = nLen + 1 /\ rLen + rLen <= max_size_t}
  -> n:lbignum nLen
  -> mu:uint64
  -> c:lbignum (rLen + rLen) ->
  lbignum rLen


val to_mont:
    #nLen:size_nat
  -> #rLen:size_nat{rLen = nLen + 1 /\ rLen + rLen <= max_size_t}
  -> n:lbignum nLen
  -> mu:uint64
  -> r2:lbignum nLen
  -> a:lbignum nLen ->
  lbignum rLen


val from_mont:
    #nLen:size_nat
  -> #rLen:size_nat{rLen = nLen + 1 /\ rLen + rLen <= max_size_t}
  -> n:lbignum nLen
  -> mu:uint64
  -> aM:lbignum rLen ->
  lbignum nLen


val mont_mul:
    #nLen:size_nat
  -> #rLen:size_nat{rLen = nLen + 1 /\ rLen + rLen <= max_size_t}
  -> n:lbignum nLen
  -> mu:uint64
  -> aM:lbignum rLen
  -> bM:lbignum rLen ->
  lbignum rLen


///
///  Lemmas
///

val mont_reduction_lemma:
    #nLen:size_nat
  -> #rLen:size_nat{rLen = nLen + 1 /\ rLen + rLen <= max_size_t}
  -> n:lbignum nLen
  -> mu:uint64
  -> c:lbignum (rLen + rLen) -> Lemma
  (requires
    (1 + (bn_v n % pow2 64) * v mu) % pow2 64 == 0 /\
    bn_v n % 2 = 1 /\ 1 < bn_v n /\ bn_v n < pow2 (64 * nLen) /\
    bn_v c < 4 * bn_v n * bn_v n)
  (ensures
    (let res = bn_v (mont_reduction #nLen #rLen n mu c) in
    res == M.mont_reduction rLen (bn_v n) (v mu) (bn_v c) /\
    res < 2 * bn_v n))


val to_mont_lemma:
    #nLen:size_nat
  -> #rLen:size_nat{rLen = nLen + 1 /\ rLen + rLen <= max_size_t}
  -> n:lbignum nLen
  -> mu:uint64
  -> r2:lbignum nLen
  -> a:lbignum nLen -> Lemma
  (requires
    (1 + (bn_v n % pow2 64) * v mu) % pow2 64 == 0 /\
    bn_v n % 2 = 1 /\ 1 < bn_v n /\ bn_v n < pow2 (64 * nLen) /\
    bn_v a < bn_v n /\ bn_v r2 == pow2 (128 * rLen) % bn_v n)
  (ensures
   (let aM = bn_v (to_mont #nLen #rLen n mu r2 a) in
    aM == M.to_mont rLen (bn_v n) (v mu) (bn_v a) /\
    aM < 2 * bn_v n))


val from_mont_lemma:
    #nLen:size_nat
  -> #rLen:size_nat{rLen = nLen + 1 /\ rLen + rLen <= max_size_t}
  -> n:lbignum nLen
  -> mu:uint64
  -> aM:lbignum rLen -> Lemma
  (requires
    (1 + (bn_v n % pow2 64) * v mu) % pow2 64 == 0 /\
    bn_v n % 2 = 1 /\ 1 < bn_v n /\ bn_v n < pow2 (64 * nLen) /\
    bn_v aM < 2 * bn_v n)
  (ensures
   (let a = bn_v (from_mont #nLen #rLen n mu aM) in
    a == M.from_mont rLen (bn_v n) (v mu) (bn_v aM) /\
    a <= bn_v n))


val mont_mul_lemma:
    #nLen:size_nat
  -> #rLen:size_nat{rLen = nLen + 1 /\ rLen + rLen <= max_size_t}
  -> n:lbignum nLen
  -> mu:uint64
  -> aM:lbignum rLen
  -> bM:lbignum rLen -> Lemma
  (requires
    (1 + (bn_v n % pow2 64) * v mu) % pow2 64 == 0 /\
    bn_v n % 2 = 1 /\ 1 < bn_v n /\ bn_v n < pow2 (64 * nLen) /\
    bn_v aM < 2 * bn_v n /\ bn_v bM < 2 * bn_v n)
  (ensures
    (let res = bn_v (mont_mul #nLen #rLen n mu aM bM) in
    res == M.mont_mul rLen (bn_v n) (v mu) (bn_v aM) (bn_v bM) /\
    res < 2 * bn_v n))
