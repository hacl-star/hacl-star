module Hacl.Spec.Bignum.GenericField

open FStar.Mul

open Lib.IntTypes
open Lib.Sequence

open Hacl.Spec.Bignum.Definitions
module Euclid = FStar.Math.Euclid
module M = Hacl.Spec.Montgomery.Lemmas
module BE = Hacl.Spec.Bignum.Exponentiation

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

let bn_mont_ctx_pre (#t:limb_t) (nBits:size_nat) (len:BE.bn_len t) (n:lbignum t len) =
  0 < nBits /\ (nBits - 1) / bits t < len /\
  pow2 (nBits - 1) < bn_v n /\ bn_v n < pow2 nBits /\

  1 < bn_v n /\ bn_v n % 2 = 1 /\ Euclid.is_prime (bn_v n)


inline_for_extraction
class bn_mont_ctx (t:limb_t) = {
  nBits: size_nat;
  len: BE.bn_len t;
  n: lbignum t len;
  mu: limb t;
  r2: lbignum t len
  }

let bn_mont_ctx_inv (#t:limb_t) (k:bn_mont_ctx t) =
  bn_mont_ctx_pre k.nBits k.len k.n /\
  (1 + (bn_v k.n % pow2 (bits t)) * v k.mu) % pow2 (bits t) == 0 /\
  bn_v k.r2 == pow2 (2 * bits t * k.len) % bn_v k.n


val bn_field_get_len: #t:limb_t -> k:bn_mont_ctx t{bn_mont_ctx_inv k} -> BE.bn_len t


// computes the Montgomery constants r2 and mu
val bn_field_init: #t:limb_t -> #len:BE.bn_len t -> nBits:size_nat -> n:lbignum t len ->
  Pure (bn_mont_ctx t)
  (requires bn_mont_ctx_pre nBits len n)
  (ensures  fun k -> bn_mont_ctx_inv k)


val bn_to_field: #t:limb_t -> k:bn_mont_ctx t{bn_mont_ctx_inv k} -> a:lbignum t k.len ->
  Pure (lbignum t k.len)
  (requires bn_v a < bn_v k.n)
  (ensures  fun aM -> bn_v aM < bn_v k.n /\
    bn_v aM == M.to_mont (bits t) k.len (bn_v k.n) (v k.mu) (bn_v a))


val bn_from_field: #t:limb_t -> k:bn_mont_ctx t{bn_mont_ctx_inv k} -> aM:lbignum t k.len ->
  Pure (lbignum t k.len)
  (requires bn_v aM < bn_v k.n)
  (ensures  fun a -> bn_v a < bn_v k.n /\
    bn_v a == M.from_mont (bits t) k.len (bn_v k.n) (v k.mu) (bn_v aM))


val bn_from_to_field_lemma: #t:limb_t -> k:bn_mont_ctx t{bn_mont_ctx_inv k} -> a:lbignum t k.len -> Lemma
  (requires bn_v a < bn_v k.n)
  (ensures  bn_v (bn_from_field k (bn_to_field k a)) == bn_v a)


val bn_field_add: #t:limb_t -> k:bn_mont_ctx t{bn_mont_ctx_inv k} -> aM:lbignum t k.len -> bM:lbignum t k.len ->
  Pure (lbignum t k.len)
  (requires bn_v aM < bn_v k.n /\ bn_v bM < bn_v k.n)
  (ensures  fun cM -> bn_v cM < bn_v k.n /\
    bn_v (bn_from_field k cM) == (bn_v (bn_from_field k aM) + bn_v (bn_from_field k bM)) % bn_v k.n)


val bn_field_sub: #t:limb_t -> k:bn_mont_ctx t{bn_mont_ctx_inv k} -> aM:lbignum t k.len -> bM:lbignum t k.len ->
  Pure (lbignum t k.len)
  (requires bn_v aM < bn_v k.n /\ bn_v bM < bn_v k.n)
  (ensures  fun cM -> bn_v cM < bn_v k.n /\
    bn_v (bn_from_field k cM) == (bn_v (bn_from_field k aM) - bn_v (bn_from_field k bM)) % bn_v k.n)


val bn_field_mul: #t:limb_t -> k:bn_mont_ctx t{bn_mont_ctx_inv k} -> aM:lbignum t k.len -> bM:lbignum t k.len ->
  Pure (lbignum t k.len)
  (requires bn_v aM < bn_v k.n /\ bn_v bM < bn_v k.n)
  (ensures  fun cM -> bn_v cM < bn_v k.n /\
    bn_v (bn_from_field k cM) == bn_v (bn_from_field k aM) * bn_v (bn_from_field k bM) % bn_v k.n)


val bn_field_sqr: #t:limb_t -> k:bn_mont_ctx t{bn_mont_ctx_inv k} -> aM:lbignum t k.len ->
  Pure (lbignum t k.len)
  (requires bn_v aM < bn_v k.n)
  (ensures  fun cM -> bn_v cM < bn_v k.n /\
    bn_v (bn_from_field k cM) == bn_v (bn_from_field k aM) * bn_v (bn_from_field k aM) % bn_v k.n)


val bn_field_one: #t:limb_t -> k:bn_mont_ctx t{bn_mont_ctx_inv k} ->
  Pure (lbignum t k.len)
  (requires True)
  (ensures  fun oneM -> bn_v oneM < bn_v k.n /\
    bn_v (bn_from_field k oneM) == 1)


val bn_field_inv: #t:limb_t -> k:bn_mont_ctx t{bn_mont_ctx_inv k} -> aM:lbignum t k.len ->
  Pure (lbignum t k.len)
  (requires 0 < bn_v aM /\ bn_v aM < bn_v k.n)
  (ensures  fun aInvM -> bn_v aInvM < bn_v k.n /\
    bn_v (bn_from_field k aInvM) * bn_v (bn_from_field k aM) % bn_v k.n == 1)
