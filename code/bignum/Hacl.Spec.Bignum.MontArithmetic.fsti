module Hacl.Spec.Bignum.MontArithmetic

open FStar.Mul

open Lib.IntTypes
open Lib.Sequence

open Hacl.Spec.Bignum.Definitions

module Euclid = FStar.Math.Euclid
module M = Hacl.Spec.Montgomery.Lemmas
module BN = Hacl.Spec.Bignum

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

let bn_mont_ctx_pre (#t:limb_t) (#len:BN.bn_len t) (n:lbignum t len) =
  1 < bn_v n /\ bn_v n % 2 = 1


inline_for_extraction
class bn_mont_ctx (t:limb_t) = {
  len: BN.bn_len t;
  n: lbignum t len;
  mu: limb t;
  r2: lbignum t len
  }


let bn_mont_ctx_inv (#t:limb_t) (k:bn_mont_ctx t) =
  bn_v k.n < pow2 (bits t * k.len) /\
  bn_mont_ctx_pre k.n /\
  (1 + bn_v k.n * v k.mu) % pow2 (bits t) == 0 /\
  bn_v k.r2 == pow2 (2 * bits t * k.len) % bn_v k.n


let bn_mont_nat (#t:limb_t) (k:bn_mont_ctx t) =
  x:lbignum t k.len{bn_v x < bn_v k.n}


val bn_field_get_len: #t:limb_t -> k:bn_mont_ctx t{bn_mont_ctx_inv k} -> BN.bn_len t


val bn_field_check_modulus: #t:limb_t -> #len:BN.bn_len t -> n:lbignum t len ->
  res:bool{res <==> bn_mont_ctx_pre n}


// computes the Montgomery constants r2 and mu
val bn_field_init: #t:limb_t -> #len:BN.bn_len t -> n:lbignum t len ->
  Pure (bn_mont_ctx t)
  (requires bn_mont_ctx_pre n)
  (ensures  fun k -> bn_mont_ctx_inv k /\ k.n == n /\ k.len == len)


val bn_to_field: #t:limb_t -> k:bn_mont_ctx t{bn_mont_ctx_inv k} -> a:lbignum t k.len ->
  Pure (bn_mont_nat k)
  (requires True)
  (ensures  fun aM ->
    bn_v aM == M.to_mont (bits t) k.len (bn_v k.n) (v k.mu) (bn_v a))


val bn_from_field: #t:limb_t -> k:bn_mont_ctx t{bn_mont_ctx_inv k} -> aM:bn_mont_nat k ->
  Pure (lbignum t k.len)
  (requires True)
  (ensures  fun a -> bn_v a < bn_v k.n /\
    bn_v a == M.from_mont (bits t) k.len (bn_v k.n) (v k.mu) (bn_v aM))


val bn_from_to_field_lemma: #t:limb_t -> k:bn_mont_ctx t{bn_mont_ctx_inv k} -> a:lbignum t k.len ->
  Lemma (bn_v (bn_from_field k (bn_to_field k a)) == bn_v a % bn_v k.n)


val bn_field_add: #t:limb_t -> k:bn_mont_ctx t{bn_mont_ctx_inv k} -> aM:bn_mont_nat k -> bM:bn_mont_nat k ->
  Pure (bn_mont_nat k)
  (requires True)
  (ensures  fun cM ->
    bn_v (bn_from_field k cM) == (bn_v (bn_from_field k aM) + bn_v (bn_from_field k bM)) % bn_v k.n)


val bn_field_sub: #t:limb_t -> k:bn_mont_ctx t{bn_mont_ctx_inv k} -> aM:bn_mont_nat k -> bM:bn_mont_nat k ->
  Pure (bn_mont_nat k)
  (requires True)
  (ensures  fun cM ->
    bn_v (bn_from_field k cM) == (bn_v (bn_from_field k aM) - bn_v (bn_from_field k bM)) % bn_v k.n)


val bn_field_mul: #t:limb_t -> k:bn_mont_ctx t{bn_mont_ctx_inv k} -> aM:bn_mont_nat k -> bM:bn_mont_nat k ->
  Pure (bn_mont_nat k)
  (requires True)
  (ensures  fun cM ->
    bn_v (bn_from_field k cM) == bn_v (bn_from_field k aM) * bn_v (bn_from_field k bM) % bn_v k.n)


val bn_field_sqr: #t:limb_t -> k:bn_mont_ctx t{bn_mont_ctx_inv k} -> aM:bn_mont_nat k ->
  Pure (bn_mont_nat k)
  (requires True)
  (ensures  fun cM ->
    bn_v (bn_from_field k cM) == bn_v (bn_from_field k aM) * bn_v (bn_from_field k aM) % bn_v k.n)


val bn_field_one: #t:limb_t -> k:bn_mont_ctx t{bn_mont_ctx_inv k} ->
  Pure (bn_mont_nat k)
  (requires True)
  (ensures  fun oneM ->
    bn_v (bn_from_field k oneM) == 1)


noextract
let bn_field_exp_st (t:limb_t) (k:bn_mont_ctx t{bn_mont_ctx_inv k}) =
    aM:bn_mont_nat k
  -> bBits:size_nat
  -> b:lbignum t (blocks0 bBits (bits t)) ->
  Pure (bn_mont_nat k)
  (requires bn_v b < pow2 bBits)
  (ensures  fun cM ->
    bn_v (bn_from_field k cM) == Lib.NatMod.pow_mod #(bn_v k.n) (bn_v (bn_from_field k aM)) (bn_v b))


val bn_field_exp_consttime: #t:limb_t -> k:bn_mont_ctx t{bn_mont_ctx_inv k} -> bn_field_exp_st t k

val bn_field_exp_vartime: #t:limb_t -> k:bn_mont_ctx t{bn_mont_ctx_inv k} -> bn_field_exp_st t k


val bn_field_inv: #t:limb_t -> k:bn_mont_ctx t{bn_mont_ctx_inv k} -> aM:bn_mont_nat k ->
  Pure (bn_mont_nat k)
  (requires 0 < bn_v aM /\ Euclid.is_prime (bn_v k.n))
  (ensures  fun aInvM ->
    bn_v (bn_from_field k aInvM) * bn_v (bn_from_field k aM) % bn_v k.n == 1)
