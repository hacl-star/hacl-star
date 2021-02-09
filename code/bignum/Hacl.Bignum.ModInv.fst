module Hacl.Bignum.ModInv

open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Mul

open Lib.IntTypes
open Lib.Buffer

open Hacl.Bignum.Definitions

module ST = FStar.HyperStack.ST
module S = Hacl.Spec.Bignum.ModInv

module BN = Hacl.Bignum
module BE = Hacl.Bignum.Exponentiation
module BM = Hacl.Bignum.Montgomery
module SN = Hacl.Spec.Bignum
module SD = Hacl.Spec.Bignum.Definitions

#reset-options "--z3rlimit 50 --fuel 0 --ifuel 0"

inline_for_extraction noextract
let bn_check_bn_mod_inv_prime_st (t:limb_t) (len:BN.meta_len t) =
    n:lbignum t len
  -> a:lbignum t len ->
  Stack (limb t)
  (requires fun h -> live h n /\ live h a /\ disjoint n a)
  (ensures  fun h0 r h1 -> modifies0 h0 h1 /\
    r == S.bn_check_bn_mod_inv_prime (as_seq h0 n) (as_seq h0 a))


inline_for_extraction noextract
val bn_check_bn_mod_inv_prime: #t:limb_t -> k:BE.exp t -> bn_check_bn_mod_inv_prime_st t k.BE.mont.BM.bn.BN.len
let bn_check_bn_mod_inv_prime #t k n a =
  [@inline_let] let len = k.BE.mont.BM.bn.BN.len in
  let m0 = k.BE.mont.BM.mont_check n in
  let m1 = BN.bn_is_zero_mask len a in
  let m2 = BN.bn_lt_mask len a n in
  m0 &. (lognot m1) &. m2


inline_for_extraction noextract
let bn_mod_inv_prime_st (t:limb_t) (len:BN.meta_len t) =
    nBits:size_t{v nBits / bits t < v len}
  -> n:lbignum t len
  -> a:lbignum t len
  -> res:lbignum t len ->
  Stack unit
  (requires fun h ->
    live h n /\ live h a /\ live h res /\
    disjoint res n /\ disjoint res a /\ disjoint n a /\
    S.bn_mod_inv_prime_pre (v nBits) (as_seq h n) (as_seq h a))
  (ensures  fun h0 r h1 -> modifies (loc res) h0 h1 /\
    as_seq h1 res == S.bn_mod_inv_prime (v nBits) (as_seq h0 n) (as_seq h0 a))


inline_for_extraction noextract
val bn_mod_inv_prime_raw: #t:limb_t -> k:BE.exp t -> bn_mod_inv_prime_st t k.BE.mont.BM.bn.BN.len
let bn_mod_inv_prime_raw #t k nBits n a res =
  [@inline_let] let len = k.BE.mont.BM.bn.BN.len in
  push_frame ();
  let n2 = create len (uint #t #SEC 0) in
  let c = BN.bn_sub1 len n (uint #t #SEC 2) n2 in
  let h0 = ST.get () in
  SN.bn_sub1_lemma (as_seq h0 n) (uint #t #SEC 2);
  SD.bn_eval_bound (as_seq h0 n2) (v len);
  SD.bn_eval_bound (as_seq h0 n) (v len);
  
  BE.bn_mod_exp_raw k.BE.mont k.BE.raw_mod_exp_precomp nBits n a (size (bits t) *! len) n2 res;
  pop_frame ()
