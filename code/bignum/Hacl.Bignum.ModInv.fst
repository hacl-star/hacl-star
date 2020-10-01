module Hacl.Bignum.ModInv

open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Mul

open Lib.IntTypes
open Lib.Buffer

open Hacl.Bignum.Definitions
open Hacl.Bignum.Exponentiation

module ST = FStar.HyperStack.ST
module S = Hacl.Spec.Bignum.ModInv
module SE = Hacl.Spec.Bignum.Exponentiation

module BN = Hacl.Bignum
module BE = Hacl.Bignum.Exponentiation
module BM = Hacl.Bignum.Montgomery

#reset-options "--z3rlimit 50 --fuel 0 --ifuel 0"

inline_for_extraction noextract
let bn_mod_inv_prime_st (t:limb_t) (len:BN.meta_len t) =
    n:lbignum t len
  -> a:lbignum t len
  -> res:lbignum t len ->
  Stack unit
  (requires fun h ->
    live h n /\ live h a /\ live h res /\
    disjoint res n /\ disjoint res a /\ disjoint n a)
  (ensures  fun h0 r h1 -> modifies (loc res) h0 h1 /\
    as_seq h1 res == S.bn_mod_inv_prime (as_seq h0 n) (as_seq h0 a))


inline_for_extraction noextract
val bn_mod_inv_prime: #t:limb_t -> k:BE.exp t -> bn_mod_inv_prime_st t k.BE.mont.BM.bn.BN.len
let bn_mod_inv_prime #t k n a res =
  [@inline_let] let len = k.BE.mont.BM.bn.BN.len in
  push_frame ();
  let b2 = create 1ul (uint #t #SEC 2) in
  let n2 = create len (uint #t #SEC 0) in
  let c = BN.bn_sub len n 1ul b2 n2 in

  k.BE.mod_exp n a (size (bits t) *! len) n2 res;
  pop_frame ()
