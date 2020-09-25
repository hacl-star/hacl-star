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

#reset-options "--z3rlimit 50 --fuel 0 --ifuel 0"

inline_for_extraction noextract
let bn_mod_inv_prime_st (t:limb_t) (nLen:BN.meta_len t) =
    n:lbignum t nLen
  -> a:lbignum t nLen
  -> res:lbignum t nLen ->
  Stack bool
  (requires fun h ->
    live h n /\ live h a /\ live h res /\
    disjoint res n /\ disjoint res a /\ disjoint n a)
  (ensures  fun h0 r h1 -> modifies (loc res) h0 h1 /\
    (r ==> as_seq h1 res == S.bn_mod_inv_prime (as_seq h0 n) (as_seq h0 a)))


inline_for_extraction noextract
val mk_bn_mod_inv_prime:
    #t:limb_t
  -> nLen:BN.meta_len t
  -> bn_mod_exp:BE.bn_mod_exp_st t nLen
  -> bn_mod_inv_prime_st t nLen

let mk_bn_mod_inv_prime #t nLen bn_mod_exp n a res =
  push_frame ();
  let b2 = create 1ul (uint #t 2) in
  let n2 = create nLen (uint #t 0) in
  let c = BN.bn_sub nLen n 1ul b2 n2 in

  let h0 = ST.get () in
  let is_valid = bn_mod_exp n a (size (bits t) *! nLen) n2 res in
  let h1 = ST.get () in
  if is_valid then begin
    SE.bn_mod_exp_lemma (v nLen) (as_seq h0 n) (as_seq h0 a) (bits t * v nLen) (as_seq h0 n2);
    Hacl.Spec.Bignum.Definitions.bn_eval_inj (v nLen)
      (SE.bn_mod_exp (v nLen) (as_seq h0 n) (as_seq h0 a) (bits t * v nLen) (as_seq h0 n2))
      (as_seq h1 res) end;
  pop_frame ();
  is_valid


val bn_mod_inv_prime: #t:limb_t -> nLen:BN.meta_len t -> bn_mod_inv_prime_st t nLen
let bn_mod_inv_prime #t nLen =
  mk_bn_mod_inv_prime nLen (BE.bn_mod_exp nLen)
