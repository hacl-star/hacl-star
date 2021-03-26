module Hacl.Bignum.ModReduction

open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Mul

open Lib.IntTypes
open Lib.Buffer

open Hacl.Bignum.Definitions

module ST = FStar.HyperStack.ST

module S = Hacl.Spec.Bignum.ModReduction
module BN = Hacl.Bignum
//module BM = Hacl.Bignum.Montgomery
module AM = Hacl.Bignum.AlmostMontgomery
module BI = Hacl.Bignum.ModInvLimb

#reset-options "--z3rlimit 50 --fuel 0 --ifuel 0"

inline_for_extraction noextract
let bn_mod_slow_precompr2_st (t:limb_t) (len:BN.meta_len t) =
     n:lbignum t len
  -> mu:limb t
  -> r2:lbignum t len
  -> a:lbignum t (len +! len)
  -> res:lbignum t len ->
  Stack unit
  (requires fun h ->
    live h n /\ live h a /\ live h r2 /\ live h res /\
    disjoint res n /\ disjoint res a /\ disjoint res r2 /\ disjoint r2 n)
  (ensures  fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    as_seq h1 res == S.bn_mod_slow_precompr2 (as_seq h0 n) mu (as_seq h0 r2) (as_seq h0 a))


inline_for_extraction noextract
val bn_mod_slow_precompr2:
    #t:limb_t
  -> k:AM.almost_mont t ->
  bn_mod_slow_precompr2_st t k.AM.bn.BN.len

let bn_mod_slow_precompr2 #t k n mu r2 a res =
  [@inline_let] let len = k.AM.bn.BN.len in
  push_frame ();
  let a_mod = create len (uint #t #SEC 0) in
  let a1 = create (len +! len) (uint #t #SEC 0) in
  copy a1 a;
  AM.bn_almost_mont_reduction k.AM.bn n mu a1 a_mod;
  AM.to n mu r2 a_mod res;
  pop_frame ()


inline_for_extraction noextract
let bn_mod_slow_st (t:limb_t) (len:BN.meta_len t) =
    nBits:size_t{v nBits / bits t < v len}
  -> n:lbignum t len
  -> a:lbignum t (len +! len)
  -> res:lbignum t len ->
  Stack unit
  (requires fun h ->
    live h n /\ live h a /\ live h res /\
    disjoint res n /\ disjoint res a)
  (ensures  fun h0 r h1 -> modifies (loc res) h0 h1 /\
    as_seq h1 res == S.bn_mod_slow (v nBits) (as_seq h0 n) (as_seq h0 a))


inline_for_extraction noextract
val mk_bn_mod_slow:
    #t:limb_t
  -> k:AM.almost_mont t
  -> bn_mod_slow_precompr2:bn_mod_slow_precompr2_st t k.AM.bn.BN.len ->
  bn_mod_slow_st t k.AM.bn.BN.len

let mk_bn_mod_slow #t k bn_mod_slow_precompr2 nBits n a res =
  [@inline_let] let len = k.AM.bn.BN.len in
  push_frame ();
  let mu = BI.mod_inv_limb n.(0ul) in
  let r2 = create len (uint #t #SEC 0) in
  AM.precomp nBits n r2;
  bn_mod_slow_precompr2 n mu r2 a res;
  pop_frame ()
