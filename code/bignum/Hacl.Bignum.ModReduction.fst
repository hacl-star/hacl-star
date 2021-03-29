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
module AM = Hacl.Bignum.AlmostMontgomery
module BM = Hacl.Bignum.Montgomery
module SM = Hacl.Spec.Bignum.Montgomery
module BD = Hacl.Spec.Bignum.Definitions

#reset-options "--z3rlimit 50 --fuel 0 --ifuel 0"

inline_for_extraction noextract
let bn_mod_slow_precomp_st (t:limb_t) (len:BN.meta_len t) =
     n:lbignum t len
  -> mu:limb t
  -> r2:lbignum t len
  -> a:lbignum t (len +! len)
  -> res:lbignum t len ->
  Stack unit
  (requires fun h ->
    live h n /\ live h a /\ live h r2 /\ live h res /\
    disjoint res n /\ disjoint res a /\ disjoint res r2 /\ disjoint r2 n /\

    SM.bn_mont_pre (as_seq h n) mu /\
    bn_v h r2 == pow2 (2 * bits t * v len) % bn_v h n)
  (ensures  fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    bn_v h1 res == bn_v h0 a % bn_v h0 n)


inline_for_extraction noextract
val bn_mod_slow_precomp:
    #t:limb_t
  -> k:AM.almost_mont t ->
  bn_mod_slow_precomp_st t k.AM.bn.BN.len

let bn_mod_slow_precomp #t k n mu r2 a res =
  let h0 = ST.get () in
  S.bn_mod_slow_precomp_lemma (as_seq h0 n) mu (as_seq h0 r2) (as_seq h0 a);
  [@inline_let] let len = k.AM.bn.BN.len in
  push_frame ();
  let a_mod = create len (uint #t #SEC 0) in
  let a1 = create (len +! len) (uint #t #SEC 0) in
  copy a1 a;
  AM.reduction n mu a1 a_mod;
  AM.to n mu r2 a_mod res;
  pop_frame ()


inline_for_extraction noextract
let bn_mod_slow_st (t:limb_t) (len:BN.meta_len t) =
    nBits:size_t
  -> n:lbignum t len
  -> a:lbignum t (len +! len)
  -> res:lbignum t len ->
  Stack unit
  (requires fun h ->
    live h n /\ live h a /\ live h res /\
    disjoint res n /\ disjoint res a /\

    1 < bn_v h n /\ bn_v h n % 2 = 1 /\
    v nBits / bits t < v len /\ pow2 (v nBits) < bn_v h n)
  (ensures  fun h0 r h1 -> modifies (loc res) h0 h1 /\
    bn_v h1 res == bn_v h0 a % bn_v h0 n)


inline_for_extraction noextract
val mk_bn_mod_slow:
    #t:limb_t
  -> len:BN.meta_len t
  -> precompr2:BM.bn_precomp_r2_mod_n_st t len
  -> bn_mod_slow_precomp:bn_mod_slow_precomp_st t len ->
  bn_mod_slow_st t len

let mk_bn_mod_slow #t len precompr2 bn_mod_slow_precomp nBits n a res =
  push_frame ();
  let r2 = create len (uint #t #SEC 0) in
  let mu = BM.bn_mont_precomp len precompr2 nBits n r2 in
  bn_mod_slow_precomp n mu r2 a res;
  pop_frame ()
