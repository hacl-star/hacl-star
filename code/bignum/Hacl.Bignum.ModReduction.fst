module Hacl.Bignum.ModReduction

open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Mul

open Lib.IntTypes
open Lib.Buffer

open Hacl.Bignum.Definitions

module ST = FStar.HyperStack.ST
module Loops = Lib.LoopCombinators
module LSeq = Lib.Sequence
module B = LowStar.Buffer

module S = Hacl.Spec.Bignum.ModReduction
module BN = Hacl.Bignum
module BM = Hacl.Bignum.Montgomery

#reset-options "--z3rlimit 50 --fuel 0 --ifuel 0"


inline_for_extraction noextract
let bn_mod_slow_precompr2_st (nLen:BN.meta_len) =
    n:lbignum nLen
  -> a:lbignum (nLen +! nLen)
  -> r2:lbignum nLen
  -> res:lbignum nLen ->
  Stack unit
  (requires fun h ->
    live h n /\ live h a /\ live h r2 /\ live h res /\
    disjoint res n /\ disjoint res a /\ disjoint res r2 /\ disjoint r2 n)
  (ensures  fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    as_seq h1 res == S.bn_mod_slow_precompr2 (as_seq h0 n) (as_seq h0 a) (as_seq h0 r2))


inline_for_extraction noextract
val mk_bn_mod_slow_precompr2: nLen:BN.meta_len
  -> (#[FStar.Tactics.Typeclasses.tcresolve ()] _ : Hacl.Bignum.Montgomery.mont nLen)
  -> bn_mod_slow_precompr2_st nLen

let mk_bn_mod_slow_precompr2 nLen #_ n a r2 res =
  push_frame ();
  let a_mod = create nLen (u64 0) in
  let a1 = create (nLen +! nLen) (u64 0) in
  copy a1 a;
  let mu = BM.mod_inv_u64 n.(0ul) in
  BM.reduction n mu a1 a_mod;
  BM.to n mu r2 a_mod res;
  pop_frame ()


val bn_mod_slow_precompr2: nLen:BN.meta_len -> bn_mod_slow_precompr2_st nLen
[@CInline]
let bn_mod_slow_precompr2 nLen =
  mk_bn_mod_slow_precompr2 nLen #(BM.mk_runtime_mont nLen)


inline_for_extraction noextract
let bn_mod_slow_st (nLen:BN.meta_len) =
    n:lbignum nLen
  -> a:lbignum (nLen +! nLen)
  -> res:lbignum nLen ->
  Stack unit
  (requires fun h ->
    live h n /\ live h a /\ live h res /\
    disjoint res n /\ disjoint res a)
  (ensures  fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    as_seq h1 res == S.bn_mod_slow (as_seq h0 n) (as_seq h0 a))


inline_for_extraction noextract
val mk_bn_mod_slow: nLen:BN.meta_len
  -> (#[FStar.Tactics.Typeclasses.tcresolve ()] _ : Hacl.Bignum.Montgomery.mont nLen)
  -> bn_mod_slow_st nLen

let mk_bn_mod_slow nLen #k n a res =
  push_frame ();
  let r2 = create nLen (u64 0) in
  BM.precomp n r2;
  mk_bn_mod_slow_precompr2 nLen #k n a r2 res;
  pop_frame ()


val bn_mod_slow: nLen:BN.meta_len -> bn_mod_slow_st nLen
[@CInline]
let bn_mod_slow nLen =
  mk_bn_mod_slow nLen #(BM.mk_runtime_mont nLen)
