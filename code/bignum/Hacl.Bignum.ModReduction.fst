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
module BB = Hacl.Bignum.Base
module BD = Hacl.Spec.Bignum.Definitions

#reset-options "--z3rlimit 50 --fuel 0 --ifuel 0"

inline_for_extraction noextract
let check_bn_mod_st (t:limb_t) (nLen:BN.meta_len) =
    n:lbignum t nLen
  -> a:lbignum t (nLen +! nLen) ->
  Stack (limb t)
  (requires fun h -> live h n /\ live h a)
  (ensures  fun h0 r h1 -> modifies0 h0 h1 /\
    r == S.check_bn_mod (as_seq h0 n) (as_seq h0 a))


inline_for_extraction noextract
val mk_check_bn_mod_st:
    #t:limb_t
  -> nLen:BN.meta_len
  -> (#[FStar.Tactics.Typeclasses.tcresolve ()] _ : Hacl.Bignum.Montgomery.mont t nLen)
  -> check_bn_mod_st t nLen

let mk_check_bn_mod_st #t nLen #_ n a =
  push_frame ();
  let m0 = BM.check n in
  let n2 = create (nLen +! nLen) (uint #t 0) in
  BN.mul n n n2;
  let m1 = BN.bn_lt_mask (nLen +! nLen) a n2 in
  let r = m0 &. m1 in
  pop_frame ();
  r


inline_for_extraction noextract
let bn_mod_slow_precompr2_st (t:limb_t) (nLen:BN.meta_len) =
    n:lbignum t nLen
  -> a:lbignum t (nLen +! nLen)
  -> r2:lbignum t nLen
  -> res:lbignum t nLen ->
  Stack unit
  (requires fun h ->
    live h n /\ live h a /\ live h r2 /\ live h res /\
    disjoint res n /\ disjoint res a /\ disjoint res r2 /\ disjoint r2 n)
  (ensures  fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    as_seq h1 res == S.bn_mod_slow_precompr2 (as_seq h0 n) (as_seq h0 a) (as_seq h0 r2))


inline_for_extraction noextract
val mk_bn_mod_slow_precompr2:
    #t:limb_t
  -> nLen:BN.meta_len
  -> (#[FStar.Tactics.Typeclasses.tcresolve ()] _ : Hacl.Bignum.Montgomery.mont t nLen)
  -> bn_mod_slow_precompr2_st t nLen

let mk_bn_mod_slow_precompr2 #t nLen #_ n a r2 res =
  push_frame ();
  let a_mod = create nLen (uint #t 0) in
  let a1 = create (nLen +! nLen) (uint #t 0) in
  copy a1 a;
  let mu = BM.mod_inv_limb n.(0ul) in
  BM.reduction n mu a1 a_mod;
  BM.to n mu r2 a_mod res;
  pop_frame ()


val bn_mod_slow_precompr2: #t:limb_t -> nLen:BN.meta_len -> bn_mod_slow_precompr2_st t nLen
[@CInline]
let bn_mod_slow_precompr2 #t nLen =
  mk_bn_mod_slow_precompr2 nLen #(BM.mk_runtime_mont t nLen)


inline_for_extraction noextract
let bn_mod_slow_st (t:limb_t) (nLen:BN.meta_len) =
    n:lbignum t nLen
  -> a:lbignum t (nLen +! nLen)
  -> res:lbignum t nLen ->
  Stack bool
  (requires fun h ->
    live h n /\ live h a /\ live h res /\
    disjoint res n /\ disjoint res a)
  (ensures  fun h0 r h1 -> modifies (loc res) h0 h1 /\
    r == BB.unsafe_bool_of_limb (S.check_bn_mod (as_seq h0 n) (as_seq h0 a)) /\
    (r ==> bn_v h1 res == bn_v h0 a % bn_v h0 n))


inline_for_extraction noextract
val mk_bn_mod_slow:
    #t:limb_t
  -> nLen:BN.meta_len
  -> (#[FStar.Tactics.Typeclasses.tcresolve ()] _ : Hacl.Bignum.Montgomery.mont t nLen)
  -> bn_mod_slow_st t nLen

let mk_bn_mod_slow #t nLen #k n a res =
  let h0 = ST.get () in
  let is_valid_m = mk_check_bn_mod_st nLen #k n a in
  push_frame ();
  let r2 = create nLen (uint #t 0) in
  BM.precomp n r2;
  mk_bn_mod_slow_precompr2 nLen #k n a r2 res;
  let h1 = ST.get () in
  mapT nLen res (logand is_valid_m) res;
  let h2 = ST.get () in
  BD.bn_mask_lemma (as_seq h1 res) is_valid_m;

  if BB.unsafe_bool_of_limb is_valid_m then begin
    S.bn_mod_slow_lemma (as_seq h0 n) (as_seq h0 a);
    assert (bn_v h2 res == bn_v h0 a % bn_v h0 n) end;
  pop_frame ();
  BB.unsafe_bool_of_limb is_valid_m


val bn_mod_slow: #t:limb_t -> nLen:BN.meta_len -> bn_mod_slow_st t nLen
[@CInline]
let bn_mod_slow #t nLen =
  mk_bn_mod_slow nLen #(BM.mk_runtime_mont t nLen)
