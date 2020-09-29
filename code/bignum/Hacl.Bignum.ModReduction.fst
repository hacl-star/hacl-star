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
let bn_check_bn_mod_st (t:limb_t) (len:BN.meta_len t) =
    n:lbignum t len
  -> a:lbignum t (len +! len) ->
  Stack (limb t)
  (requires fun h -> live h n /\ live h a)
  (ensures  fun h0 r h1 -> modifies0 h0 h1 /\
    r == S.bn_check_bn_mod (as_seq h0 n) (as_seq h0 a))


inline_for_extraction noextract
val mk_bn_check_bn_mod: k:BM.mont -> bn_check_bn_mod_st k.BM.bn.BN.t k.BM.bn.BN.len
let mk_bn_check_bn_mod k n a =
  [@inline_let] let t = k.BM.bn.BN.t in
  [@inline_let] let len = k.BM.bn.BN.len in
  push_frame ();
  let m0 = BM.check n in
  let n2 = create (len +! len) (uint #t #SEC 0) in
  BN.mul n n n2;
  let m1 = BN.bn_lt_mask (len +! len) a n2 in
  let r = m0 &. m1 in
  pop_frame ();
  r


inline_for_extraction noextract
let bn_mod_slow_precompr2_st (t:limb_t) (len:BN.meta_len t) =
    n:lbignum t len
  -> a:lbignum t (len +! len)
  -> r2:lbignum t len
  -> res:lbignum t len ->
  Stack unit
  (requires fun h ->
    live h n /\ live h a /\ live h r2 /\ live h res /\
    disjoint res n /\ disjoint res a /\ disjoint res r2 /\ disjoint r2 n)
  (ensures  fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    as_seq h1 res == S.bn_mod_slow_precompr2 (as_seq h0 n) (as_seq h0 a) (as_seq h0 r2))


inline_for_extraction noextract
val mk_bn_mod_slow_precompr2: k:BM.mont -> bn_mod_slow_precompr2_st k.BM.bn.BN.t k.BM.bn.BN.len
let mk_bn_mod_slow_precompr2 k n a r2 res =
  [@inline_let] let t = k.BM.bn.BN.t in
  [@inline_let] let len = k.BM.bn.BN.len in
  push_frame ();
  let a_mod = create len (uint #t #SEC 0) in
  let a1 = create (len +! len) (uint #t #SEC 0) in
  copy a1 a;
  let mu = BM.mod_inv_limb n.(0ul) in
  BM.reduction n mu a1 a_mod;
  BM.to n mu r2 a_mod res;
  pop_frame ()


inline_for_extraction noextract
let bn_mod_slow_st (t:limb_t) (len:BN.meta_len t) =
    n:lbignum t len
  -> a:lbignum t (len +! len)
  -> res:lbignum t len ->
  Stack bool
  (requires fun h ->
    live h n /\ live h a /\ live h res /\
    disjoint res n /\ disjoint res a)
  (ensures  fun h0 r h1 -> modifies (loc res) h0 h1 /\
    r == BB.unsafe_bool_of_limb (S.bn_check_bn_mod (as_seq h0 n) (as_seq h0 a)) /\
    (r ==> bn_v h1 res == bn_v h0 a % bn_v h0 n))


inline_for_extraction noextract
val mk_bn_mod_slow: k:BM.mont -> bn_mod_slow_st k.BM.bn.BN.t k.BM.bn.BN.len
let mk_bn_mod_slow k n a res =
  [@inline_let] let t = k.BM.bn.BN.t in
  [@inline_let] let len = k.BM.bn.BN.len in
  let h0 = ST.get () in
  let is_valid_m = mk_bn_check_bn_mod k n a in
  push_frame ();
  let r2 = create len (uint #t #SEC 0) in
  BM.precomp n r2;
  mk_bn_mod_slow_precompr2 k n a r2 res;
  let h1 = ST.get () in
  mapT len res (logand is_valid_m) res;
  let h2 = ST.get () in
  BD.bn_mask_lemma (as_seq h1 res) is_valid_m;

  if BB.unsafe_bool_of_limb is_valid_m then begin
    S.bn_mod_slow_lemma (as_seq h0 n) (as_seq h0 a);
    assert (bn_v h2 res == bn_v h0 a % bn_v h0 n) end;
  pop_frame ();
  BB.unsafe_bool_of_limb is_valid_m
