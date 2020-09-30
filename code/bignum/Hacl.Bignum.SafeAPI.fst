module Hacl.Bignum.SafeAPI

open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Mul

open Lib.IntTypes
open Lib.Buffer
open Hacl.Bignum.Definitions

module ST = FStar.HyperStack.ST
module B = LowStar.Buffer
module HS = FStar.HyperStack
module LSeq = Lib.Sequence

module BB = Hacl.Bignum.Base
module BN = Hacl.Bignum
module BM = Hacl.Bignum.Montgomery
module BE = Hacl.Bignum.Exponentiation
module BR = Hacl.Bignum.ModReduction
module BC = Hacl.Bignum.Convert

module SD = Hacl.Spec.Bignum.Definitions
module SR = Hacl.Spec.Bignum.ModReduction
module SE = Hacl.Spec.Bignum.Exponentiation
module SM = Hacl.Spec.Bignum.Montgomery
module SC = Hacl.Spec.Bignum.Convert

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

inline_for_extraction noextract
let new_bn_from_bytes_be_st (t:limb_t) =
    r:HS.rid
  -> len:size_t
  -> b:lbuffer uint8 len ->
  ST (B.buffer (limb t))
  (requires fun h ->
    live h b /\
    ST.is_eternal_region r)
  (ensures  fun h0 res h1 ->
    B.(modifies loc_none h0 h1) /\
    not (B.g_is_null res) ==> (
      0 < v len /\ numbytes t * v (blocks len (size (numbytes t))) <= max_size_t /\
      B.len res == blocks len (size (numbytes t)) /\
      B.(fresh_loc (loc_buffer res) h0 h1) /\
      B.(loc_includes (loc_region_only false r) (loc_buffer res)) /\
      as_seq h1 (res <: lbignum t (blocks len (size (numbytes t)))) == SC.bn_from_bytes_be (v len) (as_seq h0 b)))


inline_for_extraction noextract
val new_bn_from_bytes_be: #t:limb_t -> new_bn_from_bytes_be_st t
let new_bn_from_bytes_be #t r len b =
  [@inline_let]
  let numb = size (numbytes t) in
  if len = 0ul || not (blocks len numb <=. 0xfffffffful `FStar.UInt32.div` numb) then
    B.null
  else
    let h0 = ST.get () in
    let res = LowStar.Monotonic.Buffer.mmalloc_partial r (uint #t 0) (blocks len numb) in
    if B.is_null res then
      res
    else
      let h1 = ST.get () in
      B.(modifies_only_not_unused_in loc_none h0 h1);
      assert (B.len res == blocks len numb);
      let res: Lib.Buffer.buffer (limb t) = res in
      assert (B.length res == FStar.UInt32.v (blocks len numb));
      let res: lbignum t (blocks len numb) = res in
      BC.mk_bn_from_bytes_be len b res;
      let h2 = ST.get () in
      B.(modifies_only_not_unused_in loc_none h0 h2);
      res


inline_for_extraction noextract
let new_bn_precomp_r2_mod_n_st (t:limb_t) =
    r:HS.rid
  -> nLen:size_t
  -> n:lbignum t nLen ->
  ST (B.buffer (limb t))
  (requires fun h -> live h n /\ ST.is_eternal_region r)
  (ensures  fun h0 res h1 ->
    B.(modifies loc_none h0 h1) /\
    not (B.g_is_null res) ==> (
      0 < v nLen /\ 2 * bits t * v nLen <= max_size_t /\
      1 < bn_v h0 n /\ bn_v h0 n % 2 = 1 /\
      B.len res == nLen /\
      B.(fresh_loc (loc_buffer res) h0 h1) /\
      B.(loc_includes (loc_region_only false r) (loc_buffer res)) /\
      as_seq h1 (res <: lbignum t nLen) == SM.bn_precomp_r2_mod_n (as_seq h0 n) /\
      bn_v #t #nLen h1 res == pow2 (2 * bits t * v nLen) % bn_v h0 n))


inline_for_extraction noextract
val new_bn_precomp_r2_mod_n: #t:limb_t -> new_bn_precomp_r2_mod_n_st t
let new_bn_precomp_r2_mod_n #t r len n =
  [@inline_let]
  let bs2 : x:size_t {0 < v x} = 2ul *! size (bits t) in
  if len = 0ul || not (len <=. 0xfffffffful `FStar.UInt32.div` bs2)
  then B.null
  else
    let is_valid_m = BM.bn_check_modulus n in
    if not (Hacl.Bignum.Base.unsafe_bool_of_limb is_valid_m) then
      B.null
    else
      let h0 = ST.get () in
      let res = LowStar.Monotonic.Buffer.mmalloc_partial r (uint #t 0) len in
      if B.is_null res then
	res
      else
	let h1 = ST.get () in
	B.(modifies_only_not_unused_in loc_none h0 h1);
	assert (B.len res == len);
	let res: Lib.Buffer.buffer (limb t) = res in
	assert (B.length res == FStar.UInt32.v len);
	let res: lbignum t len = res in
	BM.bn_precomp_r2_mod_n (BN.mk_runtime_bn t len) n res;
	let h2 = ST.get () in
	B.(modifies_only_not_unused_in loc_none h0 h2);
	SM.bn_precomp_r2_mod_n_lemma (as_seq h0 n);
	res


inline_for_extraction noextract
let bn_mod_slow_safe_st (t:limb_t) (len:BN.meta_len t) =
    n:lbignum t len
  -> a:lbignum t (len +! len)
  -> res:lbignum t len ->
  Stack bool
  (requires fun h ->
    live h n /\ live h a /\ live h res /\
    disjoint res n /\ disjoint res a)
  (ensures  fun h0 r h1 -> modifies (loc res) h0 h1 /\
    r == BB.unsafe_bool_of_limb (SR.bn_check_bn_mod (as_seq h0 n) (as_seq h0 a)) /\
    (r ==> bn_v h1 res == bn_v h0 a % bn_v h0 n))


inline_for_extraction noextract
val bn_mod_slow_safe:
    #t:limb_t
  -> #len:BN.meta_len t
  -> k:BM.mont t len
  -> bn_check_bn_mod:BR.bn_check_bn_mod_st t len
  -> bn_mod_slow_precompr2:BR.bn_mod_slow_precompr2_st t len ->
  bn_mod_slow_safe_st t len

let bn_mod_slow_safe #t #len k bn_check_bn_mod bn_mod_slow_safe_st n a res =
  let h0 = ST.get () in
  let is_valid_m = bn_check_bn_mod n a in
  BR.bn_mod_slow k bn_mod_slow_safe_st n a res;
  let h1 = ST.get () in
  mapT len res (logand is_valid_m) res;
  let h2 = ST.get () in
  SD.bn_mask_lemma (as_seq h1 res) is_valid_m;

  if BB.unsafe_bool_of_limb is_valid_m then begin
    SR.bn_mod_slow_lemma (as_seq h0 n) (as_seq h0 a);
    assert (bn_v h2 res == bn_v h0 a % bn_v h0 n) end;
  BB.unsafe_bool_of_limb is_valid_m


inline_for_extraction noextract
let bn_mod_exp_safe_st (t:limb_t) (len:BN.meta_len t) =
    n:lbignum t len
  -> a:lbignum t len
  -> bBits:size_t{0 < v bBits /\ bits t * v (blocks bBits (size (bits t))) <= max_size_t}
  -> b:lbignum t (blocks bBits (size (bits t)))
  -> res:lbignum t len ->
  Stack bool
  (requires fun h ->
    live h n /\ live h a /\ live h b /\ live h res /\
    disjoint res a /\ disjoint res b /\ disjoint res n /\ disjoint n a)
  (ensures  fun h0 r h1 -> modifies (loc res) h0 h1 /\
    r == BB.unsafe_bool_of_limb (SE.bn_check_mod_exp (as_seq h0 n) (as_seq h0 a) (v bBits) (as_seq h0 b)) /\
    (r ==> SE.bn_mod_exp_post (as_seq h0 n) (as_seq h0 a) (v bBits) (as_seq h0 b) (as_seq h1 res)))


inline_for_extraction noextract
val bn_mod_exp_safe:
    #t:limb_t
  -> #len:BN.meta_len t
  -> k:BM.mont t len
  -> bn_check_mod_exp:BE.bn_check_mod_exp_st t len
  -> bn_mod_exp_precompr2:BE.bn_mod_exp_precompr2_st t len ->
  bn_mod_exp_safe_st t len

let bn_mod_exp_safe #t #len k bn_check_mod_exp bn_mod_exp_precompr2 n a bBits b res =
  let h0 = ST.get () in
  let is_valid_m = bn_check_mod_exp n a bBits b in
  BE.bn_mod_exp #t #len k bn_mod_exp_precompr2 n a bBits b res;
  let h1 = ST.get () in
  mapT len res (logand is_valid_m) res;
  let h2 = ST.get () in
  SD.bn_mask_lemma (as_seq h1 res) is_valid_m;

  if BB.unsafe_bool_of_limb is_valid_m then begin
    SE.bn_mod_exp_lemma (v len) (as_seq h0 n) (as_seq h0 a) (v bBits) (as_seq h0 b);
    assert (SE.bn_mod_exp_post (as_seq h0 n) (as_seq h0 a) (v bBits) (as_seq h0 b) (as_seq h2 res)) end;
  BB.unsafe_bool_of_limb is_valid_m


inline_for_extraction noextract
val bn_mod_exp_mont_ladder_safe:
    #t:limb_t
  -> #len:BN.meta_len t
  -> k:BM.mont t len
  -> bn_check_mod_exp:BE.bn_check_mod_exp_st t len
  -> bn_mod_exp_mont_ladder_precompr2:BE.bn_mod_exp_mont_ladder_precompr2_st t len ->
  bn_mod_exp_safe_st t len

let bn_mod_exp_mont_ladder_safe #t #len k bn_check_mod_exp bn_mod_exp_mont_ladder_precompr2 n a bBits b res =
  let h0 = ST.get () in
  let is_valid_m = bn_check_mod_exp n a bBits b in
  BE.bn_mod_exp_mont_ladder #t #len k bn_mod_exp_mont_ladder_precompr2 n a bBits b res;
  let h1 = ST.get () in
  mapT len res (logand is_valid_m) res;
  let h2 = ST.get () in
  SD.bn_mask_lemma (as_seq h1 res) is_valid_m;

  if BB.unsafe_bool_of_limb is_valid_m then begin
    SE.bn_mod_exp_mont_ladder_lemma (v len) (as_seq h0 n) (as_seq h0 a) (v bBits) (as_seq h0 b);
    assert (SE.bn_mod_exp_post (as_seq h0 n) (as_seq h0 a) (v bBits) (as_seq h0 b) (as_seq h1 res)) end;
  BB.unsafe_bool_of_limb is_valid_m
