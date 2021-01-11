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

module BL = Hacl.Bignum.Lib
module BB = Hacl.Bignum.Base
module BN = Hacl.Bignum
module BM = Hacl.Bignum.Montgomery
module BE = Hacl.Bignum.Exponentiation
module BR = Hacl.Bignum.ModReduction
module BC = Hacl.Bignum.Convert
module BI = Hacl.Bignum.ModInv

module SN = Hacl.Spec.Bignum
module SL = Hacl.Spec.Bignum.Lib
module SD = Hacl.Spec.Bignum.Definitions
module SR = Hacl.Spec.Bignum.ModReduction
module SE = Hacl.Spec.Bignum.Exponentiation
module SM = Hacl.Spec.Bignum.Montgomery
module SC = Hacl.Spec.Bignum.Convert
module SI = Hacl.Spec.Bignum.ModInv

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
let new_bn_precomp_r2_mod_n_st (t:limb_t) (len:BN.meta_len t) =
    r:HS.rid
  -> n:lbignum t len ->
  ST (B.buffer (limb t))
  (requires fun h -> live h n /\ ST.is_eternal_region r)
  (ensures  fun h0 res h1 ->
    B.(modifies loc_none h0 h1) /\
    not (B.g_is_null res) ==> (
      1 < bn_v h0 n /\ bn_v h0 n % 2 = 1 /\
      B.len res == len /\
      B.(fresh_loc (loc_buffer res) h0 h1) /\
      B.(loc_includes (loc_region_only false r) (loc_buffer res)) /\
      as_seq h1 (res <: lbignum t len) ==
	SM.bn_precomp_r2_mod_n (SL.bn_low_bound_bits #t #(v len) (as_seq h0 n)) (as_seq h0 n) /\
      bn_v #t #len h1 res == pow2 (2 * bits t * v len) % bn_v h0 n))


inline_for_extraction noextract
val new_bn_precomp_r2_mod_n: #t:limb_t -> k:BM.mont t -> new_bn_precomp_r2_mod_n_st t k.BM.bn.BN.len
let new_bn_precomp_r2_mod_n #t k r n =
  [@inline_let] let len = k.BM.bn.BN.len in
  let is_valid_m = BM.bn_check_modulus n in
  if not (BB.unsafe_bool_of_limb is_valid_m) then
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
      let nBits = size (bits t) *! BB.unsafe_size_from_limb (BL.bn_get_top_index len n) in
      SL.bn_low_bound_bits_lemma #t #(v len) (as_seq h0 n);
      k.BM.precomp nBits n res;
      let h2 = ST.get () in
      B.(modifies_only_not_unused_in loc_none h0 h2);
      SM.bn_precomp_r2_mod_n_lemma (v nBits) (as_seq h0 n);
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
  -> k:BM.mont t
  -> bn_mod_precompr2:BR.bn_mod_slow_precompr2_st t k.BM.bn.BN.len ->
  bn_mod_slow_safe_st t k.BM.bn.BN.len

let bn_mod_slow_safe #t k bn_mod_precompr2 n a res =
  [@inline_let] let len = k.BM.bn.BN.len in
  let h0 = ST.get () in
  let is_valid_m = BR.bn_check_bn_mod k n a in
  let nBits = size (bits t) *! BB.unsafe_size_from_limb (BL.bn_get_top_index len n) in

  BR.bn_mod_slow k bn_mod_precompr2 nBits n a res;
  let h1 = ST.get () in
  mapT len res (logand is_valid_m) res;
  SD.bn_mask_lemma (as_seq h1 res) is_valid_m;

  if BB.unsafe_bool_of_limb is_valid_m then begin
    SL.bn_low_bound_bits_lemma #t #(v len) (as_seq h0 n);
    SR.bn_mod_slow_lemma (v nBits) (as_seq h0 n) (as_seq h0 a) end;
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
val bn_mod_exp_safe: #t:limb_t -> k:BE.exp t -> bn_mod_exp_safe_st t k.BE.mont.BM.bn.BN.len
let bn_mod_exp_safe #t k n a bBits b res =
  [@inline_let] let len = k.BE.mont.BM.bn.BN.len in
  let h0 = ST.get () in
  let is_valid_m = k.BE.exp_check n a bBits b in
  let nBits = size (bits t) *! BB.unsafe_size_from_limb (BL.bn_get_top_index len n) in

  BE.bn_mod_exp k.BE.mont k.BE.mod_exp_precomp nBits n a bBits b res;
  let h1 = ST.get () in
  mapT len res (logand is_valid_m) res;
  SD.bn_mask_lemma (as_seq h1 res) is_valid_m;

  if BB.unsafe_bool_of_limb is_valid_m then begin
    SL.bn_low_bound_bits_lemma #t #(v len) (as_seq h0 n);
    SE.bn_mod_exp_lemma (v len) (v nBits) (as_seq h0 n) (as_seq h0 a) (v bBits) (as_seq h0 b) end;
  BB.unsafe_bool_of_limb is_valid_m


inline_for_extraction noextract
val bn_mod_exp_mont_ladder_safe: #t:limb_t -> k:BE.exp t -> bn_mod_exp_safe_st t k.BE.mont.BM.bn.BN.len
let bn_mod_exp_mont_ladder_safe #t k n a bBits b res =
  [@inline_let] let len = k.BE.mont.BM.bn.BN.len in
  let h0 = ST.get () in
  let is_valid_m = k.BE.exp_check n a bBits b in
  let nBits = size (bits t) *! BB.unsafe_size_from_limb (BL.bn_get_top_index len n) in

  BE.bn_mod_exp_mont_ladder k.BE.mont k.BE.ct_mod_exp_precomp nBits n a bBits b res;
  let h1 = ST.get () in
  mapT len res (logand is_valid_m) res;
  SD.bn_mask_lemma (as_seq h1 res) is_valid_m;

  if BB.unsafe_bool_of_limb is_valid_m then begin
    SL.bn_low_bound_bits_lemma #t #(v len) (as_seq h0 n);
    SE.bn_mod_exp_mont_ladder_lemma (v len) (v nBits) (as_seq h0 n) (as_seq h0 a) (v bBits) (as_seq h0 b);
    assert (SE.bn_mod_exp_post (as_seq h0 n) (as_seq h0 a) (v bBits) (as_seq h0 b) (as_seq h1 res)) end;
  BB.unsafe_bool_of_limb is_valid_m


inline_for_extraction noextract
let bn_mod_inv_prime_safe_st (t:limb_t) (len:BN.meta_len t) =
    n:lbignum t len
  -> a:lbignum t len
  -> res:lbignum t len ->
  Stack bool
  (requires fun h -> FStar.Math.Euclid.is_prime (bn_v h n) /\
    live h n /\ live h a /\ live h res /\
    disjoint res n /\ disjoint res a /\ disjoint n a)
  (ensures  fun h0 r h1 -> modifies (loc res) h0 h1 /\
    r == BB.unsafe_bool_of_limb (SI.bn_check_bn_mod_inv_prime (as_seq h0 n) (as_seq h0 a)) /\
   (r ==> bn_v h1 res * bn_v h0 a % bn_v h0 n = 1))


inline_for_extraction noextract
val bn_mod_inv_prime_safe: #t:limb_t -> k:BE.exp t -> bn_mod_inv_prime_safe_st t k.BE.mont.BM.bn.BN.len
let bn_mod_inv_prime_safe #t k n a res =
  [@inline_let] let len = k.BE.mont.BM.bn.BN.len in
  let h0 = ST.get () in
  let is_valid_m = BI.bn_check_bn_mod_inv_prime #t k n a in
  let nBits = size (bits t) *! BB.unsafe_size_from_limb (BL.bn_get_top_index len n) in

  BI.bn_mod_inv_prime k nBits n a res;
  let h1 = ST.get () in
  mapT len res (logand is_valid_m) res;
  SD.bn_mask_lemma (as_seq h1 res) is_valid_m;

  if BB.unsafe_bool_of_limb is_valid_m then begin
    SL.bn_low_bound_bits_lemma #t #(v len) (as_seq h0 n);
    SI.bn_mod_inv_prime_lemma (v nBits) (as_seq h0 n) (as_seq h0 a) end;
  BB.unsafe_bool_of_limb is_valid_m
