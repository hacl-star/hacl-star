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

module E = Hacl.Spec.Exponentiation.Lemmas

module BL = Hacl.Bignum.Lib
module BB = Hacl.Bignum.Base
module BN = Hacl.Bignum
module AM = Hacl.Bignum.AlmostMontgomery
module BMA = Hacl.Bignum.MontArithmetic
module ME = Hacl.Bignum.MontExponentiation
module BM = Hacl.Bignum.Montgomery
module BE = Hacl.Bignum.Exponentiation
module BR = Hacl.Bignum.ModReduction
module BC = Hacl.Bignum.Convert
module BI = Hacl.Bignum.ModInv

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
let new_bn_from_bytes_le_st (t:limb_t) =
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
      as_seq h1 (res <: lbignum t (blocks len (size (numbytes t)))) == SC.bn_from_bytes_le (v len) (as_seq h0 b)))


inline_for_extraction noextract
val new_bn_from_bytes_le: #t:limb_t -> new_bn_from_bytes_le_st t
let new_bn_from_bytes_le #t r len b =
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
      BC.mk_bn_from_bytes_le len b res;
      let h2 = ST.get () in
      B.(modifies_only_not_unused_in loc_none h0 h2);
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
    r == BB.unsafe_bool_of_limb (SM.bn_check_modulus (as_seq h0 n)) /\
    (r ==> bn_v h1 res == bn_v h0 a % bn_v h0 n))


inline_for_extraction noextract
val bn_mod_slow_safe:
    #t:limb_t
  -> k:AM.almost_mont t
  -> bn_mod_precompr2:BR.bn_mod_slow_precompr2_st t k.AM.bn.BN.len ->
  bn_mod_slow_safe_st t k.AM.bn.BN.len

let bn_mod_slow_safe #t k bn_mod_precompr2 n a res =
  [@inline_let] let len = k.AM.bn.BN.len in
  let h0 = ST.get () in
  let is_valid_m = AM.mont_check n in
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


//TODO: rm k:BE.exp ?
inline_for_extraction noextract
val mk_bn_mod_exp_safe:
    #t:limb_t
  -> k:BE.exp t
  -> bn_mod_exp:BE.bn_mod_exp_st t k.BE.bn.BN.len ->
  bn_mod_exp_safe_st t k.BE.bn.BN.len

let mk_bn_mod_exp_safe #t k bn_mod_exp n a bBits b res =
  [@inline_let] let len = k.BE.bn.BN.len in
  let h0 = ST.get () in
  let is_valid_m = k.BE.exp_check n a bBits b in
  let nBits = size (bits t) *! BB.unsafe_size_from_limb (BL.bn_get_top_index len n) in

  if BB.unsafe_bool_of_limb is_valid_m then begin
    SL.bn_low_bound_bits_lemma #t #(v len) (as_seq h0 n);
    bn_mod_exp nBits n a bBits b res end;

  let h1 = ST.get () in
  mapT len res (logand is_valid_m) res;
  SD.bn_mask_lemma (as_seq h1 res) is_valid_m;
  BB.unsafe_bool_of_limb is_valid_m


// inline_for_extraction noextract
// val bn_mod_exp_vartime_safe:
//     #t:limb_t
//   -> k:BE.exp t
//   -> bn_mod_exp_vartime:BE.bn_mod_exp_st t k.BE.bn.BN.len ->
//   bn_mod_exp_safe_st t k.BE.bn.BN.len

// let bn_mod_exp_vartime_safe #t k bn_mod_exp_vartime n a bBits b res =
//   mk_bn_mod_exp_safe #t k bn_mod_exp_vartime n a bBits b res


// inline_for_extraction noextract
// val bn_mod_exp_consttime_safe:
//     #t:limb_t
//   -> k:BE.exp t
//   -> bn_mod_exp_consttime:BE.bn_mod_exp_st t k.BE.bn.BN.len ->
//   bn_mod_exp_safe_st t k.BE.bn.BN.len

// let bn_mod_exp_consttime_safe #t k bn_mod_exp_consttime n a bBits b res =
//   mk_bn_mod_exp_safe #t k bn_mod_exp_consttime n a bBits b res


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
    r == BB.unsafe_bool_of_limb (SI.bn_check_mod_inv_prime (as_seq h0 n) (as_seq h0 a)) /\
   (r ==> bn_v h1 res * bn_v h0 a % bn_v h0 n = 1))


inline_for_extraction noextract
val mk_bn_mod_inv_prime_safe:
    #t:limb_t
  -> len:BN.meta_len t
  -> bn_mod_exp:BE.bn_mod_exp_st t len ->
  bn_mod_inv_prime_safe_st t len

let mk_bn_mod_inv_prime_safe #t len bn_mod_exp n a res =
  let h0 = ST.get () in
  let is_valid_m = BI.bn_check_mod_inv_prime #t len n a in
  let nBits = size (bits t) *! BB.unsafe_size_from_limb (BL.bn_get_top_index len n) in

  if BB.unsafe_bool_of_limb is_valid_m then begin
    SL.bn_low_bound_bits_lemma #t #(v len) (as_seq h0 n);
    BI.bn_mod_inv_prime len bn_mod_exp nBits n a res end;

  let h1 = ST.get () in
  mapT len res (logand is_valid_m) res;
  SD.bn_mask_lemma (as_seq h1 res) is_valid_m;
  BB.unsafe_bool_of_limb is_valid_m


// inline_for_extraction noextract
// val bn_mod_inv_prime_vartime_safe:
//     #t:limb_t
//   -> len:BN.meta_len t
//   -> bn_mod_exp_vartime:BE.bn_mod_exp_st t len ->
//   bn_mod_inv_prime_safe_st t len

// let bn_mod_inv_prime_vartime_safe #t len bn_mod_exp_vartime n a res =
//   mk_bn_mod_inv_prime_safe #t len bn_mod_exp_vartime n a res


inline_for_extraction noextract
let bn_mod_exp_ctx_st (t:limb_t) (k:BMA.bn_mont_ctx t) =
    a:lbignum t k.BMA.len
  -> bBits:size_t{v bBits > 0}
  -> b:lbignum t (blocks bBits (size (bits t)))
  -> res:lbignum t k.BMA.len ->
  Stack unit
  (requires fun h ->
    BMA.bn_mont_ctx_inv h k /\
    bn_v h a < bn_v #t #k.BMA.len h k.BMA.n /\
    0 < bn_v h b /\ bn_v h b < pow2 (v bBits) /\

    live h a /\ live h b /\ live h res /\
    disjoint res a /\ disjoint res b /\
    disjoint res (k.BMA.n <: lbignum t k.BMA.len) /\
    disjoint a (k.BMA.n <: lbignum t k.BMA.len) /\
    disjoint res (k.BMA.r2 <: lbignum t k.BMA.len) /\
    disjoint a (k.BMA.r2 <: lbignum t k.BMA.len))
  (ensures  fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    SE.bn_mod_exp_post (as_seq #MUT #(limb t) h0 k.BMA.n) (as_seq h0 a) (v bBits) (as_seq h0 b) (as_seq h1 res))


inline_for_extraction noextract
val mk_bn_mod_exp_ctx:
    #t:limb_t
  -> km:BM.mont t
  -> k:BMA.bn_mont_ctx t{k.BMA.len == km.BM.bn.BN.len}
  -> bn_exp_mont: ME.bn_exp_mont_st t km.BM.bn.BN.len ->
  bn_mod_exp_ctx_st t k

let mk_bn_mod_exp_ctx #t km k bn_exp_mont a bBits b res =
  let h0 = ST.get () in
  [@inline_let] let len = km.BM.bn.BN.len in
  push_frame ();
  let aM = create len (uint #t #SEC 0) in
  BM.to k.BMA.n k.BMA.mu k.BMA.r2 a aM;
  SM.bn_to_mont_lemma (as_seq #MUT h0 k.BMA.n) k.BMA.mu (as_seq #MUT h0 k.BMA.r2) (as_seq h0 a);

  let resM = create len (uint #t #SEC 0) in
  bn_exp_mont k.BMA.n k.BMA.mu k.BMA.r2 aM bBits b resM;
  BM.from k.BMA.n k.BMA.mu resM res;

  let h1 = ST.get () in
  SM.bn_from_mont_lemma (as_seq #MUT h0 k.BMA.n) k.BMA.mu (as_seq h1 resM);
  E.mod_exp_mont_ll_lemma (bits t) (v len) (bn_v #t #len h0 k.BMA.n) (v #t #SEC k.BMA.mu) (bn_v h0 a) (bn_v h0 b);
  assert (bn_v h1 res == Lib.NatMod.pow_mod #(bn_v #t #len h0 k.BMA.n) (bn_v h0 a) (bn_v h0 b));
  pop_frame ()


// inline_for_extraction noextract
// val bn_mod_exp_ctx_consttime:
//     #t:limb_t
//   -> km:BM.mont t
//   -> k:BMA.bn_mont_ctx t{k.BMA.len == km.BM.bn.BN.len}
//   -> bn_exp_mont_consttime: ME.bn_exp_mont_st t km.BM.bn.BN.len ->
//   bn_mod_exp_ctx_st t k

// let bn_mod_exp_ctx_consttime #t km k bn_exp_mont_consttime a bBits b res =
//   mk_bn_mod_exp_ctx #t km k bn_exp_mont_consttime a bBits b res

inline_for_extraction noextract
let bn_mod_slow_ctx_st (t:limb_t) (k:BMA.bn_mont_ctx t) =
    a:lbignum t (k.BMA.len +! k.BMA.len)
  -> res:lbignum t k.BMA.len ->
  Stack unit
  (requires fun h ->
    BMA.bn_mont_ctx_inv h k /\

    live h a /\ live h res /\ disjoint res a /\
    disjoint res (k.BMA.n <: lbignum t k.BMA.len) /\
    disjoint res (k.BMA.r2 <: lbignum t k.BMA.len))
  (ensures  fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    bn_v h1 res == bn_v h0 a % bn_v #t #k.BMA.len h0 k.BMA.n)


inline_for_extraction noextract
val bn_mod_ctx:
    #t:limb_t
  -> km:AM.almost_mont t
  -> k:BMA.bn_mont_ctx t{k.BMA.len == km.AM.bn.BN.len} ->
  bn_mod_slow_ctx_st t k

let bn_mod_ctx #t km k a res =
  let h0 = ST.get () in
  SR.bn_mod_slow_precompr2_lemma (as_seq #MUT h0 k.BMA.n) k.BMA.mu
    (as_seq #MUT #(limb t) #k.BMA.len h0 k.BMA.r2) (as_seq h0 a);
  BR.bn_mod_slow_precompr2 km k.BMA.n k.BMA.mu k.BMA.r2 a res
