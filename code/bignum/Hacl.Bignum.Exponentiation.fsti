module Hacl.Bignum.Exponentiation

open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Mul

open Lib.IntTypes
open Lib.Buffer

open Hacl.Bignum.Definitions

module S = Hacl.Spec.Bignum.Exponentiation
module BN = Hacl.Bignum
module BM = Hacl.Bignum.Montgomery

#reset-options "--z3rlimit 50 --fuel 0 --ifuel 0"


inline_for_extraction noextract
let bn_check_mod_exp_st (t:limb_t) (len:BN.meta_len t) =
    n:lbignum t len
  -> a:lbignum t len
  -> bBits:size_t{0 < v bBits /\ bits t * v (blocks bBits (size (bits t))) <= max_size_t}
  -> b:lbignum t (blocks bBits (size (bits t))) ->
  Stack (limb t)
  (requires fun h ->
    live h n /\ live h a /\ live h b)
  (ensures  fun h0 r h1 -> modifies0 h0 h1 /\
    r == S.bn_check_mod_exp (as_seq h0 n) (as_seq h0 a) (v bBits) (as_seq h0 b))


inline_for_extraction noextract
val bn_check_mod_exp: #t:limb_t -> k:BM.mont t -> bn_check_mod_exp_st t k.BM.bn.BN.len


// This function is *NOT* constant-time on the exponent b.
inline_for_extraction noextract
let bn_mod_exp_raw_precompr2_st (t:limb_t) (len:BN.meta_len t) =
    n:lbignum t len
  -> a:lbignum t len
  -> bBits:size_t{v bBits > 0}
  -> b:lbignum t (blocks bBits (size (bits t)))
  -> r2:lbignum t len
  -> res:lbignum t len ->
  Stack unit
  (requires fun h ->
    live h n /\ live h a /\ live h b /\ live h res /\ live h r2 /\
    disjoint res a /\ disjoint res b /\ disjoint res n /\ disjoint n a /\
    disjoint res r2 /\ disjoint a r2 /\ disjoint n r2 /\ disjoint n b /\
    S.bn_mod_exp_pre (as_seq h n) (as_seq h a) (v bBits) (as_seq h b) /\
    bn_v h r2 == pow2 (2 * bits t * v len) % bn_v h n)
  (ensures  fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    as_seq h1 res ==
    S.bn_mod_exp_raw_precompr2 (v len) (as_seq h0 n) (as_seq h0 a) (v bBits) (as_seq h0 b) (as_seq h0 r2))


inline_for_extraction noextract
val bn_mod_exp_raw_precompr2: #t:limb_t -> k:BM.mont t -> bn_mod_exp_raw_precompr2_st t k.BM.bn.BN.len


// This function is constant-time on the exponent b.
inline_for_extraction noextract
let bn_mod_exp_ct_precompr2_st (t:limb_t) (len:BN.meta_len t) =
    n:lbignum t len
  -> a:lbignum t len
  -> bBits:size_t{v bBits > 0}
  -> b:lbignum t (blocks bBits (size (bits t)))
  -> r2:lbignum t len
  -> res:lbignum t len ->
  Stack unit
  (requires fun h ->
    live h n /\ live h a /\ live h b /\ live h res /\ live h r2 /\
    disjoint res a /\ disjoint res b /\ disjoint res n /\ disjoint n a /\
    disjoint res r2 /\ disjoint a r2 /\ disjoint n r2 /\ disjoint n b /\
    S.bn_mod_exp_pre (as_seq h n) (as_seq h a) (v bBits) (as_seq h b) /\
    bn_v h r2 == pow2 (2 * bits t * v len) % bn_v h n)
  (ensures  fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    as_seq h1 res ==
    S.bn_mod_exp_ct_precompr2 (v len) (as_seq h0 n) (as_seq h0 a) (v bBits) (as_seq h0 b) (as_seq h0 r2))


inline_for_extraction noextract
val bn_mod_exp_ct_precompr2: #t:limb_t -> k:BM.mont t -> bn_mod_exp_ct_precompr2_st t k.BM.bn.BN.len


inline_for_extraction noextract
let bn_mod_exp_fw_precompr2_st (t:limb_t) (len:BN.meta_len t) =
    n:lbignum t len
  -> a:lbignum t len
  -> bBits:size_t{v bBits > 0}
  -> b:lbignum t (blocks bBits (size (bits t)))
  -> l:size_t{0 < v l /\ v l < bits U32 /\ pow2 (v l) * v len <= max_size_t}
  -> r2:lbignum t len
  -> res:lbignum t len ->
  Stack unit
  (requires fun h ->
    live h n /\ live h a /\ live h b /\ live h res /\ live h r2 /\
    disjoint res a /\ disjoint res b /\ disjoint res n /\ disjoint n a /\
    disjoint res r2 /\ disjoint a r2 /\ disjoint n r2 /\ disjoint n b /\
    S.bn_mod_exp_pre (as_seq h n) (as_seq h a) (v bBits) (as_seq h b) /\
    bn_v h r2 == pow2 (2 * bits t * v len) % bn_v h n)
  (ensures  fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    as_seq h1 res ==
    S.bn_mod_exp_fw_precompr2 (v len) (v l) (as_seq h0 n) (as_seq h0 a) (v bBits) (as_seq h0 b) (as_seq h0 r2))


// This function is *NOT* constant-time on the exponent b.
inline_for_extraction noextract
val bn_mod_exp_fw_raw_precompr2: #t:limb_t -> k:BM.mont t -> bn_mod_exp_fw_precompr2_st t k.BM.bn.BN.len


// This function is constant-time on the exponent b.
inline_for_extraction noextract
val bn_mod_exp_fw_ct_precompr2: #t:limb_t -> k:BM.mont t -> bn_mod_exp_fw_precompr2_st t k.BM.bn.BN.len




inline_for_extraction noextract
let bn_mod_exp_raw_st (t:limb_t) (len:BN.meta_len t) =
    nBits:size_t{v nBits / bits t < v len}
  -> n:lbignum t len
  -> a:lbignum t len
  -> bBits:size_t{0 < v bBits /\ bits t * v (blocks bBits (size (bits t))) <= max_size_t}
  -> b:lbignum t (blocks bBits (size (bits t)))
  -> res:lbignum t len ->
  Stack unit
  (requires fun h ->
    live h n /\ live h a /\ live h b /\ live h res /\ disjoint n b /\
    disjoint res a /\ disjoint res b /\ disjoint res n /\ disjoint n a /\
    S.bn_mod_exp_pre (as_seq h n) (as_seq h a) (v bBits) (as_seq h b) /\
    pow2 (v nBits) < bn_v h n)
  (ensures  fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    as_seq h1 res == S.bn_mod_exp_raw (v len) (v nBits) (as_seq h0 n) (as_seq h0 a) (v bBits) (as_seq h0 b))


// This function is *NOT* constant-time on the exponent b.
inline_for_extraction noextract
val bn_mod_exp_raw:
    #t:limb_t
  -> k:BM.mont t
  -> bn_mod_exp_raw_precompr2:bn_mod_exp_raw_precompr2_st t k.BM.bn.BN.len ->
  bn_mod_exp_raw_st t k.BM.bn.BN.len


inline_for_extraction noextract
let bn_mod_exp_ct_st (t:limb_t) (len:BN.meta_len t) =
    nBits:size_t{v nBits / bits t < v len}
  -> n:lbignum t len
  -> a:lbignum t len
  -> bBits:size_t{0 < v bBits /\ bits t * v (blocks bBits (size (bits t))) <= max_size_t}
  -> b:lbignum t (blocks bBits (size (bits t)))
  -> res:lbignum t len ->
  Stack unit
  (requires fun h ->
    live h n /\ live h a /\ live h b /\ live h res /\ disjoint n b /\
    disjoint res a /\ disjoint res b /\ disjoint res n /\ disjoint n a /\
    S.bn_mod_exp_pre (as_seq h n) (as_seq h a) (v bBits) (as_seq h b) /\
    pow2 (v nBits) < bn_v h n)
  (ensures  fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    as_seq h1 res == S.bn_mod_exp_ct (v len) (v nBits) (as_seq h0 n) (as_seq h0 a) (v bBits) (as_seq h0 b))


// This function is constant-time on the exponent b.
inline_for_extraction noextract
val bn_mod_exp_ct:
    #t:limb_t
  -> k:BM.mont t
  -> bn_mod_exp_ct_precompr2:bn_mod_exp_ct_precompr2_st t k.BM.bn.BN.len ->
  bn_mod_exp_ct_st t k.BM.bn.BN.len


inline_for_extraction noextract
let bn_mod_exp_fw_st (t:limb_t) (len:BN.meta_len t) =
    nBits:size_t{v nBits / bits t < v len}
  -> n:lbignum t len
  -> a:lbignum t len
  -> bBits:size_t{0 < v bBits /\ bits t * v (blocks bBits (size (bits t))) <= max_size_t}
  -> b:lbignum t (blocks bBits (size (bits t)))
  -> l:size_t{0 < v l /\ v l < bits U32 /\ pow2 (v l) * v len <= max_size_t}
  -> res:lbignum t len ->
  Stack unit
  (requires fun h ->
    live h n /\ live h a /\ live h b /\ live h res /\ disjoint n b /\
    disjoint res a /\ disjoint res b /\ disjoint res n /\ disjoint n a /\
    S.bn_mod_exp_pre (as_seq h n) (as_seq h a) (v bBits) (as_seq h b) /\
    pow2 (v nBits) < bn_v h n)
  (ensures  fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    as_seq h1 res == S.bn_mod_exp_fw (v len) (v l) (v nBits) (as_seq h0 n) (as_seq h0 a) (v bBits) (as_seq h0 b))


// This function is *NOT* constant-time on the exponent b.
inline_for_extraction noextract
val bn_mod_exp_fw_raw:
    #t:limb_t
  -> k:BM.mont t
  -> bn_mod_exp_fw_raw_precompr2:bn_mod_exp_fw_precompr2_st t k.BM.bn.BN.len ->
  bn_mod_exp_fw_st t k.BM.bn.BN.len


// This function is constant-time on the exponent b.
inline_for_extraction noextract
val bn_mod_exp_fw_ct:
    #t:limb_t
  -> k:BM.mont t
  -> bn_mod_exp_fw_ct_precompr2:bn_mod_exp_fw_precompr2_st t k.BM.bn.BN.len ->
  bn_mod_exp_fw_st t k.BM.bn.BN.len


inline_for_extraction noextract
class exp (t:limb_t) = {
  mont: BM.mont t;
  exp_check: bn_check_mod_exp_st t mont.BM.bn.BN.len;
  raw_mod_exp_precomp: bn_mod_exp_raw_precompr2_st t mont.BM.bn.BN.len;
  ct_mod_exp_precomp: bn_mod_exp_ct_precompr2_st t mont.BM.bn.BN.len;
  raw_mod_exp_fw_precomp: bn_mod_exp_fw_precompr2_st t mont.BM.bn.BN.len;
  ct_mod_exp_fw_precomp: bn_mod_exp_fw_precompr2_st t mont.BM.bn.BN.len;
}

// A completely run-time-only instance where the functions above exist in the C code.
inline_for_extraction noextract
val mk_runtime_exp: #t:limb_t -> len:BN.meta_len t -> exp t

val mk_runtime_exp_len_lemma: #t:limb_t -> len:BN.meta_len t ->
  Lemma ((mk_runtime_exp #t len).mont.BM.bn.BN.len == len) [SMTPat (mk_runtime_exp #t len)]
