module Hacl.Bignum.Exponentiation

open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Mul

open Lib.IntTypes
open Lib.Buffer

module BN = Hacl.Bignum
module BM = Hacl.Bignum.Montgomery

open Hacl.Bignum.Definitions

module ST = FStar.HyperStack.ST
module LSeq = Lib.Sequence
module Loops = Lib.LoopCombinators

module S = Hacl.Spec.Bignum.Exponentiation
module BD = Hacl.Spec.Bignum.Definitions
module BN = Hacl.Bignum
module BM = Hacl.Bignum.Montgomery
module SM = Hacl.Spec.Bignum.Montgomery

module LE = Lib.Exponentiation
module BE = Hacl.Impl.Exponentiation

friend Hacl.Spec.Bignum.Exponentiation

#reset-options "--z3rlimit 50 --fuel 0 --ifuel 0"

let bn_check_mod_exp #t k n a bBits b =
  [@inline_let] let len = k.BM.bn.BN.len in
  let m0 = k.BM.mont_check n in
  let bLen = blocks bBits (size (bits t)) in
  let m1 = BN.bn_is_zero_mask bLen b in
  let m1' = lognot m1 in
  let m2 =
    if bBits <. size (bits t) *! bLen
    then BN.bn_lt_pow2_mask bLen b bBits
    else ones t SEC in
  let m3 = BN.bn_lt_mask len a n in
  let m = m1' &. m2 &. m3 in
  m0 &. m

//////////////////////////////////////////////////////////////

unfold
let a_spec
  (#t:limb_t)
  (#len:S.bn_len t)
  (n:BD.lbignum t len)
 =
  S.nat_mod_bn n


inline_for_extraction noextract
let exp_s
  (#t:limb_t)
  (#len:S.bn_len t)
  (n:BD.lbignum t len)
  (mu:limb t{SM.bn_mont_pre n mu})
  : LE.exp (a_spec n)
 =
  S.mk_nat_mont_group_bn n mu


unfold
let linv_ctx
  (#t:limb_t)
  (#len:S.bn_len t)
  (n:BD.lbignum t len)
  (a:BD.lbignum t len) : Type0
 =
  n == a


unfold
let linv
  (#t:limb_t)
  (#len:S.bn_len t)
  (n:BD.lbignum t len)
  (a:BD.lbignum t len) : Type0
 =
  BD.bn_v a < BD.bn_v n


unfold
let refl
  (#t:limb_t)
  (#len:S.bn_len t)
  (n:BD.lbignum t len)
  (a:BD.lbignum t len{linv n a}) : a_spec n
 =
  a


inline_for_extraction noextract
let mk_lexp_to_exp
  (t:limb_t)
  (len:BN.meta_len t)
  (n:BD.lbignum t (v len))
  (mu:limb t{SM.bn_mont_pre n mu}) : BE.lexp_to_exp t len len =
{
  BE.a_spec = a_spec n;
  BE.exp = exp_s n mu;
  BE.linv_ctx = linv_ctx n;
  BE.linv = linv n;
  BE.refl = refl n;
}


inline_for_extraction noextract
let bn_mont_one_st (t:limb_t) (len:BN.meta_len t) =
    n:lbignum t len
  -> mu:limb t
  -> r2:lbignum t len
  -> oneM:lbignum t len ->
  Stack unit
  (requires fun h ->
    live h n /\ live h r2 /\ live h oneM /\
    disjoint n r2 /\ disjoint n oneM /\ disjoint r2 oneM /\
    SM.bn_mont_pre (as_seq h n) mu /\
    bn_v h r2 == pow2 (2 * bits t * v len) % bn_v h n)
  (ensures  fun h0 _ h1 -> modifies (loc oneM) h0 h1 /\
    as_seq h1 oneM == S.bn_mont_one (as_seq h0 n) mu)


inline_for_extraction noextract
val bn_mont_one: #t:limb_t -> k:BM.mont t -> bn_mont_one_st t k.BM.bn.BN.len
let bn_mont_one #t k n mu r2 oneM =
  let h0 = ST.get () in
  let len = k.BM.bn.BN.len in
  BM.bn_mont_one k n mu r2 oneM;
  SM.bn_mont_one_lemma (as_seq h0 n) mu (as_seq h0 r2);
  SM.bn_precomp_r2_mod_n_lemma 0 (as_seq h0 n);
  BD.bn_eval_inj (v len) (SM.bn_precomp_r2_mod_n 0 (as_seq h0 n)) (as_seq h0 r2)


inline_for_extraction noextract
val bn_mont_mul:
    #t:limb_t
  -> k:BM.mont t
  -> n:Ghost.erased (BD.lbignum t (v k.BM.bn.BN.len))
  -> mu:limb t{SM.bn_mont_pre n mu}
  -> BE.lmul_st t k.BM.bn.BN.len k.BM.bn.BN.len (mk_lexp_to_exp t k.BM.bn.BN.len n mu)

let bn_mont_mul #t k n mu ctx aM bM resM =
  let h0 = ST.get () in
  let len = k.BM.bn.BN.len in
  SM.bn_mont_mul_lemma n mu (as_seq h0 aM) (as_seq h0 bM);
  k.BM.mul ctx mu aM bM resM


inline_for_extraction noextract
val bn_mont_sqr:
    #t:limb_t
  -> k:BM.mont t
  -> n:Ghost.erased (BD.lbignum t (v k.BM.bn.BN.len))
  -> mu:limb t{SM.bn_mont_pre n mu}
  -> BE.lsqr_st t k.BM.bn.BN.len k.BM.bn.BN.len (mk_lexp_to_exp t k.BM.bn.BN.len n mu)

let bn_mont_sqr #t k n mu ctx aM resM =
  let h0 = ST.get () in
  let len = k.BM.bn.BN.len in
  SM.bn_mont_sqr_lemma n mu (as_seq h0 aM);
  SM.bn_mont_mul_lemma n mu (as_seq h0 aM) (as_seq h0 aM);
  BD.bn_eval_inj #t (v len)
    (SM.bn_mont_mul n mu (as_seq h0 aM) (as_seq h0 aM))
    (SM.bn_mont_sqr n mu (as_seq h0 aM));
  k.BM.sqr ctx mu aM resM


inline_for_extraction noextract
let mk_lexp
  (t:limb_t)
  (k:BM.mont t)
  (n:Ghost.erased (BD.lbignum t (v k.BM.bn.BN.len)))
  (mu:limb t{SM.bn_mont_pre n mu}) : BE.lexp t k.BM.bn.BN.len k.BM.bn.BN.len =
{
  BE.to = mk_lexp_to_exp t k.BM.bn.BN.len n mu;
  BE.lmul = bn_mont_mul k n mu;
  BE.lsqr = bn_mont_sqr k n mu;
}

///////////////////////////////////////////////////////////////////////

let bn_mod_exp_raw_precompr2 #t k n a bBits b r2 res =
  let h0 = ST.get () in
  [@inline_let] let len = k.BM.bn.BN.len in
  push_frame ();
  let bLen = blocks bBits (size (bits t)) in
  let nInv = BM.mod_inv_limb n.(0ul) in // n * nInv = 1 (mod (pow2 64))
  Hacl.Spec.Bignum.ModInvLimb.bn_mod_inv_limb_lemma (as_seq h0 n);

  let aM   = create len (uint #t #SEC 0) in
  let accM = create len (uint #t #SEC 0) in
  BM.to n nInv r2 a aM;
  SM.bn_to_mont_lemma (as_seq h0 n) nInv (as_seq h0 r2) (as_seq h0 a);
  bn_mont_one k n nInv r2 accM;

  BE.lexp_rl len len (mk_lexp t k (as_seq h0 n) nInv) n aM bLen bBits b accM;

  BM.from n nInv accM res;
  pop_frame ()


let bn_mod_exp_ct_precompr2 #t k n a bBits b r2 res =
  let h0 = ST.get () in
  [@inline_let] let len = k.BM.bn.BN.len in
  push_frame ();
  let bLen = blocks bBits (size (bits t)) in
  let nInv = BM.mod_inv_limb n.(0ul) in // n * nInv = 1 (mod (pow2 64))
  Hacl.Spec.Bignum.ModInvLimb.bn_mod_inv_limb_lemma (as_seq h0 n);

  let aM   = create len (uint #t #SEC 0) in
  let accM = create len (uint #t #SEC 0) in
  BM.to n nInv r2 a aM;
  SM.bn_to_mont_lemma (as_seq h0 n) nInv (as_seq h0 r2) (as_seq h0 a);
  bn_mont_one k n nInv r2 accM;

  BE.lexp_mont_ladder_swap len len (mk_lexp t k (as_seq h0 n) nInv) n aM bLen bBits b accM;

  BM.from n nInv accM res;
  pop_frame ()


let bn_mod_exp_fw_raw_precompr2 #t k n a bBits b l r2 res =
  let h0 = ST.get () in
  [@inline_let] let len = k.BM.bn.BN.len in
  push_frame ();
  let bLen = blocks bBits (size (bits t)) in
  let nInv = BM.mod_inv_limb n.(0ul) in // n * nInv = 1 (mod (pow2 64))
  Hacl.Spec.Bignum.ModInvLimb.bn_mod_inv_limb_lemma (as_seq h0 n);

  let aM   = create len (uint #t #SEC 0) in
  let accM = create len (uint #t #SEC 0) in
  BM.to n nInv r2 a aM;
  SM.bn_to_mont_lemma (as_seq h0 n) nInv (as_seq h0 r2) (as_seq h0 a);
  bn_mont_one k n nInv r2 accM;

  BE.lexp_fw_raw len len (mk_lexp t k (as_seq h0 n) nInv) n aM bLen bBits b accM l;

  BM.from n nInv accM res;
  pop_frame ()


let bn_mod_exp_fw_ct_precompr2 #t k n a bBits b l r2 res =
  let h0 = ST.get () in
  [@inline_let] let len = k.BM.bn.BN.len in
  push_frame ();
  let bLen = blocks bBits (size (bits t)) in
  let nInv = BM.mod_inv_limb n.(0ul) in // n * nInv = 1 (mod (pow2 64))
  Hacl.Spec.Bignum.ModInvLimb.bn_mod_inv_limb_lemma (as_seq h0 n);

  let aM   = create len (uint #t #SEC 0) in
  let accM = create len (uint #t #SEC 0) in
  BM.to n nInv r2 a aM;
  SM.bn_to_mont_lemma (as_seq h0 n) nInv (as_seq h0 r2) (as_seq h0 a);
  bn_mont_one k n nInv r2 accM;

  BE.lexp_fw_ct len len (mk_lexp t k (as_seq h0 n) nInv) n aM bLen bBits b accM l;

  BM.from n nInv accM res;
  pop_frame ()



let bn_mod_exp_raw #t k bn_mod_exp_raw_precompr2 nBits n a bBits b res =
  let h0 = ST.get () in
  SM.bn_precomp_r2_mod_n_lemma (v nBits) (as_seq h0 n);
  [@inline_let] let len = k.BM.bn.BN.len in
  push_frame ();
  let r2 = create len (uint #t #SEC 0) in
  BM.precomp nBits n r2;
  bn_mod_exp_raw_precompr2 n a bBits b r2 res;
  pop_frame ()


let bn_mod_exp_ct #t k bn_mod_exp_ct_precompr2 nBits n a bBits b res =
  let h0 = ST.get () in
  SM.bn_precomp_r2_mod_n_lemma (v nBits) (as_seq h0 n);
  [@inline_let] let len = k.BM.bn.BN.len in
  push_frame ();
  let r2 = create len (uint #t #SEC 0) in
  BM.precomp nBits n r2;
  bn_mod_exp_ct_precompr2 n a bBits b r2 res;
  pop_frame ()


let bn_mod_exp_fw_raw #t k bn_mod_exp_fw_raw_precompr2 nBits n a bBits b l res =
  let h0 = ST.get () in
  SM.bn_precomp_r2_mod_n_lemma (v nBits) (as_seq h0 n);
  [@inline_let] let len = k.BM.bn.BN.len in
  push_frame ();
  let r2 = create len (uint #t #SEC 0) in
  BM.precomp nBits n r2;
  bn_mod_exp_fw_raw_precompr2 n a bBits b l r2 res;
  pop_frame ()


let bn_mod_exp_fw_ct #t k bn_mod_exp_fw_ct_precompr2 nBits n a bBits b l res =
  let h0 = ST.get () in
  SM.bn_precomp_r2_mod_n_lemma (v nBits) (as_seq h0 n);
  [@inline_let] let len = k.BM.bn.BN.len in
  push_frame ();
  let r2 = create len (uint #t #SEC 0) in
  BM.precomp nBits n r2;
  bn_mod_exp_fw_ct_precompr2 n a bBits b l r2 res;
  pop_frame ()


/// A fully runtime implementation of modular exponentiation.

[@CInline]
let bn_check_mod_exp_u32 (len:BN.meta_len U32) : bn_check_mod_exp_st U32 len =
  bn_check_mod_exp (BM.mk_runtime_mont len)
[@CInline]
let bn_mod_exp_raw_precompr2_u32 (len:BN.meta_len U32) : bn_mod_exp_raw_precompr2_st U32 len =
  bn_mod_exp_raw_precompr2 (BM.mk_runtime_mont len)
[@CInline]
let bn_mod_exp_ct_precompr2_u32 (len:BN.meta_len U32) : bn_mod_exp_ct_precompr2_st U32 len =
  bn_mod_exp_ct_precompr2 (BM.mk_runtime_mont len)
[@CInline]
let bn_mod_exp_fw_raw_precompr2_u32 (len:BN.meta_len U32) : bn_mod_exp_fw_precompr2_st U32 len =
  bn_mod_exp_fw_raw_precompr2 (BM.mk_runtime_mont len)
[@CInline]
let bn_mod_exp_fw_ct_precompr2_u32 (len:BN.meta_len U32) : bn_mod_exp_fw_precompr2_st U32 len =
  bn_mod_exp_fw_ct_precompr2 (BM.mk_runtime_mont len)

inline_for_extraction noextract
let mk_runtime_exp_u32 (len:BN.meta_len U32) : exp U32 = {
  mont = BM.mk_runtime_mont len;
  exp_check = bn_check_mod_exp_u32 len;
  raw_mod_exp_precomp = bn_mod_exp_raw_precompr2_u32 len;
  ct_mod_exp_precomp = bn_mod_exp_ct_precompr2_u32 len;
  raw_mod_exp_fw_precomp = bn_mod_exp_fw_raw_precompr2_u32 len;
  ct_mod_exp_fw_precomp = bn_mod_exp_fw_ct_precompr2_u32 len;
  }


[@CInline]
let bn_check_mod_exp_u64 (len:BN.meta_len U64) : bn_check_mod_exp_st U64 len =
  bn_check_mod_exp (BM.mk_runtime_mont len)
[@CInline]
let bn_mod_exp_raw_precompr2_u64 (len:BN.meta_len U64) : bn_mod_exp_raw_precompr2_st U64 len =
  bn_mod_exp_raw_precompr2 (BM.mk_runtime_mont len)
[@CInline]
let bn_mod_exp_ct_precompr2_u64 (len:BN.meta_len U64) : bn_mod_exp_ct_precompr2_st U64 len =
  bn_mod_exp_ct_precompr2 (BM.mk_runtime_mont len)
[@CInline]
let bn_mod_exp_fw_raw_precompr2_u64 (len:BN.meta_len U64) : bn_mod_exp_fw_precompr2_st U64 len =
  bn_mod_exp_fw_raw_precompr2 (BM.mk_runtime_mont len)
[@CInline]
let bn_mod_exp_fw_ct_precompr2_u64 (len:BN.meta_len U64) : bn_mod_exp_fw_precompr2_st U64 len =
  bn_mod_exp_fw_ct_precompr2 (BM.mk_runtime_mont len)

inline_for_extraction noextract
let mk_runtime_exp_u64 (len:BN.meta_len U64) : exp U64 = {
  mont = BM.mk_runtime_mont len;
  exp_check = bn_check_mod_exp_u64 len;
  raw_mod_exp_precomp = bn_mod_exp_raw_precompr2_u64 len;
  ct_mod_exp_precomp = bn_mod_exp_ct_precompr2_u64 len;
  raw_mod_exp_fw_precomp = bn_mod_exp_fw_raw_precompr2_u64 len;
  ct_mod_exp_fw_precomp = bn_mod_exp_fw_ct_precompr2_u64 len;
  }


let mk_runtime_exp (#t:limb_t) (len:BN.meta_len t) : exp t =
  match t with
  | U32 -> mk_runtime_exp_u32 len
  | U64 -> mk_runtime_exp_u64 len

let mk_runtime_exp_len_lemma #t len =
  BM.mk_runtime_mont_len_lemma #t len
