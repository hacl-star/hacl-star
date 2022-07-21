module Hacl.Bignum.MontExponentiation

open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Mul

open Lib.IntTypes
open Lib.Buffer

open Hacl.Bignum.Definitions

module ST = FStar.HyperStack.ST
module LSeq = Lib.Sequence

module BD = Hacl.Spec.Bignum.Definitions
module SN = Hacl.Spec.Bignum
module SM = Hacl.Spec.Bignum.Montgomery

module BN = Hacl.Bignum
module BM = Hacl.Bignum.Montgomery

module LE = Lib.Exponentiation
module SE = Spec.Exponentiation
module BE = Hacl.Impl.Exponentiation
module E = Hacl.Spec.Exponentiation.Lemmas

module S = Hacl.Spec.Bignum.MontExponentiation

#reset-options "--z3rlimit 50 --fuel 0 --ifuel 0"

// All operations are performed in the Montgomery domain!

inline_for_extraction noextract
let linv (#t:limb_t) (#len:SN.bn_len t) (n:BD.lbignum t len) (a:BD.lbignum t len) : Type0 =
  BD.bn_v a < BD.bn_v n

inline_for_extraction noextract
let refl (#t:limb_t) (#len:SN.bn_len t) (n:BD.lbignum t len) (a:BD.lbignum t len{linv n a}) : S.bn_mont_t n =
  a

inline_for_extraction noextract
let linv_ctx (#t:limb_t) (#len:SN.bn_len t) (n:BD.lbignum t len) (a:BD.lbignum t len) : Type0 =
  n == a


inline_for_extraction noextract
let mk_to_bn_mont_ll_concr_ops
  (t:limb_t)
  (len:BN.meta_len t)
  (n:BD.lbignum t (v len))
  (mu:limb t{SM.bn_mont_pre n mu})
  : BE.to_concrete_ops t len len =
{
  BE.t_spec = S.bn_mont_t n;
  BE.concr_ops = S.mk_bn_mont_concrete_ops n mu;
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
    as_seq h1 oneM == S.bn_mont_one (as_seq h0 n) mu ())


inline_for_extraction noextract
val bn_mont_one: #t:limb_t -> k:BM.mont t -> bn_mont_one_st t k.BM.bn.BN.len
let bn_mont_one #t k n mu r2 oneM =
  let h0 = ST.get () in
  BM.bn_mont_one k.BM.bn.BN.len k.BM.from n mu r2 oneM;
  SM.bn_precomp_r2_mod_n_lemma 0 (as_seq h0 n);
  BD.bn_eval_inj (v k.BM.bn.BN.len) (SM.bn_precomp_r2_mod_n 0 (as_seq h0 n)) (as_seq h0 r2)


inline_for_extraction noextract
val bn_mont_mul:
    #t:limb_t
  -> k:BM.mont t
  -> n:Ghost.erased (BD.lbignum t (v k.BM.bn.BN.len))
  -> mu:limb t{SM.bn_mont_pre n mu} ->
  BE.lmul_st t k.BM.bn.BN.len k.BM.bn.BN.len (mk_to_bn_mont_ll_concr_ops t k.BM.bn.BN.len n mu)

let bn_mont_mul #t k n mu ctx aM bM resM =
  let h0 = ST.get () in
  SM.bn_mont_mul_lemma n mu (as_seq h0 aM) (as_seq h0 bM);
  k.BM.mul ctx mu aM bM resM


inline_for_extraction noextract
val bn_mont_sqr:
    #t:limb_t
  -> k:BM.mont t
  -> n:Ghost.erased (BD.lbignum t (v k.BM.bn.BN.len))
  -> mu:limb t{SM.bn_mont_pre n mu} ->
  BE.lsqr_st t k.BM.bn.BN.len k.BM.bn.BN.len (mk_to_bn_mont_ll_concr_ops t k.BM.bn.BN.len n mu)

let bn_mont_sqr #t k n mu ctx aM resM =
  let h0 = ST.get () in
  SM.bn_mont_sqr_lemma n mu (as_seq h0 aM);
  SM.bn_mont_mul_lemma n mu (as_seq h0 aM) (as_seq h0 aM);
  k.BM.sqr ctx mu aM resM


inline_for_extraction noextract
let mk_bn_mont_concrete_ops
  (t:limb_t)
  (k:BM.mont t)
  (n:Ghost.erased (BD.lbignum t (v k.BM.bn.BN.len)))
  (mu:limb t{SM.bn_mont_pre n mu}) : BE.concrete_ops t k.BM.bn.BN.len k.BM.bn.BN.len =
{
  BE.to = mk_to_bn_mont_ll_concr_ops t k.BM.bn.BN.len n mu;
  BE.lmul = bn_mont_mul k n mu;
  BE.lsqr = bn_mont_sqr k n mu;
}

///////////////////////////////////////////////////////////////////////

noextract
let bn_exp_mont_pre
  (#t:limb_t)
  (#len:SN.bn_len t)
  (n:BD.lbignum t len)
  (mu:limb t)
  (r2:BD.lbignum t len)
  (aM:BD.lbignum t len)
  (bBits:size_nat)
  (b:BD.lbignum t (BD.blocks0 bBits (bits t)))
 =
   SM.bn_mont_pre n mu /\
   BD.bn_v r2 == pow2 (2 * bits t * len) % BD.bn_v n /\
   BD.bn_v b < pow2 bBits /\
   BD.bn_v aM < BD.bn_v n


inline_for_extraction noextract
let bn_exp_mont_st (t:limb_t) (len:BN.meta_len t) =
    n:lbignum t len
  -> mu:limb t
  -> r2:lbignum t len
  -> aM:lbignum t len
  -> bBits:size_t
  -> b:lbignum t (blocks0 bBits (size (bits t)))
  -> resM:lbignum t len ->
  Stack unit
  (requires fun h ->
    live h n /\ live h aM /\ live h b /\ live h resM /\ live h r2 /\
    disjoint resM aM /\ disjoint resM b /\ disjoint resM n /\ disjoint n aM /\
    disjoint resM r2 /\ disjoint aM r2 /\ disjoint n r2 /\ disjoint aM b /\

    bn_exp_mont_pre (as_seq h n) mu (as_seq h r2) (as_seq h aM) (v bBits) (as_seq h b))
  (ensures  fun h0 _ h1 -> modifies (loc aM |+| loc resM) h0 h1 /\
   (let k1 = E.mk_nat_mont_ll_comm_monoid (bits t) (v len) (bn_v h0 n) (v mu) in
    bn_v h1 resM == LE.pow k1 (bn_v h0 aM) (bn_v h0 b)))


// This function is *NOT* constant-time on the exponent b.
inline_for_extraction noextract
val bn_exp_mont_bm_vartime: #t:limb_t -> k:BM.mont t -> bn_exp_mont_st t k.BM.bn.BN.len
let bn_exp_mont_bm_vartime #t k n mu r2 aM bBits b resM =
  [@inline_let] let len = k.BM.bn.BN.len in
  let h0 = ST.get () in
  let k1 = Ghost.hide (E.mk_nat_mont_ll_comm_monoid (bits t) (v len) (bn_v h0 n) (v mu)) in

  [@inline_let] let bLen = blocks0 bBits (size (bits t)) in
  bn_mont_one k n mu r2 resM;
  BE.lexp_rl_vartime len len (mk_bn_mont_concrete_ops t k (as_seq h0 n) mu) n aM bLen bBits b resM;
  SE.exp_rl_lemma (S.mk_bn_mont_concrete_ops (as_seq h0 n) mu) (as_seq h0 aM) (v bBits) (bn_v h0 b);
  LE.exp_rl_lemma k1 (bn_v h0 aM) (v bBits) (bn_v h0 b)


// This function is constant-time on the exponent b.
inline_for_extraction noextract
val bn_exp_mont_bm_consttime: #t:limb_t -> k:BM.mont t -> bn_exp_mont_st t k.BM.bn.BN.len
let bn_exp_mont_bm_consttime #t k n mu r2 aM bBits b resM =
  [@inline_let] let len = k.BM.bn.BN.len in
  let h0 = ST.get () in
  let k1 = Ghost.hide (E.mk_nat_mont_ll_comm_monoid (bits t) (v len) (bn_v h0 n) (v mu)) in

  [@inline_let] let bLen = blocks0 bBits (size (bits t)) in
  bn_mont_one k n mu r2 resM;
  BE.lexp_mont_ladder_swap_consttime len len (mk_bn_mont_concrete_ops t k (as_seq h0 n) mu) n aM bLen bBits b resM;
  SE.exp_mont_ladder_swap_lemma (S.mk_bn_mont_concrete_ops (as_seq h0 n) mu) (as_seq h0 aM) (v bBits) (bn_v h0 b);
  LE.exp_mont_ladder_swap_lemma k1 (bn_v h0 aM) (v bBits) (bn_v h0 b);
  LE.exp_mont_ladder_lemma k1 (bn_v h0 aM) (v bBits) (bn_v h0 b)


// This function is *NOT* constant-time on the exponent b.
inline_for_extraction noextract
val bn_exp_mont_fw_vartime:
    #t:limb_t
  -> k:BM.mont t
  -> l:size_t{0 < v l /\ v l < bits U32 /\ pow2 (v l) * v k.BM.bn.BN.len <= max_size_t} ->
  bn_exp_mont_st t k.BM.bn.BN.len

let bn_exp_mont_fw_vartime #t k l n mu r2 aM bBits b resM =
  [@inline_let] let len = k.BM.bn.BN.len in
  let h0 = ST.get () in
  let k1 = Ghost.hide (E.mk_nat_mont_ll_comm_monoid (bits t) (v len) (bn_v h0 n) (v mu)) in

  let bLen = blocks0 bBits (size (bits t)) in
  bn_mont_one k n mu r2 resM;
  BE.lexp_fw_vartime len len (mk_bn_mont_concrete_ops t k (as_seq h0 n) mu) n aM bLen bBits b resM l;
  SE.exp_fw_lemma (S.mk_bn_mont_concrete_ops (as_seq h0 n) mu) (as_seq h0 aM) (v bBits) (bn_v h0 b) (v l);
  LE.exp_fw_lemma k1 (bn_v h0 aM) (v bBits) (bn_v h0 b) (v l)


// This function is constant-time on the exponent b.
inline_for_extraction noextract
val bn_exp_mont_fw_consttime:
    #t:limb_t
  -> k:BM.mont t
  -> l:size_t{0 < v l /\ v l < bits U32 /\ pow2 (v l) * v k.BM.bn.BN.len <= max_size_t} ->
  bn_exp_mont_st t k.BM.bn.BN.len

let bn_exp_mont_fw_consttime #t k l n mu r2 aM bBits b resM =
  [@inline_let] let len = k.BM.bn.BN.len in
  let h0 = ST.get () in
  let k1 = Ghost.hide (E.mk_nat_mont_ll_comm_monoid (bits t) (v len) (bn_v h0 n) (v mu)) in

  let bLen = blocks0 bBits (size (bits t)) in
  bn_mont_one k n mu r2 resM;
  BE.lexp_fw_consttime len len (mk_bn_mont_concrete_ops t k (as_seq h0 n) mu) n aM bLen bBits b resM l;
  SE.exp_fw_lemma (S.mk_bn_mont_concrete_ops (as_seq h0 n) mu) (as_seq h0 aM) (v bBits) (bn_v h0 b) (v l);
  LE.exp_fw_lemma k1 (bn_v h0 aM) (v bBits) (bn_v h0 b) (v l)


///////////////////////////////////////////////

// This function is *NOT* constant-time on the exponent b.
inline_for_extraction noextract
val bn_exp_mont_vartime: #t:limb_t -> k:BM.mont t -> bn_exp_mont_st t k.BM.bn.BN.len
let bn_exp_mont_vartime #t k n mu r2 aM bBits b resM =
  if bBits <. size S.bn_exp_mont_vartime_threshold then
    bn_exp_mont_bm_vartime k n mu r2 aM bBits b resM
  else
    bn_exp_mont_fw_vartime k 4ul n mu r2 aM bBits b resM


// This function is constant-time on the exponent b.
inline_for_extraction noextract
val bn_exp_mont_consttime: #t:limb_t -> k:BM.mont t -> bn_exp_mont_st t k.BM.bn.BN.len
let bn_exp_mont_consttime #t k n mu r2 aM bBits b resM =
  if bBits <. size S.bn_exp_mont_consttime_threshold then
    bn_exp_mont_bm_consttime k n mu r2 aM bBits b resM
  else
    bn_exp_mont_fw_consttime k 4ul n mu r2 aM bBits b resM
