module Hacl.Spec.Bignum.Exponentiation

open FStar.Mul

open Lib.IntTypes
open Lib.Sequence

open Hacl.Spec.Bignum.Definitions

module BM = Hacl.Spec.Bignum.Montgomery

#reset-options "--z3rlimit 50 --fuel 0 --ifuel 0"


let bn_mod_exp_pre
  (#t:limb_t)
  (#nLen:size_pos{2 * bits t * nLen <= max_size_t})
  (n:lbignum t nLen)
  (a:lbignum t nLen)
  (bBits:size_pos)
  (b:lbignum t (blocks bBits (bits t)))
 =
   bn_v n % 2 = 1 /\ 1 < bn_v n /\
   0 < bn_v b /\ bn_v b < pow2 bBits /\ bn_v a < bn_v n


let bn_mod_exp_post
  (#t:limb_t)
  (#nLen:size_pos{2 * bits t * nLen <= max_size_t})
  (n:lbignum t nLen)
  (a:lbignum t nLen)
  (bBits:size_pos)
  (b:lbignum t (blocks bBits (bits t)))
  (res:lbignum t nLen)
 =
  bn_mod_exp_pre n a bBits b /\
  bn_v res == Lib.NatMod.pow_mod #(bn_v n) (bn_v a) (bn_v b)


val bn_check_mod_exp:
    #t:limb_t
  -> #nLen:size_pos{2 * bits t * nLen <= max_size_t}
  -> n:lbignum t nLen
  -> a:lbignum t nLen
  -> bBits:size_pos
  -> b:lbignum t (blocks bBits (bits t)) ->
  res:limb t{
    let b = bn_v n % 2 = 1 && 1 < bn_v n && 0 < bn_v b && bn_v b < pow2 bBits && bn_v a < bn_v n in
    v res == (if b then v (ones t SEC) else v (zeros t SEC))}


// This function is *NOT* constant-time on the exponent b
val bn_mod_exp_precompr2:
    #t:limb_t
  -> nLen:size_pos{2 * bits t * nLen <= max_size_t}
  -> n:lbignum t nLen
  -> a:lbignum t nLen
  -> bBits:size_pos
  -> b:lbignum t (blocks bBits (bits t))
  -> r2:lbignum t nLen ->
  lbignum t nLen


val bn_mod_exp_precompr2_lemma:
    #t:limb_t
  -> nLen:size_pos{2 * bits t * nLen <= max_size_t}
  -> n:lbignum t nLen
  -> a:lbignum t nLen
  -> bBits:size_pos
  -> b:lbignum t (blocks bBits (bits t))
  -> r2:lbignum t nLen -> Lemma
  (requires
    bn_mod_exp_pre n a bBits b /\
    bn_v r2 == pow2 (2 * bits t * nLen) % bn_v n)
  (ensures
    bn_mod_exp_post n a bBits b (bn_mod_exp_precompr2 nLen n a bBits b r2))


// This function is constant-time on the exponent b
val bn_mod_exp_mont_ladder_precompr2:
    #t:limb_t
  -> nLen:size_pos{2 * bits t * nLen <= max_size_t}
  -> n:lbignum t nLen
  -> a:lbignum t nLen
  -> bBits:size_pos
  -> b:lbignum t (blocks bBits (bits t))
  -> r2:lbignum t nLen ->
  lbignum t nLen


val bn_mod_exp_mont_ladder_precompr2_lemma:
    #t:limb_t
  -> nLen:size_pos{2 * bits t * nLen <= max_size_t}
  -> n:lbignum t nLen
  -> a:lbignum t nLen
  -> bBits:size_pos
  -> b:lbignum t (blocks bBits (bits t))
  -> r2:lbignum t nLen -> Lemma
  (requires
    bn_mod_exp_pre n a bBits b /\
    bn_v r2 == pow2 (2 * bits t * nLen) % bn_v n)
  (ensures
    bn_mod_exp_post n a bBits b (bn_mod_exp_mont_ladder_precompr2 nLen n a bBits b r2))


// This function is *NOT* constant-time on the exponent b
val bn_mod_exp:
    #t:limb_t
  -> nLen:size_pos{2 * bits t * nLen <= max_size_t}
  -> nBits:size_nat{nBits / bits t < nLen}
  -> n:lbignum t nLen
  -> a:lbignum t nLen
  -> bBits:size_pos
  -> b:lbignum t (blocks bBits (bits t)) ->
  lbignum t nLen


val bn_mod_exp_lemma:
    #t:limb_t
  -> nLen:size_pos{2 * bits t * nLen <= max_size_t}
  -> nBits:size_nat{nBits / bits t < nLen}
  -> n:lbignum t nLen
  -> a:lbignum t nLen
  -> bBits:size_pos
  -> b:lbignum t (blocks bBits (bits t)) -> Lemma
  (requires bn_mod_exp_pre n a bBits b /\ pow2 nBits < bn_v n)
  (ensures  bn_mod_exp_post n a bBits b (bn_mod_exp nLen nBits n a bBits b))


// This function is constant-time on the exponent b
val bn_mod_exp_mont_ladder:
    #t:limb_t
  -> nLen:size_pos{2 * bits t * nLen <= max_size_t}
  -> nBits:size_nat{nBits / bits t < nLen}
  -> n:lbignum t nLen
  -> a:lbignum t nLen
  -> bBits:size_pos
  -> b:lbignum t (blocks bBits (bits t)) ->
  lbignum t nLen


val bn_mod_exp_mont_ladder_lemma:
    #t:limb_t
  -> nLen:size_pos{2 * bits t * nLen <= max_size_t}
  -> nBits:size_nat{nBits / bits t < nLen}
  -> n:lbignum t nLen
  -> a:lbignum t nLen
  -> bBits:size_pos
  -> b:lbignum t (blocks bBits (bits t)) -> Lemma
  (requires bn_mod_exp_pre n a bBits b /\ pow2 nBits < bn_v n)
  (ensures  bn_mod_exp_post n a bBits b (bn_mod_exp_mont_ladder nLen nBits n a bBits b))
