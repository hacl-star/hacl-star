module Hacl.Bignum.GenericField

open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Mul

open Lib.IntTypes
open Lib.Buffer

open Hacl.Bignum.Definitions

module B = LowStar.Buffer
module HS = FStar.HyperStack
module ST = FStar.HyperStack.ST

module Euclid = FStar.Math.Euclid
module S = Hacl.Spec.Bignum.GenericField
module BE = Hacl.Bignum.Exponentiation
module IE = Hacl.Impl.Exponentiation
module BN = Hacl.Bignum
module BM = Hacl.Bignum.Montgomery

friend Hacl.Bignum.Exponentiation
friend Hacl.Spec.Bignum.GenericField

#set-options "--z3rlimit 50 --fuel 1 --ifuel 0"

let bn_field_get_len #t k _ =
  k.len


let bn_field_init #t km r nBits n =
  [@inline_let]
  let len = km.BM.bn.BN.len in
  let h0 = ST.get () in
  let r2 : buffer (limb t) = LowStar.Monotonic.Buffer.mmalloc r (uint #t #SEC 0) len in
  let n1 : buffer (limb t) = LowStar.Monotonic.Buffer.mmalloc r (uint #t #SEC 0) len in
  let h1 = ST.get () in
  B.(modifies_only_not_unused_in loc_none h0 h1);
  assert (B.length r2 == FStar.UInt32.v len);
  assert (B.length n1 == FStar.UInt32.v len);
  let r2 : lbignum t len = r2 in
  let n1 : lbignum t len = n1 in
  copy n1 n;

  km.BM.precomp (nBits -! 1ul) n r2;
  let mu = BM.mod_inv_limb n.(0ul) in
  let res : bn_mont_ctx t = { nBits = nBits; len = len; n = n1; mu = mu; r2 = r2 } in
  let h2 = ST.get () in
  assert (as_ctx h2 res == S.bn_field_init (v nBits) (as_seq h0 n));
  assert (S.bn_mont_ctx_inv (as_ctx h2 res));
  B.(modifies_only_not_unused_in loc_none h0 h2);
  res


let bn_to_field #t km k a aM =
  let h0 = ST.get () in
  km.BM.to k.n k.mu k.r2 a aM;
  let h1 = ST.get () in
  assert (as_seq h1 aM == S.bn_to_field (as_ctx h0 k) (as_seq h0 a))


let bn_from_field #t km k aM a =
  let h0 = ST.get () in
  km.BM.from k.n k.mu aM a;
  let h1 = ST.get () in
  assert (as_seq h1 a == S.bn_from_field (as_ctx h0 k) (as_seq h0 aM))


let bn_field_add #t km k aM bM cM =
  let h0 = ST.get () in
  km.BM.bn.BN.add_mod_n k.n aM bM cM;
  let h1 = ST.get () in
  assert (as_seq h1 cM == S.bn_field_add (as_ctx h0 k) (as_seq h0 aM) (as_seq h0 bM))


let bn_field_sub #t km k aM bM cM =
  let h0 = ST.get () in
  BN.bn_sub_mod_n k.len k.n aM bM cM;
  let h1 = ST.get () in
  assert (as_seq h1 cM == S.bn_field_sub (as_ctx h0 k) (as_seq h0 aM) (as_seq h0 bM))


let bn_field_mul #t km k aM bM cM =
  let h0 = ST.get () in
  km.BM.mul k.n k.mu aM bM cM;
  let h1 = ST.get () in
  assert (as_seq h1 cM == S.bn_field_mul (as_ctx h0 k) (as_seq h0 aM) (as_seq h0 bM))


let bn_field_sqr #t km k aM cM =
  let h0 = ST.get () in
  km.BM.sqr k.n k.mu aM cM;
  let h1 = ST.get () in
  assert (as_seq h1 cM == S.bn_field_sqr (as_ctx h0 k) (as_seq h0 aM))


let bn_field_one #t km k oneM =
  let h0 = ST.get () in
  BM.bn_mont_one km k.n k.mu k.r2 oneM;
  let h1 = ST.get () in
  assert (as_seq h1 oneM == S.bn_field_one (as_ctx h0 k))


let bn_field_inv #t km k aM aInvM =
  [@inline_let]
  let len = k.len in
  push_frame ();
  let n2 = create len (uint #t #SEC 0) in
  let c = BN.bn_sub1 len k.n (uint #t #SEC 2) n2 in
  let h0 = ST.get () in
  S.bn_field_inv_lemma (as_ctx h0 k) (as_seq h0 aM);
  Hacl.Spec.Bignum.bn_sub1_lemma (as_seq h0 (k.n <: lbignum t len)) (uint #t #SEC 2);
  Hacl.Spec.Bignum.Definitions.bn_eval_bound (as_seq h0 n2) (v len);
  Hacl.Spec.Bignum.Definitions.bn_eval_bound (as_seq h0 (k.n <: lbignum t len)) (v len);
  BE.bn_mont_one km k.n k.mu k.r2 aInvM;
  IE.lexp_fw_vartime len len (BE.mk_lexp t km ((as_ctx h0 k).S.n) k.mu) k.n aM len k.nBits n2 aInvM 4ul;
  let h1 = ST.get () in
  assert (bn_v h0 n2 == bn_v #t #k.len h0 k.n - 2);
  assert (as_seq h1 aInvM ==
    Lib.Exponentiation.exp_fw
    (Hacl.Spec.Bignum.Exponentiation.mk_bn_mont_comm_monoid ((as_ctx h0 k).S.n) k.mu)
    (as_seq h0 aM) (v k.nBits) (bn_v #t #k.len h0 k.n - 2) 4);

  norm_spec [delta_only [`%S.bn_field_inv]] (S.bn_field_inv (as_ctx h0 k) (as_seq h0 aM));
  assert (as_seq h1 aInvM == S.bn_field_inv (as_ctx h0 k) (as_seq h0 aM));
  pop_frame ()
