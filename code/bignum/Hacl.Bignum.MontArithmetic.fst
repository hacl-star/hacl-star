module Hacl.Bignum.MontArithmetic

open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Mul

open Lib.IntTypes
open Lib.Buffer

open Hacl.Bignum.Definitions

module B = LowStar.Buffer
module HS = FStar.HyperStack
module ST = FStar.HyperStack.ST

module S = Hacl.Spec.Bignum.MontArithmetic
module BD = Hacl.Spec.Bignum.Definitions
module BB = Hacl.Bignum.Base
module BL = Hacl.Bignum.Lib

module ME = Hacl.Bignum.MontExponentiation
module BE = Hacl.Bignum.Exponentiation
module BN = Hacl.Bignum
module BM = Hacl.Bignum.Montgomery
module BI = Hacl.Bignum.ModInv

friend Hacl.Spec.Bignum.MontArithmetic

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

let bn_field_get_len #t k _ =
  k.len


let bn_field_check_modulus #t km n =
  let m = km.BM.mont_check n in
  BB.unsafe_bool_of_limb m


let bn_field_init #t km r n =
  [@inline_let]
  let len = km.BM.bn.BN.len in
  let h0 = ST.get () in
  let r2 : buffer (limb t) = B.mmalloc r (uint #t #SEC 0) len in
  let n1 : buffer (limb t) = B.mmalloc r (uint #t #SEC 0) len in
  let h1 = ST.get () in
  B.(modifies_only_not_unused_in loc_none h0 h1);
  assert (B.length r2 == FStar.UInt32.v len);
  assert (B.length n1 == FStar.UInt32.v len);
  let r2 : lbignum t len = r2 in
  let n1 : lbignum t len = n1 in

  if bn_field_check_modulus km n then begin
    copy n1 n;

    let nBits = size (bits t) *! BB.unsafe_size_from_limb (BL.bn_get_top_index len n) in
    km.BM.precomp nBits n r2;

    let mu = BM.mod_inv_limb n.(0ul) in
    let res : bn_mont_ctx t = { len = len; n = n1; mu = mu; r2 = r2 } in
    let h2 = ST.get () in
    assert (as_ctx h2 res == S.bn_field_init (as_seq h0 n));
    assert (S.bn_mont_ctx_inv (as_ctx h2 res));
    B.(modifies_only_not_unused_in loc_none h0 h2);
    res end
  else begin
    let mu = uint #t #SEC 0 in
    let res : bn_mont_ctx t = { len = len; n = n1; mu = mu; r2 = r2 } in
    let h2 = ST.get () in
    B.(modifies_only_not_unused_in loc_none h0 h2);
    res end


let bn_field_free #t k =
  let n : buffer (limb t) = k.n in
  let r2 : buffer (limb t) = k.r2 in
  B.free n;
  B.freeable_disjoint n r2;
  B.free r2


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


let bn_field_exp_consttime #t km k aM bBits b resM =
  push_frame ();
  let aMc = create k.len (uint #t #SEC 0) in
  copy aMc aM;
  ME.bn_exp_mont_consttime #t km k.n k.mu k.r2 aMc bBits b resM;
  let h0 = ST.get () in
  assert (bn_v h0 aM < bn_v #t #k.len h0 k.n);
  BD.bn_eval_inj (v k.len)
    (S.bn_field_exp_consttime (as_ctx h0 k) (as_seq h0 aM) (v bBits) (as_seq h0 b))
    (as_seq h0 resM);
  pop_frame ()


let bn_field_exp_vartime #t km k aM bBits b resM =
  push_frame ();
  let aMc = create k.len (uint #t #SEC 0) in
  copy aMc aM;
  ME.bn_exp_mont_vartime #t km k.n k.mu k.r2 aMc bBits b resM;
  let h0 = ST.get () in
  assert (bn_v h0 aM < bn_v #t #k.len h0 k.n);
  BD.bn_eval_inj (v k.len)
    (S.bn_field_exp_vartime (as_ctx h0 k) (as_seq h0 aM) (v bBits) (as_seq h0 b))
    (as_seq h0 resM);
  pop_frame ()


let bn_field_inv #t k bn_field_exp_vartime aM aInvM =
  [@inline_let]
  let len = k.len in
  push_frame ();
  let n2 = create len (uint #t #SEC 0) in
  BI.bn_mod_inv_prime_n2 len k.n n2;
  bn_field_exp_vartime aM (k.len *! size (bits t)) n2 aInvM;
  pop_frame ()
