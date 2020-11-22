module Hacl.Impl.Curve25519.Field64.Hacl

open FStar.HyperStack
open FStar.HyperStack.All
open FStar.Mul

open Lib.Sequence
open Lib.IntTypes
open Lib.Buffer

module B = Lib.Buffer
module ST = FStar.HyperStack.ST
module BSeq = Lib.ByteSequence
module LSeq = Lib.Sequence

module CD = Hacl.Spec.Curve25519.Field64.Definition
module CC = Hacl.Spec.Curve25519.Field64.Core

module BN = Hacl.Bignum
module BD = Hacl.Bignum.Definitions
module SB = Hacl.Spec.Bignum
module SD = Hacl.Spec.Bignum.Definitions

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"


[@CInline]
let add1_ out f1 f2 =
  let h0 = ST.get () in
  let c = BN.bn_add1 4ul f1 f2 out in
  let h1 = ST.get () in
  assert (let c1, r1 = CC.add1 (as_seq h0 f1) f2 in c == c1 /\ as_seq h1 out == r1);
  CD.bn_v_is_as_nat (as_seq h0 f1);
  CD.bn_v_is_as_nat (as_seq h1 out);
  c


[@CInline]
let fadd_ out f1 f2 =
  let h0 = ST.get () in
  let c0 = BN.bn_add_eq_len 4ul f1 f2 out in
  let c = BN.bn_add1 4ul out (c0 *. u64 38) out in
  out.(0ul) <- out.(0ul) +. c *. u64 38;
  let h1 = ST.get () in
  assert (as_seq h1 out == CC.fadd4 (as_seq h0 f1) (as_seq h0 f2));
  CD.bn_v_is_as_nat (as_seq h0 f1);
  CD.bn_v_is_as_nat (as_seq h0 f2);
  CD.bn_v_is_as_nat (as_seq h1 out)


[@CInline]
let fsub_ out f1 f2 =
  let h0 = ST.get () in
  let c0 = BN.bn_sub_eq_len 4ul f1 f2 out in
  let c = BN.bn_sub1 4ul out (c0 *! u64 38) out in
  out.(0ul) <- out.(0ul) -. c *. u64 38;
  let h1 = ST.get () in
  assert (as_seq h1 out == CC.fsub4 (as_seq h0 f1) (as_seq h0 f2));
  CD.bn_v_is_as_nat (as_seq h0 f1);
  CD.bn_v_is_as_nat (as_seq h0 f2);
  CD.bn_v_is_as_nat (as_seq h1 out)


[@CInline]
let fmul_ out f1 f2 tmp =
  let h0 = ST.get () in
  let tmp0 = sub tmp 0ul 8ul in
  BN.bn_mul 4ul 4ul f1 f2 tmp0;
  let c0 = BN.bn_mul1_lshift_add_in_place 4ul (sub tmp0 4ul 4ul) (u64 38) 4ul 0ul (sub tmp0 0ul 4ul) in
  let c = BN.bn_add1 4ul (sub tmp0 0ul 4ul) (c0 *. u64 38) out in
  out.(0ul) <- out.(0ul) +. c *. u64 38;
  let h1 = ST.get () in
  assert (as_seq h1 out == CC.fmul4 (as_seq h0 f1) (as_seq h0 f2));
  CD.bn_v_is_as_nat (as_seq h0 f1);
  CD.bn_v_is_as_nat (as_seq h0 f2);
  CD.bn_v_is_as_nat (as_seq h1 out)


[@CInline]
let fmul2_ out f1 f2 tmp =
  let out1 = B.sub out 0ul 4ul in
  let out2 = B.sub out 4ul 4ul in
  let f11 = B.sub f1 0ul 4ul in
  let f12 = B.sub f1 4ul 4ul in
  let f21 = B.sub f2 0ul 4ul in
  let f22 = B.sub f2 4ul 4ul in
  fmul_ out1 f11 f21 tmp;
  fmul_ out2 f12 f22 tmp


[@CInline]
let fmul1_ out f1 f2 =
  let h0 = ST.get () in
  let c0 = BN.bn_mul1 4ul f1 f2 out in
  let c = BN.bn_add1 4ul out (c0 *. u64 38) out in
  out.(0ul) <- out.(0ul) +. c *. u64 38;
  let h1 = ST.get () in
  assert (as_seq h1 out == CC.fmul14 (as_seq h0 f1) f2);
  CD.bn_v_is_as_nat (as_seq h0 f1);
  CD.bn_v_is_as_nat (as_seq h1 out)


[@CInline]
let fsqr_ out f1 tmp =
  let h0 = ST.get () in
  BN.bn_sqr 4ul f1 tmp;
  SB.bn_sqr_lemma (as_seq h0 f1);
  let c0 = BN.bn_mul1_lshift_add_in_place 4ul (sub tmp 4ul 4ul) (u64 38) 4ul 0ul (sub tmp 0ul 4ul) in
  let c = BN.bn_add1 4ul (sub tmp 0ul 4ul) (c0 *. u64 38) out in
  out.(0ul) <- out.(0ul) +. c *. u64 38;
  let h1 = ST.get () in
  assert (as_seq h1 out == CC.fsqr4 (as_seq h0 f1));
  CD.bn_v_is_as_nat (as_seq h0 f1);
  CD.bn_v_is_as_nat (as_seq h1 out)


[@CInline]
let fsqr2_ out f tmp =
  let out1 = B.sub out 0ul 4ul in
  let out2 = B.sub out 4ul 4ul in
  let f1 = B.sub f 0ul 4ul in
  let f2 = B.sub f 4ul 4ul in
  fmul_ out1 f1 f1 tmp;
  fmul_ out2 f2 f2 tmp


[@CInline]
let cswap2_ bit p1 p2 =
  let h0 = ST.get () in
  let mask = u64 0 -. bit in

  [@ inline_let]
  let inv h1 (i:nat{i <= 8}) =
    (forall (k:nat{k < i}).
      if v bit = 1
      then (as_seq h1 p1).[k] == (as_seq h0 p2).[k] /\ (as_seq h1 p2).[k] == (as_seq h0 p1).[k]
      else (as_seq h1 p1).[k] == (as_seq h0 p1).[k] /\ (as_seq h1 p2).[k] == (as_seq h0 p2).[k]) /\
    (forall (k:nat{i <= k /\ k < 8}).
      (as_seq h1 p1).[k] == (as_seq h0 p1).[k] /\ (as_seq h1 p2).[k] == (as_seq h0 p2).[k]) /\
    modifies (loc p1 |+| loc p2) h0 h1 in

  Lib.Loops.for 0ul 8ul inv
    (fun i ->
      let dummy = mask &. (p1.(i) ^. p2.(i)) in
      p1.(i) <- p1.(i) ^. dummy;
      p2.(i) <- p2.(i) ^. dummy;
      Hacl.Spec.Bignum.Lib.lemma_cswap2_step bit ((as_seq h0 p1).[v i]) ((as_seq h0 p2).[v i])
    );
  let h1 = ST.get () in
  assert (if v bit = 1 then (eq_intro (as_seq h1 p1) (as_seq h0 p2); as_seq h1 p1 == as_seq h0 p2)
    else (eq_intro (as_seq h1 p1) (as_seq h0 p1); as_seq h1 p1 == as_seq h0 p1));
  assert (if v bit = 1 then (eq_intro (as_seq h1 p2) (as_seq h0 p1); as_seq h1 p2 == as_seq h0 p1)
    else (eq_intro (as_seq h1 p2) (as_seq h0 p2); as_seq h1 p2 == as_seq h0 p2))
