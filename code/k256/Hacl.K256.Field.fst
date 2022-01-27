module Hacl.K256.Field

open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Mul

open Lib.IntTypes
open Lib.Buffer
open Lib.ByteBuffer

module ST = FStar.HyperStack.ST
module LSeq = Lib.Sequence
module BSeq = Lib.ByteSequence

module S = Spec.K256

module BI = Hacl.Spec.K256.Field52
module BL = Hacl.Spec.K256.Field52.Lemmas
module BDL = Hacl.Spec.K256.Field52.Definitions.Lemmas

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

let make_u64_4 out (f0,f1,f2,f3) =
  out.(0ul) <- f3;
  out.(1ul) <- f2;
  out.(2ul) <- f1;
  out.(3ul) <- f0


let make_u52_5 out (f0,f1,f2,f3,f4) =
  out.(0ul) <- f0;
  out.(1ul) <- f1;
  out.(2ul) <- f2;
  out.(3ul) <- f3;
  out.(4ul) <- f4


let make_prime_k256 () =
  [@inline_let]
  let r =
   (u64 0xffffefffffc2f,
    u64 0xfffffffffffff,
    u64 0xfffffffffffff,
    u64 0xfffffffffffff,
    u64 0xffffffffffff) in

  assert_norm (as_nat5 r = S.prime);
  assert_norm (0xffffffffffff <= max48);
  assert_norm (0xfffffffffffff <= max52);
  r


let make_order_k256 () =
  [@inline_let]
  let r =
   (u64 0x25e8cd0364141,
    u64 0xe6af48a03bbfd,
    u64 0xffffffebaaedc,
    u64 0xfffffffffffff,
    u64 0xffffffffffff) in

  assert_norm (as_nat5 r = S.q);
  assert_norm (0xffffffffffff <= max48);
  assert_norm (0xfffffffffffff <= max52);
  r


let make_b_k256 () =
  [@inline_let]
  let r = (u64 0x7, u64 0, u64 0, u64 0, u64 0) in
  assert_norm (as_nat5 r = S.b);
  r


[@CInline]
let is_felem_zero_vartime f =
  let h0 = ST.get () in
  BL.is_felem_zero_vartime5_lemma (as_felem5 h0 f);
  BI.is_felem_zero_vartime5 (f.(0ul), f.(1ul), f.(2ul), f.(3ul), f.(4ul))


[@CInline]
let is_felem_eq_vartime f1 f2 =
  let h0 = ST.get () in
  BL.is_felem_eq_vartime5_lemma (as_felem5 h0 f1) (as_felem5 h0 f2);
  BI.is_felem_eq_vartime5
    (f1.(0ul), f1.(1ul), f1.(2ul), f1.(3ul), f1.(4ul))
    (f2.(0ul), f2.(1ul), f2.(2ul), f2.(3ul), f2.(4ul))


[@CInline]
let is_felem_lt_prime_minus_order_vartime f =
  let h0 = ST.get () in
  BL.is_felem_lt_prime_minus_order_vartime5_lemma (as_felem5 h0 f);
  BI.is_felem_lt_prime_minus_order_vartime5 (f.(0ul), f.(1ul), f.(2ul), f.(3ul), f.(4ul))


let create_felem () =
  create nlimb (u64 0)


[@CInline]
let load_felem f b =
  push_frame ();
  let tmp = create 4ul (u64 0) in
  let h0 = ST.get () in
  uints_from_bytes_be tmp b;
  let h1 = ST.get () in
  assert (as_seq h1 tmp == BSeq.uints_from_bytes_be (as_seq h0 b));
  BSeq.uints_from_bytes_be_nat_lemma #U64 #_ #4 (as_seq h0 b);
  assert (BSeq.nat_from_intseq_be (BSeq.uints_from_bytes_be #U64 #_ #4 (as_seq h0 b)) == BSeq.nat_from_bytes_be (as_seq h0 b));
  BDL.unfold_nat_from_uint64_four (as_seq h1 tmp);
  assert (BSeq.nat_from_intseq_be (as_seq h1 tmp) == as_nat4 (as_felem4 h1 tmp));
  BL.load_felem5_lemma (as_felem4 h1 tmp);
  make_u52_5 f (BI.load_felem5 (tmp.(3ul),tmp.(2ul),tmp.(1ul),tmp.(0ul)));
  let h2 = ST.get () in
  assert (as_nat4 (as_felem4 h1 tmp) == as_nat5 (as_felem5 h2 f));
  pop_frame ()


[@CInline]
let load_felem_vartime f b =
  load_felem f b;
  let h0 = ST.get () in
  let is_ge_p = BI.is_felem_ge_prime_vartime5 (f.(0ul),f.(1ul),f.(2ul),f.(3ul),f.(4ul)) in
  BL.is_felem_ge_prime_vartime5_lemma (as_felem5 h0 f);
  if is_ge_p then false
  else not (is_felem_zero_vartime f)


[@CInline]
let store_felem b f =
  push_frame ();
  let tmp = create 4ul (u64 0) in
  let h0 = ST.get () in
  make_u64_4 tmp (BI.store_felem5 (f.(0ul),f.(1ul),f.(2ul),f.(3ul),f.(4ul)));
  let h1 = ST.get () in
  BL.store_felem5_lemma (as_felem5 h0 f);
  assert (as_nat4 (as_felem4 h1 tmp) == as_nat5 (as_felem5 h0 f));
  BDL.unfold_nat_from_uint64_four (as_seq h1 tmp);
  BSeq.lemma_nat_from_to_intseq_be_preserves_value 4 (as_seq h1 tmp);
  assert (BSeq.nat_to_intseq_be 4 (BSeq.nat_from_intseq_be (as_seq h1 tmp)) == as_seq h1 tmp);
  assert (BSeq.nat_to_intseq_be 4 (as_nat5 (as_felem5 h0 f)) == as_seq h1 tmp);
  uints_to_bytes_be 4ul b tmp;
  let h2 = ST.get () in
  assert (as_seq h2 b == BSeq.uints_to_bytes_be (as_seq h1 tmp));
  assert (as_seq h2 b == BSeq.uints_to_bytes_be #_ #_ #4 (BSeq.nat_to_intseq_be #U64 4 (as_nat5 (as_felem5 h0 f))));
  BSeq.uints_to_bytes_be_nat_lemma #U64 #SEC 4 (as_nat5 (as_felem5 h0 f));
  pop_frame ()


let set_zero f =
  memset f (u64 0) nlimb;
  let h = ST.get () in
  assert (as_seq h f == LSeq.create (v nlimb) (u64 0))


let set_one f =
  set_zero f;
  f.(0ul) <- u64 1

// not used
let copy_felem f1 f2 = copy f1 f2


[@CInline]
let fmul_small_num out f num =
  make_u52_5 out (BI.mul15 (f.(0ul), f.(1ul), f.(2ul), f.(3ul), f.(4ul)) num)

[@CInline]
let fadd out f1 f2 =
  make_u52_5 out (BI.add5
    (f1.(0ul), f1.(1ul), f1.(2ul), f1.(3ul), f1.(4ul))
    (f2.(0ul), f2.(1ul), f2.(2ul), f2.(3ul), f2.(4ul)))


[@CInline]
let fsub out f1 f2 x =
  make_u52_5 out (BI.fsub5
    (f1.(0ul), f1.(1ul), f1.(2ul), f1.(3ul), f1.(4ul))
    (f2.(0ul), f2.(1ul), f2.(2ul), f2.(3ul), f2.(4ul)) x)


[@CInline]
let fmul out f1 f2 =
  let h0 = ST.get () in
  BL.fmul5_lemma1 (as_felem5 h0 f1) (as_felem5 h0 f2);
  make_u52_5 out (BI.fmul5
    (f1.(0ul), f1.(1ul), f1.(2ul), f1.(3ul), f1.(4ul))
    (f2.(0ul), f2.(1ul), f2.(2ul), f2.(3ul), f2.(4ul)))


[@CInline]
let fsqr out f =
  let h0 = ST.get () in
  BL.fsqr5_lemma1 (as_felem5 h0 f);
  make_u52_5 out (BI.fsqr5 (f.(0ul), f.(1ul), f.(2ul), f.(3ul), f.(4ul)))


[@CInline]
let fnormalize_weak out f =
  make_u52_5 out (BI.normalize_weak5 (f.(0ul), f.(1ul), f.(2ul), f.(3ul), f.(4ul)))


[@CInline]
let fnormalize out f =
  make_u52_5 out (BI.normalize5 (f.(0ul), f.(1ul), f.(2ul), f.(3ul), f.(4ul)))


let fmul_3b_normalize_weak out f =
  let h0 = ST.get () in
  fmul_small_num out f (u64 21);
  let h1 = ST.get () in
  BL.fmul15_lemma (9,9,9,9,10) 21 (as_felem5 h0 f) (u64 21);
  assert (felem_fits5 (as_felem5 h1 out) (189,189,189,189,210));
  fnormalize_weak out out;
  BL.normalize_weak5_lemma (189,189,189,189,210) (as_felem5 h1 out)


let fmul_8_normalize_weak out f =
  let h0 = ST.get () in
  fmul_small_num out f (u64 8);
  let h1 = ST.get () in
  BL.fmul15_lemma (1,1,1,1,2) 8 (as_felem5 h0 f) (u64 8);
  assert (felem_fits5 (as_felem5 h1 out) (8,8,8,8,16));
  fnormalize_weak out out;
  BL.normalize_weak5_lemma (8,8,8,8,16) (as_felem5 h1 out)
