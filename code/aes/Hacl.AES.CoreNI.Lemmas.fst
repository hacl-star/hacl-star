module Hacl.AES.CoreNI.Lemmas

open FStar.Mul
open Lib.IntTypes
open Lib.ByteSequence

open Hacl.AES.Common

module LSeq = Lib.Sequence
module BV = FStar.BitVector

#set-options "--z3rlimit 180 --max_fuel 0 --max_ifuel 0"

let uints_bytes_be_lemma b =
  lemma_nat_from_to_intseq_be_preserves_value 1 (uints_from_bytes_be #U128 #SEC #1 b);
  assert (nat_to_intseq_be 1 (nat_from_intseq_be (uints_from_bytes_be #U128 #SEC #1 b)) ==
    uints_from_bytes_be #U128 #SEC #1 b);
  uints_from_bytes_be_nat_lemma #U128 #SEC #1 b;
  assert (nat_to_intseq_be 1 (nat_from_bytes_be b) ==
    uints_from_bytes_be #U128 #SEC #1 b);
  uints_to_bytes_be_nat_lemma #U128 #SEC 1 (nat_from_bytes_be b);
  assert (nat_to_bytes_be 16 (nat_from_bytes_be b) ==
    uints_to_bytes_be (uints_from_bytes_be #U128 #SEC #1 b));
  lemma_nat_from_to_bytes_be_preserves_value b 16

val unfold_nat_from_uint32_four: b:LSeq.lseq uint32 4 ->
  Lemma (nat_from_intseq_be b ==
    v (LSeq.index b 3) + pow2 32 * (v (LSeq.index b 2) +
    pow2 32 * (v (LSeq.index b 1) + pow2 32 * v (LSeq.index b 0))))

let unfold_nat_from_uint32_four b =
  let b0 = v (LSeq.index b 0) in
  let b1 = v (LSeq.index b 1) in
  let b2 = v (LSeq.index b 2) in
  let b3 = v (LSeq.index b 3) in

  let res = nat_from_intseq_be b in
  nat_from_intseq_be_slice_lemma b 3;
  nat_from_intseq_be_lemma0 (Seq.slice b 3 4);
  assert (res == b3 + pow2 32 * (nat_from_intseq_be (Seq.slice b 0 3)));

  nat_from_intseq_be_slice_lemma #U32 #SEC #3 (Seq.slice b 0 3) 2;
  nat_from_intseq_be_lemma0 (Seq.slice b 2 3);
  assert (nat_from_intseq_be (Seq.slice b 0 3) == b2 + pow2 32 * (nat_from_intseq_be (Seq.slice b 0 2)));

  nat_from_intseq_be_slice_lemma #U32 #SEC #2 (Seq.slice b 0 2) 1;
  nat_from_intseq_be_lemma0 (Seq.slice b 1 2);
  assert (nat_from_intseq_be (Seq.slice b 0 2) == b1 + pow2 32 * (nat_from_intseq_be (Seq.slice b 0 1)));

  nat_from_intseq_be_lemma0 (Seq.slice b 0 1);
  assert (res == b3 + pow2 32 * (b2 + pow2 32 * (b1 + pow2 32 * b0)))

let vec_set_counter_lemma b c =
  let counter = uint #U32 #SEC c in
  let n = uints_from_bytes_be #U32 #SEC #4 b in
  let n' = LSeq.upd n 3 counter in
  unfold_nat_from_uint32_four n';
  assert (nat_from_intseq_be n' ==
    v (LSeq.index n' 3) + pow2 32 * (v (LSeq.index n' 2) +
    pow2 32 * (v (LSeq.index n' 1) + pow2 32 * v (LSeq.index n' 0))));
  assert (v (LSeq.index n' 3) == c);
  assert (LSeq.index n' 2 == LSeq.index n 2);
  assert (LSeq.index n' 1 == LSeq.index n 1);
  assert (LSeq.index n' 0 == LSeq.index n 0);
  index_uints_from_bytes_be #U32 #SEC #4 b 2;
  index_uints_from_bytes_be #U32 #SEC #4 b 1;
  index_uints_from_bytes_be #U32 #SEC #4 b 0;
  lemma_reveal_uint_to_bytes_be #U32 #SEC (LSeq.sub b 8 4);
  lemma_reveal_uint_to_bytes_be #U32 #SEC (LSeq.sub b 4 4);
  lemma_reveal_uint_to_bytes_be #U32 #SEC (LSeq.sub b 0 4);
  assert (nat_from_intseq_be n' ==
    c + pow2 32 * (nat_from_bytes_be (LSeq.sub b 8 4) +
    pow2 32 * (nat_from_bytes_be (LSeq.sub b 4 4) +
    pow2 32 * nat_from_bytes_be (LSeq.sub b 0 4))));

  let m = LSeq.update_sub b 12 4 (nat_to_bytes_be 4 c) in
  let m' = uints_from_bytes_be #U32 #SEC #4 m in
  unfold_nat_from_uint32_four m';
  assert (nat_from_intseq_be m' ==
    v (LSeq.index m' 3) + pow2 32 * (v (LSeq.index m' 2) +
    pow2 32 * (v (LSeq.index m' 1) + pow2 32 * v (LSeq.index m' 0))));
  index_uints_from_bytes_be #U32 #SEC #4 m 3;
  assert (LSeq.index m' 3 == uint_from_bytes_be (LSeq.sub m 12 4));
  lemma_reveal_uint_to_bytes_be #U32 #SEC (LSeq.sub m 12 4);
  assert (nat_from_bytes_be (LSeq.sub m 12 4) == uint_v (uint_from_bytes_be #U32 #SEC (LSeq.sub m 12 4)));
  assert (LSeq.sub m 12 4 == nat_to_bytes_be 4 c);
  lemma_nat_to_from_bytes_be_preserves_value (nat_to_bytes_be #SEC 16 c) 16 c;
  assert (v (LSeq.index m' 3) == c);
  index_uints_from_bytes_be #U32 #SEC #4 m 2;
  index_uints_from_bytes_be #U32 #SEC #4 m 1;
  index_uints_from_bytes_be #U32 #SEC #4 m 0;
  lemma_reveal_uint_to_bytes_be #U32 #SEC (LSeq.sub m 8 4);
  lemma_reveal_uint_to_bytes_be #U32 #SEC (LSeq.sub m 4 4);
  lemma_reveal_uint_to_bytes_be #U32 #SEC (LSeq.sub m 0 4);
  LSeq.eq_intro (LSeq.sub b 8 4) (LSeq.sub m 8 4);
  LSeq.eq_intro (LSeq.sub b 4 4) (LSeq.sub m 4 4);
  LSeq.eq_intro (LSeq.sub b 0 4) (LSeq.sub m 0 4);
  assert (v (LSeq.index m' 2) == nat_from_bytes_be (LSeq.sub m 8 4));
  assert (v (LSeq.index m' 1) == nat_from_bytes_be (LSeq.sub m 4 4));
  assert (v (LSeq.index m' 0) == nat_from_bytes_be (LSeq.sub m 0 4));
  uints_from_bytes_be_nat_lemma #U32 #SEC #4 m;
  assert (nat_from_bytes_be m ==
    c + pow2 32 * (nat_from_bytes_be (LSeq.sub b 8 4) +
    pow2 32 * (nat_from_bytes_be (LSeq.sub b 4 4) +
    pow2 32 * nat_from_bytes_be (LSeq.sub b 0 4))));

  let u = uints_to_bytes_be (uints_from_bytes_be #U128 #SEC #1 (uints_to_bytes_be n')) in
  uints_bytes_be_lemma (uints_to_bytes_be n');
  assert (u == uints_to_bytes_be n');

  assert (nat_from_intseq_be n' == nat_from_bytes_be m);
  lemma_nat_from_to_intseq_be_preserves_value #U32 #SEC 4 n';
  assert (nat_to_intseq_be #U32 #SEC 4 (nat_from_intseq_be #U32 #SEC n') == n');
  assert (u == uints_to_bytes_be #U32 #SEC #4 (nat_to_intseq_be #U32 #SEC 4 (nat_from_intseq_be #U32 #SEC n')));
  assert (u == uints_to_bytes_be #U32 #SEC #4 (nat_to_intseq_be #U32 #SEC 4 (nat_from_bytes_be m)));
  uints_to_bytes_be_nat_lemma #U32 #SEC 4 (nat_from_bytes_be m);
  assert (u == nat_to_bytes_be 16 (nat_from_bytes_be m));
  lemma_nat_from_to_bytes_be_preserves_value m 16;
  assert (u == m)

val vec_u128_bytes_nat:
  b:LSeq.lseq uint128 1 ->
  Lemma (nat_from_intseq_be b == nat_from_bytes_be (uints_to_bytes_be b))

let vec_u128_bytes_nat b =
  uints_from_bytes_be_nat_lemma (uints_to_bytes_be b);
  assert (nat_from_intseq_be (uints_from_bytes_be #U128 #SEC #1 (uints_to_bytes_be b)) ==
    nat_from_bytes_be (uints_to_bytes_be b));
  lemma_nat_from_to_intseq_be_preserves_value 1 b;
  assert (nat_from_intseq_be (uints_from_bytes_be #U128 #SEC #1 (uints_to_bytes_be b)) ==
    nat_from_intseq_be (uints_from_bytes_be #U128 #SEC #1 (uints_to_bytes_be (nat_to_intseq_be 1 (nat_from_intseq_be b)))));
  uints_to_bytes_be_nat_lemma #U128 #SEC 1 (nat_from_intseq_be b);
  assert (nat_from_intseq_be (uints_from_bytes_be #U128 #SEC #1 (uints_to_bytes_be b)) ==
    nat_from_intseq_be (uints_from_bytes_be #U128 #SEC #1 (nat_to_bytes_be 16 (nat_from_intseq_be b))));
  uints_from_bytes_be_nat_lemma #U128 #SEC #1 (nat_to_bytes_be 16 (nat_from_intseq_be b));
  assert (nat_from_intseq_be (uints_from_bytes_be #U128 #SEC #1 (uints_to_bytes_be b)) ==
    nat_from_bytes_be (nat_to_bytes_be #SEC 16 (nat_from_intseq_be b)));
  lemma_nat_to_from_bytes_be_preserves_value #SEC (nat_to_bytes_be #SEC 16 (nat_from_intseq_be b)) 16 (nat_from_intseq_be b)

val unfold_nat_from_uint8_16: b:LSeq.lseq uint8 16 ->
  Lemma (nat_from_intseq_be b ==
    v (LSeq.index b 15) + pow2 8 * (v (LSeq.index b 14) +
    pow2 8 * (v (LSeq.index b 13) + pow2 8 * (v (LSeq.index b 12) +
    pow2 8 * (v (LSeq.index b 11) + pow2 8 * (v (LSeq.index b 10) +
    pow2 8 * (v (LSeq.index b 9) + pow2 8 * (v (LSeq.index b 8) +
    pow2 8 * (v (LSeq.index b 7) + pow2 8 * (v (LSeq.index b 6) +
    pow2 8 * (v (LSeq.index b 5) + pow2 8 * (v (LSeq.index b 4) +
    pow2 8 * (v (LSeq.index b 3) + pow2 8 * (v (LSeq.index b 2) +
    pow2 8 * (v (LSeq.index b 1) + pow2 8 * v (LSeq.index b 0))))))))))))))))

let unfold_nat_from_uint8_16 b =
  let b0 = v (LSeq.index b 0) in
  let b1 = v (LSeq.index b 1) in
  let b2 = v (LSeq.index b 2) in
  let b3 = v (LSeq.index b 3) in
  let b4 = v (LSeq.index b 4) in
  let b5 = v (LSeq.index b 5) in
  let b6 = v (LSeq.index b 6) in
  let b7 = v (LSeq.index b 7) in
  let b8 = v (LSeq.index b 8) in
  let b9 = v (LSeq.index b 9) in
  let b10 = v (LSeq.index b 10) in
  let b11 = v (LSeq.index b 11) in
  let b12 = v (LSeq.index b 12) in
  let b13 = v (LSeq.index b 13) in
  let b14 = v (LSeq.index b 14) in
  let b15 = v (LSeq.index b 15) in

  let res = nat_from_intseq_be b in
  nat_from_intseq_be_slice_lemma b 15;
  nat_from_intseq_be_lemma0 (Seq.slice b 15 16);
  assert (res == b15 + pow2 8 * (nat_from_intseq_be (Seq.slice b 0 15)));

  nat_from_intseq_be_slice_lemma #U8 #SEC #15 (Seq.slice b 0 15) 14;
  nat_from_intseq_be_lemma0 (Seq.slice b 14 15);
  assert (nat_from_intseq_be (Seq.slice b 0 15) == b14 + pow2 8 * (nat_from_intseq_be (Seq.slice b 0 14)));

  nat_from_intseq_be_slice_lemma #U8 #SEC #14 (Seq.slice b 0 14) 13;
  nat_from_intseq_be_lemma0 (Seq.slice b 13 14);
  assert (nat_from_intseq_be (Seq.slice b 0 14) == b13 + pow2 8 * (nat_from_intseq_be (Seq.slice b 0 13)));

  nat_from_intseq_be_slice_lemma #U8 #SEC #13 (Seq.slice b 0 13) 12;
  nat_from_intseq_be_lemma0 (Seq.slice b 12 13);
  assert (nat_from_intseq_be (Seq.slice b 0 13) == b12 + pow2 8 * (nat_from_intseq_be (Seq.slice b 0 12)));

  nat_from_intseq_be_slice_lemma #U8 #SEC #12 (Seq.slice b 0 12) 11;
  nat_from_intseq_be_lemma0 (Seq.slice b 11 12);
  assert (nat_from_intseq_be (Seq.slice b 0 12) == b11 + pow2 8 * (nat_from_intseq_be (Seq.slice b 0 11)));

  nat_from_intseq_be_slice_lemma #U8 #SEC #11 (Seq.slice b 0 11) 10;
  nat_from_intseq_be_lemma0 (Seq.slice b 10 11);
  assert (nat_from_intseq_be (Seq.slice b 0 11) == b10 + pow2 8 * (nat_from_intseq_be (Seq.slice b 0 10)));

  nat_from_intseq_be_slice_lemma #U8 #SEC #10 (Seq.slice b 0 10) 9;
  nat_from_intseq_be_lemma0 (Seq.slice b 9 10);
  assert (nat_from_intseq_be (Seq.slice b 0 10) == b9 + pow2 8 * (nat_from_intseq_be (Seq.slice b 0 9)));

  nat_from_intseq_be_slice_lemma #U8 #SEC #9 (Seq.slice b 0 9) 8;
  nat_from_intseq_be_lemma0 (Seq.slice b 8 9);
  assert (nat_from_intseq_be (Seq.slice b 0 9) == b8 + pow2 8 * (nat_from_intseq_be (Seq.slice b 0 8)));

  nat_from_intseq_be_slice_lemma #U8 #SEC #8 (Seq.slice b 0 8) 7;
  nat_from_intseq_be_lemma0 (Seq.slice b 7 8);
  assert (nat_from_intseq_be (Seq.slice b 0 8) == b7 + pow2 8 * (nat_from_intseq_be (Seq.slice b 0 7)));

  nat_from_intseq_be_slice_lemma #U8 #SEC #7 (Seq.slice b 0 7) 6;
  nat_from_intseq_be_lemma0 (Seq.slice b 6 7);
  assert (nat_from_intseq_be (Seq.slice b 0 7) == b6 + pow2 8 * (nat_from_intseq_be (Seq.slice b 0 6)));

  nat_from_intseq_be_slice_lemma #U8 #SEC #6 (Seq.slice b 0 6) 5;
  nat_from_intseq_be_lemma0 (Seq.slice b 5 6);
  assert (nat_from_intseq_be (Seq.slice b 0 6) == b5 + pow2 8 * (nat_from_intseq_be (Seq.slice b 0 5)));

  nat_from_intseq_be_slice_lemma #U8 #SEC #5 (Seq.slice b 0 5) 4;
  nat_from_intseq_be_lemma0 (Seq.slice b 4 5);
  assert (nat_from_intseq_be (Seq.slice b 0 5) == b4 + pow2 8 * (nat_from_intseq_be (Seq.slice b 0 4)));

  nat_from_intseq_be_slice_lemma #U8 #SEC #4 (Seq.slice b 0 4) 3;
  nat_from_intseq_be_lemma0 (Seq.slice b 3 4);
  assert (nat_from_intseq_be (Seq.slice b 0 4) == b3 + pow2 8 * (nat_from_intseq_be (Seq.slice b 0 3)));

  nat_from_intseq_be_slice_lemma #U8 #SEC #3 (Seq.slice b 0 3) 2;
  nat_from_intseq_be_lemma0 (Seq.slice b 2 3);
  assert (nat_from_intseq_be (Seq.slice b 0 3) == b2 + pow2 8 * (nat_from_intseq_be (Seq.slice b 0 2)));

  nat_from_intseq_be_slice_lemma #U8 #SEC #2 (Seq.slice b 0 2) 1;
  nat_from_intseq_be_lemma0 (Seq.slice b 1 2);
  assert (nat_from_intseq_be (Seq.slice b 0 2) == b1 + pow2 8 * (nat_from_intseq_be (Seq.slice b 0 1)));

  nat_from_intseq_be_lemma0 (Seq.slice b 0 1)

let to_vec128 (x:uint128) : BV.bv_t 128 = UInt.to_vec #128 (v x)
let to_vec8 (x:uint8) : BV.bv_t 8 = UInt.to_vec #8 (v x)

let elem_s = LSeq.lseq uint8 16

let to_elem (x:elem_s) : uint128 =
  mk_int #U128 (v (LSeq.index x 15) + pow2 8 * (v (LSeq.index x 14) +
    pow2 8 * (v (LSeq.index x 13) + pow2 8 * (v (LSeq.index x 12) +
    pow2 8 * (v (LSeq.index x 11) + pow2 8 * (v (LSeq.index x 10) +
    pow2 8 * (v (LSeq.index x 9) + pow2 8 * (v (LSeq.index x 8) +
    pow2 8 * (v (LSeq.index x 7) + pow2 8 * (v (LSeq.index x 6) +
    pow2 8 * (v (LSeq.index x 5) + pow2 8 * (v (LSeq.index x 4) +
    pow2 8 * (v (LSeq.index x 3) + pow2 8 * (v (LSeq.index x 2) +
    pow2 8 * (v (LSeq.index x 1) + pow2 8 * v (LSeq.index x 0))))))))))))))))

let logxor_s (x:elem_s) (y:elem_s) : elem_s =
  let r0 = LSeq.index x 0 ^. LSeq.index y 0 in
  let r1 = LSeq.index x 1 ^. LSeq.index y 1 in
  let r2 = LSeq.index x 2 ^. LSeq.index y 2 in
  let r3 = LSeq.index x 3 ^. LSeq.index y 3 in
  let r4 = LSeq.index x 4 ^. LSeq.index y 4 in
  let r5 = LSeq.index x 5 ^. LSeq.index y 5 in
  let r6 = LSeq.index x 6 ^. LSeq.index y 6 in
  let r7 = LSeq.index x 7 ^. LSeq.index y 7 in
  let r8 = LSeq.index x 8 ^. LSeq.index y 8 in
  let r9 = LSeq.index x 9 ^. LSeq.index y 9 in
  let r10 = LSeq.index x 10 ^. LSeq.index y 10 in
  let r11 = LSeq.index x 11 ^. LSeq.index y 11 in
  let r12 = LSeq.index x 12 ^. LSeq.index y 12 in
  let r13 = LSeq.index x 13 ^. LSeq.index y 13 in
  let r14 = LSeq.index x 14 ^. LSeq.index y 14 in
  let r15 = LSeq.index x 15 ^. LSeq.index y 15 in
  LSeq.create16 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15

val to_vec128_lemma : x:elem_s -> Lemma
  (to_vec128 (to_elem x) == Seq.append (Seq.append (Seq.append
    (Seq.append (Seq.append (Seq.append (Seq.append (Seq.append (Seq.append
    (Seq.append (Seq.append (Seq.append (Seq.append (Seq.append (Seq.append
    (to_vec8 (LSeq.index x 0)) (to_vec8 (LSeq.index x 1))) (to_vec8 (LSeq.index x 2)))
    (to_vec8 (LSeq.index x 3))) (to_vec8 (LSeq.index x 4))) (to_vec8 (LSeq.index x 5)))
    (to_vec8 (LSeq.index x 6))) (to_vec8 (LSeq.index x 7))) (to_vec8 (LSeq.index x 8)))
    (to_vec8 (LSeq.index x 9))) (to_vec8 (LSeq.index x 10))) (to_vec8 (LSeq.index x 11)))
    (to_vec8 (LSeq.index x 12))) (to_vec8 (LSeq.index x 13))) (to_vec8 (LSeq.index x 14)))
    (to_vec8 (LSeq.index x 15)))
let to_vec128_lemma x =
  let x0 = to_vec8 (LSeq.index x 0) in
  let x1 = to_vec8 (LSeq.index x 1) in
  let x2 = to_vec8 (LSeq.index x 2) in
  let x3 = to_vec8 (LSeq.index x 3) in
  let x4 = to_vec8 (LSeq.index x 4) in
  let x5 = to_vec8 (LSeq.index x 5) in
  let x6 = to_vec8 (LSeq.index x 6) in
  let x7 = to_vec8 (LSeq.index x 7) in
  let x8 = to_vec8 (LSeq.index x 8) in
  let x9 = to_vec8 (LSeq.index x 9) in
  let x10 = to_vec8 (LSeq.index x 10) in
  let x11 = to_vec8 (LSeq.index x 11) in
  let x12 = to_vec8 (LSeq.index x 12) in
  let x13 = to_vec8 (LSeq.index x 13) in
  let x14 = to_vec8 (LSeq.index x 14) in
  let x15 = to_vec8 (LSeq.index x 15) in
  UInt.append_lemma x0 x1;
  UInt.append_lemma #16 #8 (Seq.append x0 x1) x2;
  UInt.append_lemma #24 #8 (Seq.append (Seq.append x0 x1) x2) x3;
  UInt.append_lemma #32 #8 (Seq.append (Seq.append (Seq.append x0 x1) x2) x3) x4;
  UInt.append_lemma #40 #8 (Seq.append (Seq.append (Seq.append (Seq.append x0 x1) x2) x3) x4) x5;
  UInt.append_lemma #48 #8 (Seq.append (Seq.append (Seq.append (Seq.append (Seq.append x0 x1) x2)
    x3) x4) x5) x6;
  UInt.append_lemma #56 #8 (Seq.append (Seq.append (Seq.append (Seq.append (Seq.append (Seq.append
    x0 x1) x2) x3) x4) x5) x6) x7;
  UInt.append_lemma #64 #8 (Seq.append (Seq.append (Seq.append (Seq.append (Seq.append (Seq.append
    (Seq.append x0 x1) x2) x3) x4) x5) x6) x7) x8;
  UInt.append_lemma #72 #8 (Seq.append (Seq.append (Seq.append (Seq.append (Seq.append (Seq.append
    (Seq.append (Seq.append x0 x1) x2) x3) x4) x5) x6) x7) x8) x9;
  UInt.append_lemma #80 #8 (Seq.append (Seq.append (Seq.append (Seq.append (Seq.append (Seq.append
    (Seq.append (Seq.append (Seq.append x0 x1) x2) x3) x4) x5) x6) x7) x8) x9) x10;
  UInt.append_lemma #88 #8 (Seq.append (Seq.append (Seq.append (Seq.append (Seq.append (Seq.append
    (Seq.append (Seq.append (Seq.append (Seq.append x0 x1) x2) x3) x4) x5) x6) x7) x8) x9) x10)
    x11;
  UInt.append_lemma #96 #8 (Seq.append (Seq.append (Seq.append (Seq.append (Seq.append (Seq.append
    (Seq.append (Seq.append (Seq.append (Seq.append (Seq.append x0 x1) x2) x3) x4) x5) x6) x7) x8)
    x9) x10) x11) x12;
  UInt.append_lemma #104 #8 (Seq.append (Seq.append (Seq.append (Seq.append (Seq.append (Seq.append
    (Seq.append (Seq.append (Seq.append (Seq.append (Seq.append (Seq.append x0 x1) x2) x3) x4) x5)
    x6) x7) x8) x9) x10) x11) x12) x13;
  UInt.append_lemma #112 #8 (Seq.append (Seq.append (Seq.append (Seq.append (Seq.append (Seq.append
    (Seq.append (Seq.append (Seq.append (Seq.append (Seq.append (Seq.append (Seq.append x0 x1) x2)
    x3) x4) x5) x6) x7) x8) x9) x10) x11) x12) x13) x14;
  UInt.append_lemma #120 #8 (Seq.append (Seq.append (Seq.append (Seq.append (Seq.append (Seq.append
    (Seq.append (Seq.append (Seq.append (Seq.append (Seq.append (Seq.append (Seq.append (Seq.append
    x0 x1) x2) x3) x4) x5) x6) x7) x8) x9) x10) x11) x12) x13) x14) x15;
  assert(
    UInt.from_vec x15 + pow2 8 * (UInt.from_vec x14 + pow2 8 * (UInt.from_vec x13 +
      pow2 8 * (UInt.from_vec x12 + pow2 8 * (UInt.from_vec x11 + pow2 8 * (UInt.from_vec x10 +
      pow2 8 * (UInt.from_vec x9 + pow2 8 * (UInt.from_vec x8 + pow2 8 * (UInt.from_vec x7 +
      pow2 8 * (UInt.from_vec x6 + pow2 8 * (UInt.from_vec x5 + pow2 8 * (UInt.from_vec x4 +
      pow2 8 * (UInt.from_vec x3 + pow2 8 * (UInt.from_vec x2 + pow2 8 * (UInt.from_vec x1 +
      pow2 8 * (UInt.from_vec x0))))))))))))))) ==
    UInt.from_vec #128 (Seq.append (Seq.append (Seq.append (Seq.append (Seq.append (Seq.append
      (Seq.append (Seq.append (Seq.append (Seq.append (Seq.append (Seq.append (Seq.append
      (Seq.append (Seq.append x0 x1) x2) x3) x4) x5) x6) x7) x8) x9) x10) x11) x12) x13) x14) x15))

val logxor_vec_helper_0_32: x:elem_s -> y:elem_s -> Lemma
  (Seq.slice (BV.logxor_vec (to_vec128 (to_elem x)) (to_vec128 (to_elem y))) 0 32 ==
   Seq.append (Seq.append (Seq.append
     (BV.logxor_vec (to_vec8 (LSeq.index x 0)) (to_vec8 (LSeq.index y 0)))
     (BV.logxor_vec (to_vec8 (LSeq.index x 1)) (to_vec8 (LSeq.index y 1))))
     (BV.logxor_vec (to_vec8 (LSeq.index x 2)) (to_vec8 (LSeq.index y 2))))
     (BV.logxor_vec (to_vec8 (LSeq.index x 3)) (to_vec8 (LSeq.index y 3))))
let logxor_vec_helper_0_32 x y =
  to_vec128_lemma x;
  to_vec128_lemma y;
  Seq.lemma_eq_intro
    (Seq.slice (BV.logxor_vec (to_vec128 (to_elem x)) (to_vec128 (to_elem y))) 0 32)
    (BV.logxor_vec #32 (Seq.slice (to_vec128 (to_elem x)) 0 32) (Seq.slice (to_vec128 (to_elem y)) 0 32));
  Seq.lemma_eq_intro
    (Seq.slice (to_vec128 (to_elem x)) 0 32)
    (Seq.append (Seq.append (Seq.append
      (to_vec8 (LSeq.index x 0)) (to_vec8 (LSeq.index x 1))) (to_vec8 (LSeq.index x 2)))
      (to_vec8 (LSeq.index x 3)));
  Seq.lemma_eq_intro
    (Seq.slice (to_vec128 (to_elem y)) 0 32)
    (Seq.append (Seq.append (Seq.append
      (to_vec8 (LSeq.index y 0)) (to_vec8 (LSeq.index y 1))) (to_vec8 (LSeq.index y 2)))
      (to_vec8 (LSeq.index y 3)));
  Seq.lemma_eq_intro
    (Seq.slice (BV.logxor_vec (to_vec128 (to_elem x)) (to_vec128 (to_elem y))) 0 32)
    (Seq.append (Seq.append (Seq.append
      (BV.logxor_vec (to_vec8 (LSeq.index x 0)) (to_vec8 (LSeq.index y 0)))
      (BV.logxor_vec (to_vec8 (LSeq.index x 1)) (to_vec8 (LSeq.index y 1))))
      (BV.logxor_vec (to_vec8 (LSeq.index x 2)) (to_vec8 (LSeq.index y 2))))
      (BV.logxor_vec (to_vec8 (LSeq.index x 3)) (to_vec8 (LSeq.index y 3))))

val logxor_vec_helper_32_64: x:elem_s -> y:elem_s -> Lemma
  (Seq.slice (BV.logxor_vec (to_vec128 (to_elem x)) (to_vec128 (to_elem y))) 32 64 ==
   Seq.append (Seq.append (Seq.append
     (BV.logxor_vec (to_vec8 (LSeq.index x 4)) (to_vec8 (LSeq.index y 4)))
     (BV.logxor_vec (to_vec8 (LSeq.index x 5)) (to_vec8 (LSeq.index y 5))))
     (BV.logxor_vec (to_vec8 (LSeq.index x 6)) (to_vec8 (LSeq.index y 6))))
     (BV.logxor_vec (to_vec8 (LSeq.index x 7)) (to_vec8 (LSeq.index y 7))))
let logxor_vec_helper_32_64 x y =
  to_vec128_lemma x;
  to_vec128_lemma y;
  Seq.lemma_eq_intro
    (Seq.slice (BV.logxor_vec (to_vec128 (to_elem x)) (to_vec128 (to_elem y))) 32 64)
    (BV.logxor_vec #32 (Seq.slice (to_vec128 (to_elem x)) 32 64) (Seq.slice (to_vec128 (to_elem y)) 32 64));
  Seq.lemma_eq_intro
    (Seq.slice (to_vec128 (to_elem x)) 32 64)
    (Seq.append (Seq.append (Seq.append
      (to_vec8 (LSeq.index x 4)) (to_vec8 (LSeq.index x 5))) (to_vec8 (LSeq.index x 6)))
      (to_vec8 (LSeq.index x 7)));
  Seq.lemma_eq_intro
    (Seq.slice (to_vec128 (to_elem y)) 32 64)
    (Seq.append (Seq.append (Seq.append
      (to_vec8 (LSeq.index y 4)) (to_vec8 (LSeq.index y 5))) (to_vec8 (LSeq.index y 6)))
      (to_vec8 (LSeq.index y 7)));
  Seq.lemma_eq_intro
    (Seq.slice (BV.logxor_vec (to_vec128 (to_elem x)) (to_vec128 (to_elem y))) 32 64)
    (Seq.append (Seq.append (Seq.append
      (BV.logxor_vec (to_vec8 (LSeq.index x 4)) (to_vec8 (LSeq.index y 4)))
      (BV.logxor_vec (to_vec8 (LSeq.index x 5)) (to_vec8 (LSeq.index y 5))))
      (BV.logxor_vec (to_vec8 (LSeq.index x 6)) (to_vec8 (LSeq.index y 6))))
      (BV.logxor_vec (to_vec8 (LSeq.index x 7)) (to_vec8 (LSeq.index y 7))))

val logxor_vec_helper_0_64: x:elem_s -> y:elem_s -> Lemma
  (Seq.slice (BV.logxor_vec (to_vec128 (to_elem x)) (to_vec128 (to_elem y))) 0 64 ==
   Seq.append (Seq.append (Seq.append
     (Seq.append (Seq.append (Seq.append (Seq.append
     (BV.logxor_vec (to_vec8 (LSeq.index x 0)) (to_vec8 (LSeq.index y 0)))
     (BV.logxor_vec (to_vec8 (LSeq.index x 1)) (to_vec8 (LSeq.index y 1))))
     (BV.logxor_vec (to_vec8 (LSeq.index x 2)) (to_vec8 (LSeq.index y 2))))
     (BV.logxor_vec (to_vec8 (LSeq.index x 3)) (to_vec8 (LSeq.index y 3))))
     (BV.logxor_vec (to_vec8 (LSeq.index x 4)) (to_vec8 (LSeq.index y 4))))
     (BV.logxor_vec (to_vec8 (LSeq.index x 5)) (to_vec8 (LSeq.index y 5))))
     (BV.logxor_vec (to_vec8 (LSeq.index x 6)) (to_vec8 (LSeq.index y 6))))
     (BV.logxor_vec (to_vec8 (LSeq.index x 7)) (to_vec8 (LSeq.index y 7))))
let logxor_vec_helper_0_64 x y =
  to_vec128_lemma x;
  to_vec128_lemma y;
  logxor_vec_helper_0_32 x y;
  logxor_vec_helper_32_64 x y;
  Seq.lemma_eq_intro
    (Seq.slice (BV.logxor_vec (to_vec128 (to_elem x)) (to_vec128 (to_elem y))) 0 64)
    (Seq.append (Seq.append (Seq.append
      (Seq.append (Seq.append (Seq.append (Seq.append
      (BV.logxor_vec (to_vec8 (LSeq.index x 0)) (to_vec8 (LSeq.index y 0)))
      (BV.logxor_vec (to_vec8 (LSeq.index x 1)) (to_vec8 (LSeq.index y 1))))
      (BV.logxor_vec (to_vec8 (LSeq.index x 2)) (to_vec8 (LSeq.index y 2))))
      (BV.logxor_vec (to_vec8 (LSeq.index x 3)) (to_vec8 (LSeq.index y 3))))
      (BV.logxor_vec (to_vec8 (LSeq.index x 4)) (to_vec8 (LSeq.index y 4))))
      (BV.logxor_vec (to_vec8 (LSeq.index x 5)) (to_vec8 (LSeq.index y 5))))
      (BV.logxor_vec (to_vec8 (LSeq.index x 6)) (to_vec8 (LSeq.index y 6))))
      (BV.logxor_vec (to_vec8 (LSeq.index x 7)) (to_vec8 (LSeq.index y 7))))

val logxor_vec_lemma: x:elem_s -> y:elem_s -> Lemma
  (BV.logxor_vec (to_vec128 (to_elem x)) (to_vec128 (to_elem y)) ==
   Seq.append (Seq.append (Seq.append (Seq.append (Seq.append
     (Seq.append (Seq.append (Seq.append (Seq.append (Seq.append
     (Seq.append (Seq.append (Seq.append (Seq.append (Seq.append
     (BV.logxor_vec (to_vec8 (LSeq.index x 0)) (to_vec8 (LSeq.index y 0)))
     (BV.logxor_vec (to_vec8 (LSeq.index x 1)) (to_vec8 (LSeq.index y 1))))
     (BV.logxor_vec (to_vec8 (LSeq.index x 2)) (to_vec8 (LSeq.index y 2))))
     (BV.logxor_vec (to_vec8 (LSeq.index x 3)) (to_vec8 (LSeq.index y 3))))
     (BV.logxor_vec (to_vec8 (LSeq.index x 4)) (to_vec8 (LSeq.index y 4))))
     (BV.logxor_vec (to_vec8 (LSeq.index x 5)) (to_vec8 (LSeq.index y 5))))
     (BV.logxor_vec (to_vec8 (LSeq.index x 6)) (to_vec8 (LSeq.index y 6))))
     (BV.logxor_vec (to_vec8 (LSeq.index x 7)) (to_vec8 (LSeq.index y 7))))
     (BV.logxor_vec (to_vec8 (LSeq.index x 8)) (to_vec8 (LSeq.index y 8))))
     (BV.logxor_vec (to_vec8 (LSeq.index x 9)) (to_vec8 (LSeq.index y 9))))
     (BV.logxor_vec (to_vec8 (LSeq.index x 10)) (to_vec8 (LSeq.index y 10))))
     (BV.logxor_vec (to_vec8 (LSeq.index x 11)) (to_vec8 (LSeq.index y 11))))
     (BV.logxor_vec (to_vec8 (LSeq.index x 12)) (to_vec8 (LSeq.index y 12))))
     (BV.logxor_vec (to_vec8 (LSeq.index x 13)) (to_vec8 (LSeq.index y 13))))
     (BV.logxor_vec (to_vec8 (LSeq.index x 14)) (to_vec8 (LSeq.index y 14))))
     (BV.logxor_vec (to_vec8 (LSeq.index x 15)) (to_vec8 (LSeq.index y 15))))
let logxor_vec_lemma x y =
  to_vec128_lemma x;
  to_vec128_lemma y;
  logxor_vec_helper_0_64 x y;
  Seq.lemma_eq_intro
    (BV.logxor_vec (to_vec128 (to_elem x)) (to_vec128 (to_elem y)))
    (Seq.append (Seq.append (Seq.append (Seq.append (Seq.append
      (Seq.append (Seq.append (Seq.append (Seq.append (Seq.append
      (Seq.append (Seq.append (Seq.append (Seq.append (Seq.append
      (BV.logxor_vec (to_vec8 (LSeq.index x 0)) (to_vec8 (LSeq.index y 0)))
      (BV.logxor_vec (to_vec8 (LSeq.index x 1)) (to_vec8 (LSeq.index y 1))))
      (BV.logxor_vec (to_vec8 (LSeq.index x 2)) (to_vec8 (LSeq.index y 2))))
      (BV.logxor_vec (to_vec8 (LSeq.index x 3)) (to_vec8 (LSeq.index y 3))))
      (BV.logxor_vec (to_vec8 (LSeq.index x 4)) (to_vec8 (LSeq.index y 4))))
      (BV.logxor_vec (to_vec8 (LSeq.index x 5)) (to_vec8 (LSeq.index y 5))))
      (BV.logxor_vec (to_vec8 (LSeq.index x 6)) (to_vec8 (LSeq.index y 6))))
      (BV.logxor_vec (to_vec8 (LSeq.index x 7)) (to_vec8 (LSeq.index y 7))))
      (BV.logxor_vec (to_vec8 (LSeq.index x 8)) (to_vec8 (LSeq.index y 8))))
      (BV.logxor_vec (to_vec8 (LSeq.index x 9)) (to_vec8 (LSeq.index y 9))))
      (BV.logxor_vec (to_vec8 (LSeq.index x 10)) (to_vec8 (LSeq.index y 10))))
      (BV.logxor_vec (to_vec8 (LSeq.index x 11)) (to_vec8 (LSeq.index y 11))))
      (BV.logxor_vec (to_vec8 (LSeq.index x 12)) (to_vec8 (LSeq.index y 12))))
      (BV.logxor_vec (to_vec8 (LSeq.index x 13)) (to_vec8 (LSeq.index y 13))))
      (BV.logxor_vec (to_vec8 (LSeq.index x 14)) (to_vec8 (LSeq.index y 14))))
      (BV.logxor_vec (to_vec8 (LSeq.index x 15)) (to_vec8 (LSeq.index y 15))))

val logxor_s_lemma: x:elem_s -> y:elem_s -> Lemma
  (to_elem (logxor_s x y) == to_elem x ^. to_elem y)

let logxor_s_lemma x y =
  logxor_spec (to_elem x) (to_elem y);
  assert (to_vec128 (to_elem x ^. to_elem y) == BV.logxor_vec (to_vec128 (to_elem x)) (to_vec128 (to_elem y)));
  logxor_vec_lemma x y;
  logxor_spec (LSeq.index x 0) (LSeq.index y 0);
  logxor_spec (LSeq.index x 1) (LSeq.index y 1);
  logxor_spec (LSeq.index x 2) (LSeq.index y 2);
  logxor_spec (LSeq.index x 3) (LSeq.index y 3);
  logxor_spec (LSeq.index x 4) (LSeq.index y 4);
  logxor_spec (LSeq.index x 5) (LSeq.index y 5);
  logxor_spec (LSeq.index x 6) (LSeq.index y 6);
  logxor_spec (LSeq.index x 7) (LSeq.index y 7);
  logxor_spec (LSeq.index x 8) (LSeq.index y 8);
  logxor_spec (LSeq.index x 9) (LSeq.index y 9);
  logxor_spec (LSeq.index x 10) (LSeq.index y 10);
  logxor_spec (LSeq.index x 11) (LSeq.index y 11);
  logxor_spec (LSeq.index x 12) (LSeq.index y 12);
  logxor_spec (LSeq.index x 13) (LSeq.index y 13);
  logxor_spec (LSeq.index x 14) (LSeq.index y 14);
  logxor_spec (LSeq.index x 15) (LSeq.index y 15);
  to_vec128_lemma (logxor_s x y)

let vec_xor_lemma b1 b2 =
  let x = uints_to_bytes_be b1 in
  let y = uints_to_bytes_be b2 in
  let m = LSeq.map2 (logxor #U8) (uints_to_bytes_be b1) (uints_to_bytes_be b2) in
  vec_u128_bytes_nat b1;
  vec_u128_bytes_nat b2;
  assert (nat_from_intseq_be b1 == nat_from_bytes_be x);
  assert (nat_from_intseq_be b2 == nat_from_bytes_be y);
  unfold_nat_from_uint8_16 x;
  unfold_nat_from_uint8_16 y;
  logxor_s_lemma x y;
  assert (to_elem (logxor_s x y) == to_elem x ^. to_elem y);
  assert (v (to_elem (logxor_s x y)) == v (to_elem x ^. to_elem y));
  logxor_spec (to_elem x) (to_elem y);
  assert (v (to_elem (logxor_s x y)) == UInt.logxor #128 (nat_from_intseq_be b1) (nat_from_intseq_be b2));
  unfold_nat_from_uint8_16 m;
  assert (nat_from_intseq_be m == v (to_elem (logxor_s x y)));
  assert (nat_from_intseq_be m == UInt.logxor #128 (nat_from_intseq_be b1) (nat_from_intseq_be b2));
  nat_from_intseq_be_lemma0 (LSeq.map2 ( ^. ) b1 b2);
  assert (nat_from_intseq_be (LSeq.map2 ( ^. ) b1 b2) == v (LSeq.index b1 0 ^. LSeq.index b2 0));
  logxor_spec (LSeq.index b1 0) (LSeq.index b2 0);
  nat_from_intseq_be_lemma0 (b1);
  nat_from_intseq_be_lemma0 (b2);
  assert (nat_from_intseq_be (LSeq.map2 ( ^. ) b1 b2) == UInt.logxor #128 (nat_from_intseq_be b1) (nat_from_intseq_be b2));
  assert (nat_from_intseq_be m == nat_from_intseq_be (LSeq.map2 ( ^. ) b1 b2));
  assert (nat_to_bytes_be #SEC 16 (nat_from_intseq_be m) == nat_to_bytes_be 16 (nat_from_intseq_be (LSeq.map2 ( ^. ) b1 b2)));
  lemma_nat_from_to_intseq_be_preserves_value 16 m;
  uints_to_bytes_be_nat_lemma #U128 #SEC 1 (nat_from_intseq_be (LSeq.map2 ( ^. ) b1 b2));
  assert (m == uints_to_bytes_be #U128 #SEC #1 (nat_to_intseq_be #U128 #SEC 1 (nat_from_intseq_be (LSeq.map2 ( ^. ) b1 b2))));
  lemma_nat_from_to_intseq_be_preserves_value 1 (LSeq.map2 ( ^. ) b1 b2);
  assert (m == uints_to_bytes_be #U128 #SEC #1 (LSeq.map2 ( ^. ) b1 b2))

val unfold_nat_from_uint8_16_le: b:LSeq.lseq uint8 16 ->
  Lemma (nat_from_intseq_le b ==
    v (LSeq.index b 0) + pow2 8 * (v (LSeq.index b 1) +
    pow2 8 * (v (LSeq.index b 2) + pow2 8 * (v (LSeq.index b 3) +
    pow2 8 * (v (LSeq.index b 4) + pow2 8 * (v (LSeq.index b 5) +
    pow2 8 * (v (LSeq.index b 6) + pow2 8 * (v (LSeq.index b 7) +
    pow2 8 * (v (LSeq.index b 8) + pow2 8 * (v (LSeq.index b 9) +
    pow2 8 * (v (LSeq.index b 10) + pow2 8 * (v (LSeq.index b 11) +
    pow2 8 * (v (LSeq.index b 12) + pow2 8 * (v (LSeq.index b 13) +
    pow2 8 * (v (LSeq.index b 14) + pow2 8 * v (LSeq.index b 15))))))))))))))))

let unfold_nat_from_uint8_16_le b =
  let b0 = v (LSeq.index b 0) in
  let b1 = v (LSeq.index b 1) in
  let b2 = v (LSeq.index b 2) in
  let b3 = v (LSeq.index b 3) in
  let b4 = v (LSeq.index b 4) in
  let b5 = v (LSeq.index b 5) in
  let b6 = v (LSeq.index b 6) in
  let b7 = v (LSeq.index b 7) in
  let b8 = v (LSeq.index b 8) in
  let b9 = v (LSeq.index b 9) in
  let b10 = v (LSeq.index b 10) in
  let b11 = v (LSeq.index b 11) in
  let b12 = v (LSeq.index b 12) in
  let b13 = v (LSeq.index b 13) in
  let b14 = v (LSeq.index b 14) in
  let b15 = v (LSeq.index b 15) in

  let res = nat_from_intseq_le b in
  nat_from_intseq_le_slice_lemma b 1;
  nat_from_intseq_le_lemma0 (Seq.slice b 0 1);
  assert (res == b0 + pow2 8 * (nat_from_intseq_le (Seq.slice b 1 16)));

  nat_from_intseq_le_slice_lemma #U8 #SEC #15 (Seq.slice b 1 16) 1;
  nat_from_intseq_le_lemma0 (Seq.slice b 1 2);
  assert (nat_from_intseq_le (Seq.slice b 1 16) == b1 + pow2 8 * (nat_from_intseq_le (Seq.slice b 2 16)));
  
  nat_from_intseq_le_slice_lemma #U8 #SEC #14 (Seq.slice b 2 16) 1;
  nat_from_intseq_le_lemma0 (Seq.slice b 2 3);
  assert (nat_from_intseq_le (Seq.slice b 2 16) == b2 + pow2 8 * (nat_from_intseq_le (Seq.slice b 3 16)));
  
  nat_from_intseq_le_slice_lemma #U8 #SEC #13 (Seq.slice b 3 16) 1;
  nat_from_intseq_le_lemma0 (Seq.slice b 3 4);
  assert (nat_from_intseq_le (Seq.slice b 3 16) == b3 + pow2 8 * (nat_from_intseq_le (Seq.slice b 4 16)));
  
  nat_from_intseq_le_slice_lemma #U8 #SEC #12 (Seq.slice b 4 16) 1;
  nat_from_intseq_le_lemma0 (Seq.slice b 4 5);
  assert (nat_from_intseq_le (Seq.slice b 4 16) == b4 + pow2 8 * (nat_from_intseq_le (Seq.slice b 5 16)));

  nat_from_intseq_le_slice_lemma #U8 #SEC #11 (Seq.slice b 5 16) 1;
  nat_from_intseq_le_lemma0 (Seq.slice b 5 6);
  assert (nat_from_intseq_le (Seq.slice b 5 16) == b5 + pow2 8 * (nat_from_intseq_le (Seq.slice b 6 16)));
  
  nat_from_intseq_le_slice_lemma #U8 #SEC #10 (Seq.slice b 6 16) 1;
  nat_from_intseq_le_lemma0 (Seq.slice b 6 7);
  assert (nat_from_intseq_le (Seq.slice b 6 16) == b6 + pow2 8 * (nat_from_intseq_le (Seq.slice b 7 16)));
  
  nat_from_intseq_le_slice_lemma #U8 #SEC #9 (Seq.slice b 7 16) 1;
  nat_from_intseq_le_lemma0 (Seq.slice b 7 8);
  assert (nat_from_intseq_le (Seq.slice b 7 16) == b7 + pow2 8 * (nat_from_intseq_le (Seq.slice b 8 16)));
  
  nat_from_intseq_le_slice_lemma #U8 #SEC #8 (Seq.slice b 8 16) 1;
  nat_from_intseq_le_lemma0 (Seq.slice b 8 9);
  assert (nat_from_intseq_le (Seq.slice b 8 16) == b8 + pow2 8 * (nat_from_intseq_le (Seq.slice b 9 16)));
  
  nat_from_intseq_le_slice_lemma #U8 #SEC #7 (Seq.slice b 9 16) 1;
  nat_from_intseq_le_lemma0 (Seq.slice b 9 10);
  assert (nat_from_intseq_le (Seq.slice b 9 16) == b9 + pow2 8 * (nat_from_intseq_le (Seq.slice b 10 16)));
  
  nat_from_intseq_le_slice_lemma #U8 #SEC #6 (Seq.slice b 10 16) 1;
  nat_from_intseq_le_lemma0 (Seq.slice b 10 11);
  assert (nat_from_intseq_le (Seq.slice b 10 16) == b10 + pow2 8 * (nat_from_intseq_le (Seq.slice b 11 16)));
  
  nat_from_intseq_le_slice_lemma #U8 #SEC #5 (Seq.slice b 11 16) 1;
  nat_from_intseq_le_lemma0 (Seq.slice b 11 12);
  assert (nat_from_intseq_le (Seq.slice b 11 16) == b11 + pow2 8 * (nat_from_intseq_le (Seq.slice b 12 16)));
  
  nat_from_intseq_le_slice_lemma #U8 #SEC #4 (Seq.slice b 12 16) 1;
  nat_from_intseq_le_lemma0 (Seq.slice b 12 13);
  assert (nat_from_intseq_le (Seq.slice b 12 16) == b12 + pow2 8 * (nat_from_intseq_le (Seq.slice b 13 16)));
  
  nat_from_intseq_le_slice_lemma #U8 #SEC #3 (Seq.slice b 13 16) 1;
  nat_from_intseq_le_lemma0 (Seq.slice b 13 14);
  assert (nat_from_intseq_le (Seq.slice b 13 16) == b13 + pow2 8 * (nat_from_intseq_le (Seq.slice b 14 16)));
  
  nat_from_intseq_le_slice_lemma #U8 #SEC #2 (Seq.slice b 14 16) 1;
  nat_from_intseq_le_lemma0 (Seq.slice b 14 15);
  assert (nat_from_intseq_le (Seq.slice b 14 16) == b14 + pow2 8 * (nat_from_intseq_le (Seq.slice b 15 16)));

  nat_from_intseq_le_lemma0 (Seq.slice b 15 16)

val nat_from_intseq_le_be:
  b:LSeq.lseq uint8 16 ->
  Lemma (nat_from_intseq_le b == nat_from_intseq_be (u8_16_to_le b))

let nat_from_intseq_le_be b =
  unfold_nat_from_uint8_16_le b;
  unfold_nat_from_uint8_16 (u8_16_to_le b)

val nat_from_intseq_be_le:
  b:LSeq.lseq uint8 16 ->
  Lemma (nat_from_intseq_be b == nat_from_intseq_le (u8_16_to_le b))

let nat_from_intseq_be_le b =
  unfold_nat_from_uint8_16 b;
  unfold_nat_from_uint8_16_le (u8_16_to_le b)

val vec_xor_lemma_le_helper:
  b:LSeq.lseq uint8 16 ->
  Lemma (
    uints_to_bytes_be (uints_from_bytes_le #U128 #SEC #1 b) ==
    u8_16_to_le b)

let vec_xor_lemma_le_helper b =
  lemma_nat_from_to_intseq_be_preserves_value 1 (uints_from_bytes_le #U128 #SEC #1 b);
  assert (nat_to_intseq_be 1 (nat_from_intseq_be (uints_from_bytes_le #U128 #SEC #1 b)) ==
    uints_from_bytes_le #U128 #SEC #1 b);
  uints_to_bytes_be_nat_lemma #U128 #SEC 1 (nat_from_intseq_be (uints_from_bytes_le #U128 #SEC #1 b));
  assert (nat_to_bytes_be #SEC 16 (nat_from_intseq_be (uints_from_bytes_le #U128 #SEC #1 b)) ==
    uints_to_bytes_be #U128 #SEC #1 (nat_to_intseq_be #U128 #SEC 1 (nat_from_intseq_be (uints_from_bytes_le #U128 #SEC #1 b))));
  nat_from_intseq_be_lemma0 (uints_from_bytes_le #U128 #SEC #1 b);
  nat_from_intseq_le_lemma0 (uints_from_bytes_le #U128 #SEC #1 b);
  assert (nat_to_intseq_be #U8 #SEC 16 (nat_from_intseq_le (uints_from_bytes_le #U128 #SEC #1 b)) ==
    nat_to_intseq_be #U8 #SEC 16 (nat_from_intseq_be (uints_from_bytes_le #U128 #SEC #1 b)));
  uints_from_bytes_le_nat_lemma #U128 #SEC #1 b;
  assert (nat_to_intseq_be #U8 #SEC 16 (nat_from_bytes_le b) ==
    nat_to_intseq_be #U8 #SEC 16 (nat_from_intseq_le (uints_from_bytes_le #U128 #SEC #1 b)));
  nat_from_intseq_le_be b;
  lemma_nat_from_to_intseq_be_preserves_value #U8 #SEC 16 (u8_16_to_le b)

let uints_to_bytes_u8_16_le b =
  lemma_nat_from_to_intseq_le_preserves_value 1 b;
  assert (nat_to_intseq_le 1 (nat_from_intseq_le b) == b);
  uints_to_bytes_le_nat_lemma #U128 #SEC 1 (nat_from_intseq_le b);
  assert (nat_to_bytes_le 16 (nat_from_intseq_le b) == uints_to_bytes_le #U128 #SEC #1 b);
  nat_from_intseq_be_lemma0 b;
  nat_from_intseq_le_lemma0 b;
  assert (nat_to_bytes_le 16 (nat_from_intseq_be b) == uints_to_bytes_le #U128 #SEC #1 b);
  lemma_nat_to_from_bytes_be_preserves_value #SEC (nat_to_bytes_be #SEC 16 (nat_from_intseq_be b)) 16 (nat_from_intseq_be b);
  assert (nat_to_bytes_le 16 (nat_from_bytes_be (nat_to_bytes_be #SEC 16 (nat_from_intseq_be b))) == nat_to_bytes_le #SEC 16 (nat_from_intseq_be b));
  nat_from_intseq_be_le (nat_to_bytes_be #SEC 16 (nat_from_intseq_be b));
  assert (uints_to_bytes_le #U128 #SEC #1 b == nat_to_bytes_le #SEC 16 (nat_from_bytes_le (u8_16_to_le (nat_to_bytes_be #SEC 16 (nat_from_intseq_be b)))));
  lemma_nat_from_to_bytes_le_preserves_value (u8_16_to_le (nat_to_bytes_be #SEC 16 (nat_from_intseq_be b))) 16;
  assert (uints_to_bytes_le #U128 #SEC #1 b == u8_16_to_le (nat_to_bytes_be #SEC 16 (nat_from_intseq_be b)));
  uints_to_bytes_be_nat_lemma #U128 #SEC 1 (nat_from_intseq_be b);
  assert (uints_to_bytes_le #U128 #SEC #1 b == u8_16_to_le (uints_to_bytes_be #U128 #SEC #1 (nat_to_intseq_be 1 (nat_from_intseq_be b))));
  lemma_nat_from_to_intseq_be_preserves_value 1 b

let vec_xor_lemma_le b1 b2 =
  vec_xor_lemma (uints_from_bytes_le b1) b2;
  assert (LSeq.map2 (logxor #U8) (uints_to_bytes_be (uints_from_bytes_le b1)) (uints_to_bytes_be b2) ==
    uints_to_bytes_be (LSeq.map2 ( ^. ) (uints_from_bytes_le b1) b2));
  vec_xor_lemma_le_helper b1;
  assert (u8_16_to_le ((LSeq.map2 (logxor #U8) (u8_16_to_le b1)) (uints_to_bytes_be b2)) ==
    u8_16_to_le (uints_to_bytes_be (LSeq.map2 ( ^. ) (uints_from_bytes_le b1) b2)));
  uints_to_bytes_u8_16_le (LSeq.map2 ( ^. ) (uints_from_bytes_le b1) b2)

let shift_l_32_s (x:elem_s) : elem_s =
  let r4 = LSeq.index x 4 in
  let r5 = LSeq.index x 5 in
  let r6 = LSeq.index x 6 in
  let r7 = LSeq.index x 7 in
  let r8 = LSeq.index x 8 in
  let r9 = LSeq.index x 9 in
  let r10 = LSeq.index x 10 in
  let r11 = LSeq.index x 11 in
  let r12 = LSeq.index x 12 in
  let r13 = LSeq.index x 13 in
  let r14 = LSeq.index x 14 in
  let r15 = LSeq.index x 15 in
  LSeq.create16 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 (u8 0) (u8 0) (u8 0) (u8 0)

val shift_l_32_s_lemma: x:elem_s -> Lemma
  ((v (to_elem x) * pow2 32) % pow2 128 == v (to_elem (shift_l_32_s x)))

#push-options "--split_queries always"
let shift_l_32_s_lemma x =
  assert ((v (to_elem x) * pow2 32) % pow2 128 == v (to_elem (shift_l_32_s x)))
#pop-options

let vec_shift_l_32_lemma p b =
  let x = uints_to_bytes_be b in
  shift_l_32_s_lemma x;
  assert ((v (to_elem x) * pow2 32) % pow2 128 == v (shift_left (to_elem x) (size 32)));
  assert (v (shift_left (to_elem x) (size 32)) == v (to_elem (shift_l_32_s x)));
  nat_from_intseq_be_lemma0 (LSeq.map (shift_left_i (size 32)) b);
  assert (nat_from_intseq_be (LSeq.map (shift_left_i (size 32)) b) ==
    v (shift_left (LSeq.index #uint128 #1 b 0) (size 32)));
  vec_u128_bytes_nat b;
  assert (nat_from_intseq_be b == nat_from_bytes_be x);
  unfold_nat_from_uint8_16 x;
  assert (nat_from_intseq_be b == v (to_elem x));
  assert (v (shift_left #U128 #SEC (mk_int (nat_from_intseq_be b)) (size 32)) ==
    v (to_elem (shift_l_32_s x)));
  nat_from_intseq_be_lemma0 b;
  assert (nat_from_intseq_be (LSeq.map (shift_left_i (size 32)) b) ==
    v (to_elem (shift_l_32_s x)));
  unfold_nat_from_uint8_16 (shift_l_32_s x);
  assert (nat_to_bytes_be #SEC 16 (nat_from_intseq_be (LSeq.map (shift_left_i (size 32)) b)) ==
    nat_to_bytes_be #SEC 16 (nat_from_intseq_be (shift_l_32_s x)));
  lemma_nat_from_to_intseq_be_preserves_value 16 (shift_l_32_s x);
  uints_to_bytes_be_nat_lemma #U128 #SEC 1 (nat_from_intseq_be (LSeq.map (shift_left_i (size 32)) b));
  assert (shift_l_32_s x == uints_to_bytes_be #U128 #SEC #1 (nat_to_intseq_be #U128 #SEC 1 (nat_from_intseq_be (LSeq.map (shift_left_i (size 32)) b))));
  lemma_nat_from_to_intseq_be_preserves_value 1 (LSeq.map (shift_left_i (size 32)) b);
  assert (shift_l_32_s x == uints_to_bytes_be (LSeq.map (shift_left_i (size 32)) b));
  LSeq.lemma_concat2 12 (LSeq.sub (LSeq.update_sub p 0 12 (LSeq.sub x 4 12)) 0 12)
    4 (LSeq.sub (LSeq.update_sub p 0 12 (LSeq.sub x 4 12)) 12 4)
    (LSeq.update_sub p 0 12 (LSeq.sub x 4 12));
  LSeq.eq_intro (shift_l_32_s x) (LSeq.update_sub p 0 12 (LSeq.sub x 4 12))

let vec_create4_3_lemma b =
  let m0 = LSeq.update_sub b 8 4 (LSeq.sub b 12 4) in
  let m = LSeq.update_sub m0 0 8 (LSeq.sub m0 8 8) in
  let m' = uints_from_bytes_be #U32 #SEC #4 m in
  unfold_nat_from_uint32_four m';
  assert (nat_from_intseq_be m' ==
    v (LSeq.index m' 3) + pow2 32 * (v (LSeq.index m' 2) +
    pow2 32 * (v (LSeq.index m' 1) + pow2 32 * v (LSeq.index m' 0))));
  index_uints_from_bytes_be #U32 #SEC #4 m 3;
  index_uints_from_bytes_be #U32 #SEC #4 m 2;
  index_uints_from_bytes_be #U32 #SEC #4 m 1;
  index_uints_from_bytes_be #U32 #SEC #4 m 0;
  lemma_reveal_uint_to_bytes_be #U32 #SEC (LSeq.sub m 12 4);
  lemma_reveal_uint_to_bytes_be #U32 #SEC (LSeq.sub m 8 4);
  lemma_reveal_uint_to_bytes_be #U32 #SEC (LSeq.sub m 4 4);
  lemma_reveal_uint_to_bytes_be #U32 #SEC (LSeq.sub m 0 4);
  assert (v (LSeq.index m' 3) == nat_from_bytes_be (LSeq.sub m 12 4));
  assert (v (LSeq.index m' 2) == nat_from_bytes_be (LSeq.sub m 8 4));
  assert (v (LSeq.index m' 1) == nat_from_bytes_be (LSeq.sub m 4 4));
  assert (v (LSeq.index m' 0) == nat_from_bytes_be (LSeq.sub m 0 4));
  LSeq.eq_intro (LSeq.sub m 12 4) (LSeq.sub b 12 4);
  LSeq.eq_intro (LSeq.sub m 8 4) (LSeq.sub b 12 4);
  LSeq.lemma_concat2 4 (LSeq.sub (LSeq.sub m 0 8) 0 4)
    4 (LSeq.sub (LSeq.sub m 0 8) 4 4) (LSeq.sub m 0 8);
  LSeq.eq_intro (LSeq.sub m 4 4) (LSeq.sub b 12 4);
  LSeq.eq_intro (LSeq.sub m 0 4) (LSeq.sub b 12 4);
  uints_from_bytes_be_nat_lemma #U32 #SEC #4 m;
  assert (nat_from_bytes_be m ==
    nat_from_bytes_be (LSeq.sub b 12 4) +
    pow2 32 * (nat_from_bytes_be (LSeq.sub b 12 4) +
    pow2 32 * (nat_from_bytes_be (LSeq.sub b 12 4) +
    pow2 32 * nat_from_bytes_be (LSeq.sub b 12 4))));

  let n = uints_from_bytes_be #U32 #SEC #4 b in
  let i = LSeq.index n 3 in
  let n' = LSeq.create4 i i i i in
  unfold_nat_from_uint32_four n';
  assert (nat_from_intseq_be n' ==
    v (LSeq.index n' 3) + pow2 32 * (v (LSeq.index n' 2) +
    pow2 32 * (v (LSeq.index n' 1) + pow2 32 * v (LSeq.index n' 0))));
  assert (LSeq.index n' 3 == LSeq.index n 3);
  assert (LSeq.index n' 2 == LSeq.index n 3);
  assert (LSeq.index n' 1 == LSeq.index n 3);
  assert (LSeq.index n' 0 == LSeq.index n 3);
  index_uints_from_bytes_be #U32 #SEC #4 b 3;
  lemma_reveal_uint_to_bytes_be #U32 #SEC (LSeq.sub b 12 4);
  assert (nat_from_intseq_be n' ==
    nat_from_bytes_be (LSeq.sub b 12 4) +
    pow2 32 * (nat_from_bytes_be (LSeq.sub b 12 4) +
    pow2 32 * (nat_from_bytes_be (LSeq.sub b 12 4) +
    pow2 32 * nat_from_bytes_be (LSeq.sub b 12 4))));

  let u = uints_to_bytes_be n' in
  assert (nat_from_intseq_be n' == nat_from_bytes_be m);
  lemma_nat_from_to_intseq_be_preserves_value #U32 #SEC 4 n';
  assert (nat_to_intseq_be #U32 #SEC 4 (nat_from_intseq_be #U32 #SEC n') == n');
  assert (u == uints_to_bytes_be #U32 #SEC #4 (nat_to_intseq_be #U32 #SEC 4 (nat_from_intseq_be #U32 #SEC n')));
  assert (u == uints_to_bytes_be #U32 #SEC #4 (nat_to_intseq_be #U32 #SEC 4 (nat_from_bytes_be m)));
  uints_to_bytes_be_nat_lemma #U32 #SEC 4 (nat_from_bytes_be m);
  assert (u == nat_to_bytes_be 16 (nat_from_bytes_be m));
  lemma_nat_from_to_bytes_be_preserves_value m 16;
  assert (u == m)

let vec_create4_2_lemma b =
  let m0 = LSeq.update_sub b 12 4 (LSeq.sub b 8 4) in
  let m = LSeq.update_sub m0 0 8 (LSeq.sub m0 8 8) in
  let m' = uints_from_bytes_be #U32 #SEC #4 m in
  unfold_nat_from_uint32_four m';
  assert (nat_from_intseq_be m' ==
    v (LSeq.index m' 3) + pow2 32 * (v (LSeq.index m' 2) +
    pow2 32 * (v (LSeq.index m' 1) + pow2 32 * v (LSeq.index m' 0))));
  index_uints_from_bytes_be #U32 #SEC #4 m 3;
  index_uints_from_bytes_be #U32 #SEC #4 m 2;
  index_uints_from_bytes_be #U32 #SEC #4 m 1;
  index_uints_from_bytes_be #U32 #SEC #4 m 0;
  lemma_reveal_uint_to_bytes_be #U32 #SEC (LSeq.sub m 12 4);
  lemma_reveal_uint_to_bytes_be #U32 #SEC (LSeq.sub m 8 4);
  lemma_reveal_uint_to_bytes_be #U32 #SEC (LSeq.sub m 4 4);
  lemma_reveal_uint_to_bytes_be #U32 #SEC (LSeq.sub m 0 4);
  assert (v (LSeq.index m' 3) == nat_from_bytes_be (LSeq.sub m 12 4));
  assert (v (LSeq.index m' 2) == nat_from_bytes_be (LSeq.sub m 8 4));
  assert (v (LSeq.index m' 1) == nat_from_bytes_be (LSeq.sub m 4 4));
  assert (v (LSeq.index m' 0) == nat_from_bytes_be (LSeq.sub m 0 4));
  LSeq.eq_intro (LSeq.sub m 12 4) (LSeq.sub b 8 4);
  LSeq.eq_intro (LSeq.sub m 8 4) (LSeq.sub b 8 4);
  LSeq.lemma_concat2 4 (LSeq.sub (LSeq.sub m 0 8) 0 4)
    4 (LSeq.sub (LSeq.sub m 0 8) 4 4) (LSeq.sub m 0 8);
  LSeq.eq_intro (LSeq.sub m 4 4) (LSeq.sub b 8 4);
  LSeq.eq_intro (LSeq.sub m 0 4) (LSeq.sub b 8 4);
  uints_from_bytes_be_nat_lemma #U32 #SEC #4 m;
  assert (nat_from_bytes_be m ==
    nat_from_bytes_be (LSeq.sub b 8 4) +
    pow2 32 * (nat_from_bytes_be (LSeq.sub b 8 4) +
    pow2 32 * (nat_from_bytes_be (LSeq.sub b 8 4) +
    pow2 32 * nat_from_bytes_be (LSeq.sub b 8 4))));

  let n = uints_from_bytes_be #U32 #SEC #4 b in
  let i = LSeq.index n 2 in
  let n' = LSeq.create4 i i i i in
  unfold_nat_from_uint32_four n';
  assert (nat_from_intseq_be n' ==
    v (LSeq.index n' 3) + pow2 32 * (v (LSeq.index n' 2) +
    pow2 32 * (v (LSeq.index n' 1) + pow2 32 * v (LSeq.index n' 0))));
  assert (LSeq.index n' 3 == LSeq.index n 2);
  assert (LSeq.index n' 2 == LSeq.index n 2);
  assert (LSeq.index n' 1 == LSeq.index n 2);
  assert (LSeq.index n' 0 == LSeq.index n 2);
  index_uints_from_bytes_be #U32 #SEC #4 b 2;
  lemma_reveal_uint_to_bytes_be #U32 #SEC (LSeq.sub b 8 4);
  assert (nat_from_intseq_be n' ==
    nat_from_bytes_be (LSeq.sub b 8 4) +
    pow2 32 * (nat_from_bytes_be (LSeq.sub b 8 4) +
    pow2 32 * (nat_from_bytes_be (LSeq.sub b 8 4) +
    pow2 32 * nat_from_bytes_be (LSeq.sub b 8 4))));

  let u = uints_to_bytes_be n' in
  assert (nat_from_intseq_be n' == nat_from_bytes_be m);
  lemma_nat_from_to_intseq_be_preserves_value #U32 #SEC 4 n';
  assert (nat_to_intseq_be #U32 #SEC 4 (nat_from_intseq_be #U32 #SEC n') == n');
  assert (u == uints_to_bytes_be #U32 #SEC #4 (nat_to_intseq_be #U32 #SEC 4 (nat_from_intseq_be #U32 #SEC n')));
  assert (u == uints_to_bytes_be #U32 #SEC #4 (nat_to_intseq_be #U32 #SEC 4 (nat_from_bytes_be m)));
  uints_to_bytes_be_nat_lemma #U32 #SEC 4 (nat_from_bytes_be m);
  assert (u == nat_to_bytes_be 16 (nat_from_bytes_be m));
  lemma_nat_from_to_bytes_be_preserves_value m 16;
  assert (u == m)

let uints_bytes_le_lemma b =
  lemma_nat_from_to_intseq_le_preserves_value 1 (uints_from_bytes_le #U128 #SEC #1 b);
  assert (nat_to_intseq_le 1 (nat_from_intseq_le (uints_from_bytes_le #U128 #SEC #1 b)) ==
    uints_from_bytes_le #U128 #SEC #1 b);
  uints_from_bytes_le_nat_lemma #U128 #SEC #1 b;
  assert (nat_to_intseq_le 1 (nat_from_bytes_le b) ==
    uints_from_bytes_le #U128 #SEC #1 b);
  uints_to_bytes_le_nat_lemma #U128 #SEC 1 (nat_from_bytes_le b);
  assert (nat_to_bytes_le 16 (nat_from_bytes_le b) ==
    uints_to_bytes_le (uints_from_bytes_le #U128 #SEC #1 b));
  lemma_nat_from_to_bytes_le_preserves_value b 16;
  uints_to_bytes_u8_16_le (uints_from_bytes_le #U128 #SEC #1 b)

let vec_u128_to_u8 b =
  let u = uints_from_bytes_be #U8 #SEC #16 (uints_to_bytes_be b) in
  lemma_nat_from_to_intseq_be_preserves_value 16 u;
  assert (nat_to_intseq_be 16 (nat_from_intseq_be u) == u);
  uints_from_bytes_be_nat_lemma #U8 #SEC #16 (uints_to_bytes_be b);
  assert (nat_to_intseq_be 16 (nat_from_bytes_be (uints_to_bytes_be b)) == u);
  lemma_nat_from_to_intseq_be_preserves_value 16 (uints_to_bytes_be b)

let vec_u8_16 b =
  let n = uints_from_bytes_be #U128 #SEC #1 (uints_to_bytes_be b) in
  lemma_nat_from_to_intseq_be_preserves_value 16 b;
  assert (nat_to_intseq_be 16 (nat_from_intseq_be b) == b);
  uints_to_bytes_be_nat_lemma #U8 #SEC 16 (nat_from_intseq_be b);
  assert (uints_to_bytes_be #U8 #SEC #16 (nat_to_intseq_be 16 (nat_from_intseq_be b)) ==
    nat_to_bytes_be #SEC 16 (nat_from_intseq_be b))
