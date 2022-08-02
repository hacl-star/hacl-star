module Hacl.Impl.K256.Qinv

open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Mul

open Lib.IntTypes
open Lib.Buffer

open Hacl.K256.Scalar

module ST = FStar.HyperStack.ST
module LSeq = Lib.Sequence

module S = Spec.K256
module SI = Hacl.Spec.K256.Qinv

module BE = Hacl.Impl.Exponentiation
module SD = Hacl.Spec.Bignum.Definitions

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

unfold
let linv_ctx (a:LSeq.lseq uint64 0) : Type0 = True

unfold
let linv (a:LSeq.lseq uint64 4) : Type0 =
  SD.bn_v #U64 #4 a < S.q

unfold
let refl (a:LSeq.lseq uint64 4{linv a}) : GTot S.qelem =
  SD.bn_v #U64 #4 a

inline_for_extraction noextract
let mk_to_k256_scalar_concrete_ops : BE.to_concrete_ops U64 4ul 0ul = {
  BE.t_spec = S.qelem;
  BE.concr_ops = SI.mk_nat_mod_concrete_ops;
  BE.linv_ctx = linv_ctx;
  BE.linv = linv;
  BE.refl = refl;
}


inline_for_extraction noextract
val one_mod : BE.lone_st U64 4ul 0ul mk_to_k256_scalar_concrete_ops
let one_mod ctx one = make_u64_4 one (u64 1, u64 0, u64 0, u64 0)


inline_for_extraction noextract
val mul_mod : BE.lmul_st U64 4ul 0ul mk_to_k256_scalar_concrete_ops
let mul_mod ctx x y xy = qmul xy x y


inline_for_extraction noextract
val sqr_mod : BE.lsqr_st U64 4ul 0ul mk_to_k256_scalar_concrete_ops
let sqr_mod ctx x xx = qsqr xx x


inline_for_extraction noextract
let mk_k256_scalar_concrete_ops : BE.concrete_ops U64 4ul 0ul = {
  BE.to = mk_to_k256_scalar_concrete_ops;
  BE.lone = one_mod;
  BE.lmul = mul_mod;
  BE.lsqr = sqr_mod;
}


val qsquare_times_in_place (out:qelem) (b:size_t) : Stack unit
  (requires fun h ->
    live h out /\ qe_lt_q h out)
  (ensures  fun h0 _ h1 -> modifies (loc out) h0 h1 /\ qe_lt_q h1 out /\
    qas_nat h1 out == SI.qsquare_times (qas_nat h0 out) (v b))

[@CInline]
let qsquare_times_in_place out b =
  BE.lexp_pow2_in_place 4ul 0ul mk_k256_scalar_concrete_ops (null uint64) out b


val qsquare_times (out a:qelem) (b:size_t) : Stack unit
  (requires fun h ->
    live h out /\ live h a /\ disjoint out a /\
    qe_lt_q h a)
  (ensures  fun h0 _ h1 -> modifies (loc out) h0 h1 /\ qe_lt_q h1 a /\
    qas_nat h1 out == SI.qsquare_times (qas_nat h0 a) (v b))

[@CInline]
let qsquare_times out a b =
  BE.lexp_pow2 4ul 0ul mk_k256_scalar_concrete_ops (null uint64) a b out


inline_for_extraction noextract
val qinv1 (f x_10 x_11 x_101 x_111 x_1001 x_1011 x_1101:qelem) : Stack unit
  (requires fun h ->
    live h f /\ live h x_10 /\ live h x_11 /\ live h x_101 /\
    live h x_111 /\ live h x_1001 /\ live h x_1011 /\ live h x_1101 /\
    disjoint f x_10 /\ disjoint f x_11 /\ disjoint f x_101 /\
    disjoint f x_111 /\ disjoint f x_1001 /\ disjoint f x_1011 /\
    disjoint f x_1101 /\ disjoint x_10 x_11 /\ disjoint x_10 x_101 /\
    disjoint x_10 x_111 /\ disjoint x_10 x_1001 /\ disjoint x_10 x_1011 /\
    disjoint x_10 x_1101 /\ disjoint x_11 x_101 /\ disjoint x_11 x_111 /\
    disjoint x_11 x_1001 /\ disjoint x_11 x_1011 /\ disjoint x_11 x_1101 /\
    disjoint x_101 x_111 /\ disjoint x_101 x_1001 /\ disjoint x_101 x_1011 /\
    disjoint x_101 x_1101 /\ disjoint x_111 x_1001 /\ disjoint x_111 x_1011 /\
    disjoint x_111 x_1101 /\ disjoint x_1001 x_1011 /\ disjoint x_1001 x_1101 /\
    disjoint x_1011 x_1101 /\ qe_lt_q h f)
  (ensures  fun h0 _ h1 ->
    modifies (loc x_10 |+| loc x_11 |+| loc x_101 |+|
      loc x_111 |+| loc x_1001 |+| loc x_1011 |+| loc x_1101) h0 h1 /\
   (let _x_10 = SI.qsquare_times (qas_nat h0 f) 1 in
    let _x_11 = S.qmul _x_10 (qas_nat h0 f) in
    let _x_101 = S.qmul _x_10 _x_11 in
    let _x_111 = S.qmul _x_10 _x_101 in
    let _x_1001 = S.qmul _x_10 _x_111 in
    let _x_1011 = S.qmul _x_10 _x_1001 in
    let _x_1101 = S.qmul _x_10 _x_1011 in
    qas_nat h1 x_10 == _x_10 /\ qe_lt_q h1 x_10 /\
    qas_nat h1 x_11 == _x_11 /\ qe_lt_q h1 x_11 /\
    qas_nat h1 x_101 == _x_101 /\ qe_lt_q h1 x_101 /\
    qas_nat h1 x_111 == _x_111 /\ qe_lt_q h1 x_111 /\
    qas_nat h1 x_1001 == _x_1001 /\ qe_lt_q h1 x_1001 /\
    qas_nat h1 x_1011 == _x_1011 /\ qe_lt_q h1 x_1011 /\
    qas_nat h1 x_1101 == _x_1101 /\ qe_lt_q h1 x_1101))

let qinv1 f x_10 x_11 x_101 x_111 x_1001 x_1011 x_1101 =
  let h0 = ST.get () in
  qsquare_times x_10 f 1ul;
  let h1 = ST.get () in
  assert (qas_nat h1 x_10 == SI.qsquare_times (qas_nat h0 f) 1);

  qmul x_11 x_10 f;
  let h2 = ST.get () in
  assert (qas_nat h2 x_11 == S.qmul (qas_nat h1 x_10) (qas_nat h0 f));

  qmul x_101 x_10 x_11;
  let h3 = ST.get () in
  assert (qas_nat h3 x_101 == S.qmul (qas_nat h1 x_10) (qas_nat h2 x_11));

  qmul x_111 x_10 x_101;
  let h4 = ST.get () in
  assert (qas_nat h4 x_111 == S.qmul (qas_nat h1 x_10) (qas_nat h3 x_101));

  qmul x_1001 x_10 x_111;
  let h5 = ST.get () in
  assert (qas_nat h5 x_1001 == S.qmul (qas_nat h1 x_10) (qas_nat h4 x_111));

  qmul x_1011 x_10 x_1001;
  let h6 = ST.get () in
  assert (qas_nat h6 x_1011 == S.qmul (qas_nat h1 x_10) (qas_nat h5 x_1001));

  qmul x_1101 x_10 x_1011;
  let h7 = ST.get () in
  assert (qas_nat h7 x_1101 == S.qmul (qas_nat h1 x_10) (qas_nat h6 x_1011))


inline_for_extraction noextract
val qinv2 (x_11 x_1011 x_1101 x6 x8 x14: qelem) : Stack unit
  (requires fun h ->
    live h x_11 /\ live h x_1011 /\ live h x_1101 /\
    live h x6 /\ live h x8 /\ live h x14 /\
    disjoint x_11 x6 /\ disjoint x_11 x8 /\ disjoint x_11 x14 /\
    disjoint x_1011 x6 /\ disjoint x_1011 x8 /\ disjoint x_1011 x14 /\
    disjoint x_1101 x6 /\ disjoint x_1101 x8 /\ disjoint x_1101 x14 /\
    disjoint x6 x8 /\ disjoint x6 x14 /\ disjoint x8 x14 /\
    qe_lt_q h x_11 /\ qe_lt_q h x_1011 /\ qe_lt_q h x_1101)
  (ensures fun h0 _ h1 -> modifies (loc x6 |+| loc x8 |+| loc x14) h0 h1 /\
   (let _x6 = S.qmul (SI.qsquare_times (qas_nat h0 x_1101) 2) (qas_nat h0 x_1011) in
    let _x8 = S.qmul (SI.qsquare_times _x6 2) (qas_nat h0 x_11) in
    let _x14 = S.qmul (SI.qsquare_times _x8 6) _x6 in
    qas_nat h1 x6 == _x6 /\ qe_lt_q h1 x6 /\
    qas_nat h1 x8 == _x8 /\ qe_lt_q h1 x8 /\
    qas_nat h1 x14 == _x14 /\ qe_lt_q h1 x14))

let qinv2 x_11 x_1011 x_1101 x6 x8 x14 =
  let h0 = ST.get () in
  qsquare_times x6 x_1101 2ul;
  qmul x6 x6 x_1011;
  let h1 = ST.get () in
  assert (qas_nat h1 x6 == S.qmul (SI.qsquare_times (qas_nat h0 x_1101) 2) (qas_nat h0 x_1011));

  qsquare_times x8 x6 2ul;
  qmul x8 x8 x_11;
  let h2 = ST.get () in
  assert (qas_nat h2 x8 == S.qmul (SI.qsquare_times (qas_nat h1 x6) 2) (qas_nat h0 x_11));

  qsquare_times x14 x8 6ul;
  qmul x14 x14 x6;
  let h3 = ST.get () in
  assert (qas_nat h3 x14 == S.qmul (SI.qsquare_times (qas_nat h2 x8) 6) (qas_nat h1 x6))


inline_for_extraction noextract
val qinv3 (tmp x14: qelem) : Stack unit
  (requires fun h ->
    live h tmp /\ live h x14 /\ disjoint tmp x14 /\
    qe_lt_q h x14)
  (ensures  fun h0 _ h1 -> modifies (loc tmp) h0 h1 /\
    qas_nat h1 tmp == SI.qinv_r0_r1 (qas_nat h0 x14) /\
    qe_lt_q h1 tmp)

let qinv3 tmp x14 =
  push_frame ();
  let x56 = create_qelem () in

  let h0 = ST.get () in
  qsquare_times tmp x14 14ul;
  qmul tmp tmp x14; //tmp = x28
  let h1 = ST.get () in
  assert (qas_nat h1 tmp == S.qmul (SI.qsquare_times (qas_nat h0 x14) 14) (qas_nat h0 x14));

  qsquare_times x56 tmp 28ul;
  qmul x56 x56 tmp;
  let h2 = ST.get () in
  assert (qas_nat h2 x56 == S.qmul (SI.qsquare_times (qas_nat h1 tmp) 28) (qas_nat h1 tmp));

  qsquare_times tmp x56 56ul; //tmp = r0
  qmul tmp tmp x56;
  let h3 = ST.get () in
  assert (qas_nat h3 tmp == S.qmul (SI.qsquare_times (qas_nat h2 x56) 56) (qas_nat h2 x56));

  qsquare_times_in_place tmp 14ul; //tmp = r1
  qmul tmp tmp x14;
  let h4 = ST.get () in
  assert (qas_nat h4 tmp == S.qmul (SI.qsquare_times (qas_nat h3 tmp) 14) (qas_nat h0 x14));
  pop_frame ()


//r2; .. ;r8
inline_for_extraction noextract
val qinv4 (tmp x_101 x_111 x_1011: qelem) : Stack unit
  (requires fun h ->
    live h tmp /\ live h x_101 /\ live h x_111 /\ live h x_1011 /\
    disjoint tmp x_101 /\ disjoint tmp x_111 /\ disjoint tmp x_1011 /\
    qe_lt_q h tmp /\ qe_lt_q h x_101 /\ qe_lt_q h x_111 /\ qe_lt_q h x_1011)
  (ensures  fun h0 _ h1 -> modifies (loc tmp) h0 h1 /\
    qas_nat h1 tmp == SI.qinv_r2_r8 (qas_nat h0 tmp)
      (qas_nat h0 x_101) (qas_nat h0 x_111) (qas_nat h0 x_1011) /\
    qe_lt_q h1 tmp)

let qinv4 tmp x_101 x_111 x_1011 =
  let h0 = ST.get () in
  qsquare_times_in_place tmp 3ul;
  qmul tmp tmp x_101; //tmp = r2
  let h1 = ST.get () in
  assert (qas_nat h1 tmp == S.qmul (SI.qsquare_times (qas_nat h0 tmp) 3) (qas_nat h0 x_101));

  qsquare_times_in_place tmp 4ul;
  qmul tmp tmp x_111; //tmp = r3
  let h2 = ST.get () in
  assert (qas_nat h2 tmp == S.qmul (SI.qsquare_times (qas_nat h1 tmp) 4) (qas_nat h0 x_111));

  qsquare_times_in_place tmp 4ul;
  qmul tmp tmp x_101; //tmp = r4
  let h3 = ST.get () in
  assert (qas_nat h3 tmp == S.qmul (SI.qsquare_times (qas_nat h2 tmp) 4) (qas_nat h0 x_101));

  qsquare_times_in_place tmp 5ul;
  qmul tmp tmp x_1011; //tmp = r5
  let h4 = ST.get () in
  assert (qas_nat h4 tmp == S.qmul (SI.qsquare_times (qas_nat h3 tmp) 5) (qas_nat h0 x_1011));

  qsquare_times_in_place tmp 4ul;
  qmul tmp tmp x_1011; //tmp = r6
  let h5 = ST.get () in
  assert (qas_nat h5 tmp == S.qmul (SI.qsquare_times (qas_nat h4 tmp) 4) (qas_nat h0 x_1011));

  qsquare_times_in_place tmp 4ul;
  qmul tmp tmp x_111; //tmp = r7
  let h6 = ST.get () in
  assert (qas_nat h6 tmp == S.qmul (SI.qsquare_times (qas_nat h5 tmp) 4) (qas_nat h0 x_111));

  qsquare_times_in_place tmp 5ul;
  qmul tmp tmp x_111; //tmp = r8
  let h7 = ST.get () in
  assert (qas_nat h7 tmp == S.qmul (SI.qsquare_times (qas_nat h6 tmp) 5) (qas_nat h0 x_111))


// r9; ..; r15
inline_for_extraction noextract
val qinv5 (tmp x_101 x_111 x_1001 x_1101: qelem) : Stack unit
  (requires fun h ->
    live h tmp /\ live h x_101 /\ live h x_111 /\
    live h x_1001 /\ live h x_1101 /\ disjoint tmp x_101 /\
    disjoint tmp x_111 /\ disjoint tmp x_1001 /\ disjoint tmp x_1101 /\
    qe_lt_q h tmp /\ qe_lt_q h x_101 /\ qe_lt_q h x_111 /\
    qe_lt_q h x_1001 /\ qe_lt_q h x_1101)
  (ensures  fun h0 _ h1 -> modifies (loc tmp) h0 h1 /\
    qas_nat h1 tmp == SI.qinv_r9_r15 (qas_nat h0 tmp)
      (qas_nat h0 x_101) (qas_nat h0 x_111) (qas_nat h0 x_1001) (qas_nat h0 x_1101) /\
    qe_lt_q h1 tmp)

let qinv5 tmp x_101 x_111 x_1001 x_1101 =
  let h0 = ST.get () in
  qsquare_times_in_place tmp 6ul;
  qmul tmp tmp x_1101; //tmp = r9
  let h1 = ST.get () in
  assert (qas_nat h1 tmp == S.qmul (SI.qsquare_times (qas_nat h0 tmp) 6) (qas_nat h0 x_1101));

  qsquare_times_in_place tmp 4ul;
  qmul tmp tmp x_101; //tmp = r10
  let h2 = ST.get () in
  assert (qas_nat h2 tmp == S.qmul (SI.qsquare_times (qas_nat h1 tmp) 4) (qas_nat h0 x_101));

  qsquare_times_in_place tmp 3ul;
  qmul tmp tmp x_111; //tmp = r11
  let h3 = ST.get () in
  assert (qas_nat h3 tmp == S.qmul (SI.qsquare_times (qas_nat h2 tmp) 3) (qas_nat h0 x_111));

  qsquare_times_in_place tmp 5ul;
  qmul tmp tmp x_1001; //tmp = r12
  let h4 = ST.get () in
  assert (qas_nat h4 tmp == S.qmul (SI.qsquare_times (qas_nat h3 tmp) 5) (qas_nat h0 x_1001));

  qsquare_times_in_place tmp 6ul;
  qmul tmp tmp x_101; //tmp = r13
  let h5 = ST.get () in
  assert (qas_nat h5 tmp == S.qmul (SI.qsquare_times (qas_nat h4 tmp) 6) (qas_nat h0 x_101));

  qsquare_times_in_place tmp 10ul;
  qmul tmp tmp x_111; //tmp = r14
  let h6 = ST.get () in
  assert (qas_nat h6 tmp == S.qmul (SI.qsquare_times (qas_nat h5 tmp) 10) (qas_nat h0 x_111));

  qsquare_times_in_place tmp 4ul;
  qmul tmp tmp x_111; //tmp = r15
  let h7 = ST.get () in
  assert (qas_nat h7 tmp == S.qmul (SI.qsquare_times (qas_nat h6 tmp) 4) (qas_nat h0 x_111))


// r16; ..;r23
inline_for_extraction noextract
val qinv6 (tmp x8 x_11 x_1001 x_1011 x_1101: qelem) : Stack unit
  (requires fun h ->
    live h tmp /\ live h x8 /\ live h x_11 /\
    live h x_1001 /\ live h x_1011 /\ live h x_1101 /\
    disjoint tmp x8 /\ disjoint tmp x_11 /\ disjoint tmp x_1001 /\
    disjoint tmp x_1011 /\ disjoint tmp x_1101 /\
    qe_lt_q h tmp /\ qe_lt_q h x8 /\ qe_lt_q h x_11 /\
    qe_lt_q h x_1001 /\ qe_lt_q h x_1011 /\ qe_lt_q h x_1101)
  (ensures  fun h0 _ h1 -> modifies (loc tmp) h0 h1 /\
    qas_nat h1 tmp == SI.qinv_r16_r23 (qas_nat h0 tmp)
      (qas_nat h0 x8) (qas_nat h0 x_11) (qas_nat h0 x_1001) (qas_nat h0 x_1011) (qas_nat h0 x_1101) /\
    qe_lt_q h1 tmp)

let qinv6 tmp x8 x_11 x_1001 x_1011 x_1101 =
  let h0 = ST.get () in
  qsquare_times_in_place tmp 9ul;
  qmul tmp tmp x8; //tmp = r16
  let h1 = ST.get () in
  assert (qas_nat h1 tmp == S.qmul (SI.qsquare_times (qas_nat h0 tmp) 9) (qas_nat h0 x8));

  qsquare_times_in_place tmp 5ul;
  qmul tmp tmp x_1001; //tmp = r17
  let h2 = ST.get () in
  assert (qas_nat h2 tmp == S.qmul (SI.qsquare_times (qas_nat h1 tmp) 5) (qas_nat h0 x_1001));

  qsquare_times_in_place tmp 6ul;
  qmul tmp tmp x_1011; //tmp = r18
  let h3 = ST.get () in
  assert (qas_nat h3 tmp == S.qmul (SI.qsquare_times (qas_nat h2 tmp) 6) (qas_nat h0 x_1011));

  qsquare_times_in_place tmp 4ul;
  qmul tmp tmp x_1101; //tmp = r19
  let h4 = ST.get () in
  assert (qas_nat h4 tmp == S.qmul (SI.qsquare_times (qas_nat h3 tmp) 4) (qas_nat h0 x_1101));

  qsquare_times_in_place tmp 5ul;
  qmul tmp tmp x_11; //tmp = r20
  let h5 = ST.get () in
  assert (qas_nat h5 tmp == S.qmul (SI.qsquare_times (qas_nat h4 tmp) 5) (qas_nat h0 x_11));

  qsquare_times_in_place tmp 6ul;
  qmul tmp tmp x_1101; //tmp = r21
  let h6 = ST.get () in
  assert (qas_nat h6 tmp == S.qmul (SI.qsquare_times (qas_nat h5 tmp) 6) (qas_nat h0 x_1101));

  qsquare_times_in_place tmp 10ul;
  qmul tmp tmp x_1101; //tmp = r22
  let h7 = ST.get () in
  assert (qas_nat h7 tmp == S.qmul (SI.qsquare_times (qas_nat h6 tmp) 10) (qas_nat h0 x_1101));

  qsquare_times_in_place tmp 4ul;
  qmul tmp tmp x_1001; //tmp = r23
  let h8 = ST.get () in
  assert (qas_nat h8 tmp == S.qmul (SI.qsquare_times (qas_nat h7 tmp) 4) (qas_nat h0 x_1001))


//r24; r25
inline_for_extraction noextract
val qinv7 (tmp f x6: qelem) : Stack unit
  (requires fun h ->
    live h tmp /\ live h f /\ live h x6 /\
    disjoint tmp f /\ disjoint tmp x6 /\
    qe_lt_q h tmp /\ qe_lt_q h f /\ qe_lt_q h x6)
  (ensures  fun h0 _ h1 -> modifies (loc tmp) h0 h1 /\
    qas_nat h1 tmp == SI.qinv_r24_r25 (qas_nat h0 tmp) (qas_nat h0 f) (qas_nat h0 x6) /\
    qe_lt_q h1 tmp)

let qinv7 tmp f x6 =
  let h0 = ST.get () in
  qsquare_times_in_place tmp 6ul;
  qmul tmp tmp f; //tmp = r23
  let h1 = ST.get () in
  assert (qas_nat h1 tmp == S.qmul (SI.qsquare_times (qas_nat h0 tmp) 6) (qas_nat h0 f));

  qsquare_times_in_place tmp 8ul;
  qmul tmp tmp x6; //tmp = r24
  let h2 = ST.get () in
  assert (qas_nat h2 tmp == S.qmul (SI.qsquare_times (qas_nat h1 tmp) 8) (qas_nat h0 x6))


inline_for_extraction noextract
val qinv8 (tmp f x_11 x_101 x_111 x_1001 x_1011 x_1101: qelem) : Stack unit
  (requires fun h ->
    live h tmp /\ live h f /\ live h x_11 /\
    live h x_101 /\ live h x_111 /\ live h x_1001 /\
    live h x_1011 /\ live h x_1101 /\
    disjoint tmp f /\ disjoint tmp x_11 /\ disjoint tmp x_101 /\
    disjoint tmp x_111 /\ disjoint tmp x_1001 /\ disjoint tmp x_1011 /\
    disjoint tmp x_1101 /\
    qe_lt_q h f /\ qe_lt_q h x_11 /\ qe_lt_q h x_101 /\
    qe_lt_q h x_111 /\ qe_lt_q h x_1001 /\ qe_lt_q h x_1011 /\
    qe_lt_q h x_1101)
  (ensures  fun h0 _ h1 -> modifies (loc tmp) h0 h1 /\
    qas_nat h1 tmp == SI.qinv_r0_r25 (qas_nat h0 f)
      (qas_nat h0 x_11) (qas_nat h0 x_101) (qas_nat h0 x_111)
      (qas_nat h0 x_1001) (qas_nat h0 x_1011) (qas_nat h0 x_1101) /\
    qe_lt_q h1 tmp)

let qinv8 tmp f x_11 x_101 x_111 x_1001 x_1011 x_1101 =
  push_frame ();
  let x6 = create_qelem () in
  let x8 = create_qelem () in
  let x14 = create_qelem () in

  let h1 = ST.get () in
  qinv2 x_11 x_1011 x_1101 x6 x8 x14; //x6; x8; x14
  let h2 = ST.get () in
  assert (modifies (loc x6 |+| loc x8 |+| loc x14) h1 h2);

  qinv3 tmp x14; //x28; x56; r0; r1
  let h3 = ST.get () in
  assert (modifies (loc tmp) h2 h3);

  qinv4 tmp x_101 x_111 x_1011; //r2; ..; r8
  let h4 = ST.get () in
  assert (modifies (loc tmp) h3 h4);

  qinv5 tmp x_101 x_111 x_1001 x_1101; //r9; ..; r15
  let h5 = ST.get () in
  assert (modifies (loc tmp) h4 h5);

  qinv6 tmp x8 x_11 x_1001 x_1011 x_1101; //r16; ..; r23
  let h6 = ST.get () in
  assert (modifies (loc tmp) h5 h6);

  qinv7 tmp f x6; //r24; r25
  let h7 = ST.get () in
  assert (modifies (loc tmp) h6 h7);
  pop_frame ()


inline_for_extraction noextract
val qinv_ (out f: qelem) : Stack unit
  (requires fun h ->
    live h out /\ live h f /\ disjoint out f /\
    qe_lt_q h f)
  (ensures  fun h0 _ h1 -> modifies (loc out) h0 h1 /\
    qas_nat h1 out == SI.qinv (qas_nat h0 f)  /\
    qe_lt_q h1 out)

#set-options "--z3rlimit 150"

let qinv_ out f =
  push_frame ();
  let x_10 = create_qelem () in
  let x_11 = create_qelem () in
  let x_101 = create_qelem () in
  let x_111 = create_qelem () in
  let x_1001 = create_qelem () in
  let x_1011 = create_qelem () in
  let x_1101 = create_qelem () in

  qinv1 f x_10 x_11 x_101 x_111 x_1001 x_1011 x_1101;
  qinv8 out f x_11 x_101 x_111 x_1001 x_1011 x_1101;
  pop_frame ()


val qinv (out f: qelem) : Stack unit
  (requires fun h ->
    live h out /\ live h f /\ disjoint out f /\
    qe_lt_q h f)
  (ensures  fun h0 _ h1 -> modifies (loc out) h0 h1 /\
    qas_nat h1 out == S.qinv (qas_nat h0 f)  /\
    qe_lt_q h1 out)

[@CInline]
let qinv out f =
  let h0 = ST.get () in
  SI.qinv_is_qinv_lemma (qas_nat h0 f);
  qinv_ out f
