module Hacl.Impl.P256.Qinv

open FStar.Mul
open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer

open Hacl.Impl.P256.Bignum
open Hacl.Impl.P256.Scalar

module SE = Spec.Exponentiation
module BE = Hacl.Impl.Exponentiation
module BD = Hacl.Spec.Bignum.Definitions
module LSeq = Lib.Sequence

module S = Spec.P256
module SI = Hacl.Spec.P256.Qinv
module SM = Hacl.Spec.P256.Montgomery

#reset-options "--z3rlimit 50 --fuel 0 --ifuel 0"

unfold
let linv_ctx (a:LSeq.lseq uint64 0) : Type0 = True

unfold
let linv (a:LSeq.lseq uint64 4) : Type0 =
  BD.bn_v a < S.order

unfold
let refl (a:LSeq.lseq uint64 4{linv a}) : GTot S.qelem =
  SM.from_qmont (BD.bn_v a)


inline_for_extraction noextract
let mk_to_p256_order_comm_monoid : BE.to_comm_monoid U64 4ul 0ul = {
  BE.a_spec = S.qelem;
  BE.comm_monoid = SI.nat_mod_comm_monoid;
  BE.linv_ctx = linv_ctx;
  BE.linv = linv;
  BE.refl = refl;
}

inline_for_extraction noextract
val one_mod : BE.lone_st U64 4ul 0ul mk_to_p256_order_comm_monoid
let one_mod ctx one = make_qone one


inline_for_extraction noextract
val mul_mod : BE.lmul_st U64 4ul 0ul mk_to_p256_order_comm_monoid
let mul_mod ctx x y xy = qmul xy x y


inline_for_extraction noextract
val sqr_mod : BE.lsqr_st U64 4ul 0ul mk_to_p256_order_comm_monoid
let sqr_mod ctx x xx = qsqr xx x


inline_for_extraction noextract
let mk_p256_order_concrete_ops : BE.concrete_ops U64 4ul 0ul = {
  BE.to = mk_to_p256_order_comm_monoid;
  BE.lone = one_mod;
  BE.lmul = mul_mod;
  BE.lsqr = sqr_mod;
}


inline_for_extraction noextract
val qsquare_times_in_place (out:felem) (b:size_t) : Stack unit
  (requires fun h ->
    live h out /\ as_nat h out < S.order)
  (ensures  fun h0 _ h1 -> modifies (loc out) h0 h1 /\
    as_nat h1 out < S.order /\
    qmont_as_nat h1 out == SI.qsquare_times (qmont_as_nat h0 out) (v b))

let qsquare_times_in_place out b =
  let h0 = ST.get () in
  SE.exp_pow2_lemma SI.mk_nat_mod_concrete_ops (qmont_as_nat h0 out) (v b);
  BE.lexp_pow2_in_place 4ul 0ul mk_p256_order_concrete_ops (null uint64) out b


inline_for_extraction noextract
val qsquare_times (out a:felem) (b:size_t) : Stack unit
  (requires fun h ->
    live h out /\ live h a /\ disjoint out a /\
    as_nat h a < S.order)
  (ensures  fun h0 _ h1 -> modifies (loc out) h0 h1 /\
    as_nat h1 out < S.order /\
    qmont_as_nat h1 out == SI.qsquare_times (qmont_as_nat h0 a) (v b))

let qsquare_times out a b =
  let h0 = ST.get () in
  SE.exp_pow2_lemma SI.mk_nat_mod_concrete_ops (qmont_as_nat h0 a) (v b);
  BE.lexp_pow2 4ul 0ul mk_p256_order_concrete_ops (null uint64) a b out


// x6 can be modified
// x_11 cannot be modified
inline_for_extraction noextract
val qinv_x8_x128 (x128 x6 x_11:felem) : Stack unit
  (requires fun h ->
    live h x128 /\ live h x6 /\ live h x_11 /\
    disjoint x128 x6 /\ disjoint x128 x_11 /\ disjoint x6 x_11 /\
    as_nat h x6 < S.order /\ as_nat h x_11 < S.order)
  (ensures fun h0 _ h1 -> modifies (loc x128 |+| loc x6) h0 h1 /\
    as_nat h1 x128 < S.order /\
    qmont_as_nat h1 x128 = SI.qinv_x8_x128 (qmont_as_nat h0 x6) (qmont_as_nat h0 x_11))

let qinv_x8_x128 x128 x6 x_11 =
  let h0 = ST.get () in
  qsquare_times_in_place x6 2ul;
  qmul x6 x6 x_11;
  let h1 = ST.get () in
  assert (qmont_as_nat h1 x6 == // x8
    S.qmul (SI.qsquare_times (qmont_as_nat h0 x6) 2) (qmont_as_nat h0 x_11));

  qsquare_times x128 x6 8ul;
  qmul x128 x128 x6;
  let h2 = ST.get () in
  assert (qmont_as_nat h2 x128 == // x16
    S.qmul (SI.qsquare_times (qmont_as_nat h1 x6) 8) (qmont_as_nat h1 x6));

  qsquare_times x6 x128 16ul;
  qmul x6 x6 x128;
  let h3 = ST.get () in
  assert (qmont_as_nat h3 x6 == // x32
    S.qmul (SI.qsquare_times (qmont_as_nat h2 x128) 16) (qmont_as_nat h2 x128));

  qsquare_times x128 x6 64ul;
  qmul x128 x128 x6;
  let h4 = ST.get () in
  assert (qmont_as_nat h4 x128 == // x96
    S.qmul (SI.qsquare_times (qmont_as_nat h3 x6) 64) (qmont_as_nat h3 x6));

  qsquare_times_in_place x128 32ul;
  qmul x128 x128 x6;
  let h5 = ST.get () in
  assert (qmont_as_nat h5 x128 == // x128
    S.qmul (SI.qsquare_times (qmont_as_nat h4 x128) 32) (qmont_as_nat h3 x6))


// x128 can be modified
inline_for_extraction noextract
val qinv_x134_x153 (x128 x_11 x_111 x_1111 x_10101 x_101111:felem) : Stack unit
  (requires fun h ->
    live h x128 /\ live h x_11 /\ live h x_111 /\
    live h x_1111 /\ live h x_10101 /\ live h x_101111 /\
    disjoint x128 x_11 /\ disjoint x128 x_111 /\ disjoint x128 x_1111 /\
    disjoint x128 x_10101 /\ disjoint x128 x_101111 /\
    as_nat h x128 < S.order /\ as_nat h x_11 < S.order /\
    as_nat h x_111 < S.order /\ as_nat h x_1111 < S.order /\
    as_nat h x_10101 < S.order /\ as_nat h x_101111 < S.order)
  (ensures fun h0 _ h1 -> modifies (loc x128) h0 h1 /\
    as_nat h1 x128 < S.order /\
    qmont_as_nat h1 x128 = SI.qinv_x134_x153
      (qmont_as_nat h0 x128) (qmont_as_nat h0 x_11) (qmont_as_nat h0 x_111)
        (qmont_as_nat h0 x_1111) (qmont_as_nat h0 x_10101) (qmont_as_nat h0 x_101111))

let qinv_x134_x153 x128 x_11 x_111 x_1111 x_10101 x_101111 =
  let h0 = ST.get () in
  qsquare_times_in_place x128 6ul;
  qmul x128 x128 x_101111;
  let h1 = ST.get () in
  assert (qmont_as_nat h1 x128 == // x134
    S.qmul (SI.qsquare_times (qmont_as_nat h0 x128) 6) (qmont_as_nat h0 x_101111));

  qsquare_times_in_place x128 5ul;
  qmul x128 x128 x_111;
  let h2 = ST.get () in
  assert (qmont_as_nat h2 x128 == // x139
    S.qmul (SI.qsquare_times (qmont_as_nat h1 x128) 5) (qmont_as_nat h0 x_111));

  qsquare_times_in_place x128 4ul;
  qmul x128 x128 x_11;
  let h3 = ST.get () in
  assert (qmont_as_nat h3 x128 == // x143
    S.qmul (SI.qsquare_times (qmont_as_nat h2 x128) 4) (qmont_as_nat h0 x_11));

  qsquare_times_in_place x128 5ul;
  qmul x128 x128 x_1111;
  let h4 = ST.get () in
  assert (qmont_as_nat h4 x128 == // x148
    S.qmul (SI.qsquare_times (qmont_as_nat h3 x128) 5) (qmont_as_nat h0 x_1111));

  qsquare_times_in_place x128 5ul;
  qmul x128 x128 x_10101;
  let h5 = ST.get () in
  assert (qmont_as_nat h5 x128 == // x153
    S.qmul (SI.qsquare_times (qmont_as_nat h4 x128) 5) (qmont_as_nat h0 x_10101))


// x153 can be modified
inline_for_extraction noextract
val qinv_x153_x177 (x153 x_101 x_111 x_101111:felem) : Stack unit
  (requires fun h ->
    live h x153 /\ live h x_101 /\ live h x_111 /\ live h x_101111 /\
    disjoint x153 x_101 /\ disjoint x153 x_111 /\ disjoint x153 x_101111 /\
    as_nat h x153 < S.order /\ as_nat h x_101 < S.order /\
    as_nat h x_111 < S.order /\ as_nat h x_101111 < S.order)
  (ensures fun h0 _ h1 -> modifies (loc x153) h0 h1 /\
    as_nat h1 x153 < S.order /\
    qmont_as_nat h1 x153 = SI.qinv_x153_x177 (qmont_as_nat h0 x153)
      (qmont_as_nat h0 x_101) (qmont_as_nat h0 x_111) (qmont_as_nat h0 x_101111))

let qinv_x153_x177 x153 x_101 x_111 x_101111 =
  let h0 = ST.get () in
  qsquare_times_in_place x153 4ul;
  qmul x153 x153 x_101;
  let h1 = ST.get () in
  assert (qmont_as_nat h1 x153 == // x157
    S.qmul (SI.qsquare_times (qmont_as_nat h0 x153) 4) (qmont_as_nat h0 x_101));

  qsquare_times_in_place x153 3ul;
  qmul x153 x153 x_101;
  let h2 = ST.get () in
  assert (qmont_as_nat h2 x153 == // x160
    S.qmul (SI.qsquare_times (qmont_as_nat h1 x153) 3) (qmont_as_nat h0 x_101));

  qsquare_times_in_place x153 3ul;
  qmul x153 x153 x_101;
  let h3 = ST.get () in
  assert (qmont_as_nat h3 x153 == // x163
    S.qmul (SI.qsquare_times (qmont_as_nat h2 x153) 3) (qmont_as_nat h0 x_101));

  qsquare_times_in_place x153 5ul;
  qmul x153 x153 x_111;
  let h4 = ST.get () in
  assert (qmont_as_nat h4 x153 == // x168
    S.qmul (SI.qsquare_times (qmont_as_nat h3 x153) 5) (qmont_as_nat h0 x_111));

  qsquare_times_in_place x153 9ul;
  qmul x153 x153 x_101111;
  let h5 = ST.get () in
  assert (qmont_as_nat h5 x153 == // x177
    S.qmul (SI.qsquare_times (qmont_as_nat h4 x153) 9) (qmont_as_nat h0 x_101111))


// x153 can be modified
inline_for_extraction noextract
val qinv_x177_x210 (x177 x_111 x_1111 a:felem) : Stack unit
  (requires fun h ->
    live h x177 /\ live h x_111 /\ live h x_1111 /\ live h a /\
    disjoint x177 x_111 /\ disjoint x177 x_1111 /\ disjoint x177 a /\
    as_nat h x177 < S.order /\ as_nat h x_111 < S.order /\
    as_nat h x_1111 < S.order /\ as_nat h a < S.order)
  (ensures fun h0 _ h1 -> modifies (loc x177) h0 h1 /\
    as_nat h1 x177 < S.order /\
    qmont_as_nat h1 x177 = SI.qinv_x177_x210 (qmont_as_nat h0 a)
      (qmont_as_nat h0 x177) (qmont_as_nat h0 x_111) (qmont_as_nat h0 x_1111))

let qinv_x177_x210 x177 x_111 x_1111 a =
  let h0 = ST.get () in
  qsquare_times_in_place x177 6ul;
  qmul x177 x177 x_1111;
  let h1 = ST.get () in
  assert (qmont_as_nat h1 x177 == // x183
    S.qmul (SI.qsquare_times (qmont_as_nat h0 x177) 6) (qmont_as_nat h0 x_1111));

  qsquare_times_in_place x177 2ul;
  qmul x177 x177 a;
  let h2 = ST.get () in
  assert (qmont_as_nat h2 x177 == // x185
    S.qmul (SI.qsquare_times (qmont_as_nat h1 x177) 2) (qmont_as_nat h0 a));

  qsquare_times_in_place x177 5ul;
  qmul x177 x177 a;
  let h3 = ST.get () in
  assert (qmont_as_nat h3 x177 == // x190
    S.qmul (SI.qsquare_times (qmont_as_nat h2 x177) 5) (qmont_as_nat h0 a));

  qsquare_times_in_place x177 6ul;
  qmul x177 x177 x_1111;
  let h4 = ST.get () in
  assert (qmont_as_nat h4 x177 == // x196
    S.qmul (SI.qsquare_times (qmont_as_nat h3 x177) 6) (qmont_as_nat h0 x_1111));

  qsquare_times_in_place x177 5ul;
  qmul x177 x177 x_111;
  let h5 = ST.get () in
  assert (qmont_as_nat h5 x177 == // x201
    S.qmul (SI.qsquare_times (qmont_as_nat h4 x177) 5) (qmont_as_nat h0 x_111));

  qsquare_times_in_place x177 4ul;
  qmul x177 x177 x_111;
  let h6 = ST.get () in
  assert (qmont_as_nat h6 x177 == // x205
    S.qmul (SI.qsquare_times (qmont_as_nat h5 x177) 4) (qmont_as_nat h0 x_111));

  qsquare_times_in_place x177 5ul;
  qmul x177 x177 x_111;
  let h7 = ST.get () in
  assert (qmont_as_nat h7 x177 == // x210
    S.qmul (SI.qsquare_times (qmont_as_nat h6 x177) 5) (qmont_as_nat h0 x_111))


inline_for_extraction noextract
val qinv_x210_x240 (x210 x_11 x_101 x_101111:felem) : Stack unit
  (requires fun h ->
    live h x210 /\ live h x_11 /\ live h x_101 /\ live h x_101111 /\
    disjoint x210 x_11 /\ disjoint x210 x_101 /\ disjoint x210 x_101111 /\
    as_nat h x210 < S.order /\ as_nat h x_11 < S.order /\
    as_nat h x_101 < S.order /\ as_nat h x_101111 < S.order)
  (ensures fun h0 _ h1 -> modifies (loc x210) h0 h1 /\
    as_nat h1 x210 < S.order /\
    qmont_as_nat h1 x210 = SI.qinv_x210_x240 (qmont_as_nat h0 x210)
      (qmont_as_nat h0 x_11) (qmont_as_nat h0 x_101) (qmont_as_nat h0 x_101111))

let qinv_x210_x240 x210 x_11 x_101 x_101111 =
  let h0 = ST.get () in
  qsquare_times_in_place x210 5ul;
  qmul x210 x210 x_101;
  let h1 = ST.get () in
  assert (qmont_as_nat h1 x210 == // x215
    S.qmul (SI.qsquare_times (qmont_as_nat h0 x210) 5) (qmont_as_nat h0 x_101));

  qsquare_times_in_place x210 3ul;
  qmul x210 x210 x_11;
  let h2 = ST.get () in
  assert (qmont_as_nat h2 x210 == // x218
    S.qmul (SI.qsquare_times (qmont_as_nat h1 x210) 3) (qmont_as_nat h0 x_11));

  qsquare_times_in_place x210 10ul;
  qmul x210 x210 x_101111;
  let h3 = ST.get () in
  assert (qmont_as_nat h3 x210 == // x228
    S.qmul (SI.qsquare_times (qmont_as_nat h2 x210) 10) (qmont_as_nat h0 x_101111));

  qsquare_times_in_place x210 2ul;
  qmul x210 x210 x_11;
  let h4 = ST.get () in
  assert (qmont_as_nat h4 x210 == // x230
    S.qmul (SI.qsquare_times (qmont_as_nat h3 x210) 2) (qmont_as_nat h0 x_11));

  qsquare_times_in_place x210 5ul;
  qmul x210 x210 x_11;
  let h5 = ST.get () in
  assert (qmont_as_nat h5 x210 == // x235
    S.qmul (SI.qsquare_times (qmont_as_nat h4 x210) 5) (qmont_as_nat h0 x_11));

  qsquare_times_in_place x210 5ul;
  qmul x210 x210 x_11;
  let h6 = ST.get () in
  assert (qmont_as_nat h6 x210 == // x240
    S.qmul (SI.qsquare_times (qmont_as_nat h5 x210) 5) (qmont_as_nat h0 x_11))


inline_for_extraction noextract
val qinv_x240_x256 (x240 x_1111 x_10101 a:felem) : Stack unit
  (requires fun h ->
    live h x240 /\ live h x_1111 /\ live h x_10101 /\ live h a /\
    disjoint x240 x_1111 /\ disjoint x240 x_10101 /\ disjoint x240 a /\
    as_nat h x240 < S.order /\ as_nat h x_1111 < S.order /\
    as_nat h x_10101 < S.order /\ as_nat h a < S.order)
  (ensures fun h0 _ h1 -> modifies (loc x240) h0 h1 /\
    as_nat h1 x240 < S.order /\
    qmont_as_nat h1 x240 = SI.qinv_x240_x256 (qmont_as_nat h0 a)
      (qmont_as_nat h0 x240) (qmont_as_nat h0 x_1111) (qmont_as_nat h0 x_10101))

let qinv_x240_x256 x240 x_1111 x_10101 a =
  let h0 = ST.get () in
  qsquare_times_in_place x240 3ul;
  qmul x240 x240 a;
  let h1 = ST.get () in
  assert (qmont_as_nat h1 x240 == // x243
    S.qmul (SI.qsquare_times (qmont_as_nat h0 x240) 3) (qmont_as_nat h0 a));

  qsquare_times_in_place x240 7ul;
  qmul x240 x240 x_10101;
  let h2 = ST.get () in
  assert (qmont_as_nat h2 x240 == // x250
    S.qmul (SI.qsquare_times (qmont_as_nat h1 x240) 7) (qmont_as_nat h0 x_10101));

  qsquare_times_in_place x240 6ul;
  qmul x240 x240 x_1111;
  let h3 = ST.get () in
  assert (qmont_as_nat h3 x240 == // x256
    S.qmul (SI.qsquare_times (qmont_as_nat h2 x240) 6) (qmont_as_nat h0 x_1111))


// x128 can be modified
inline_for_extraction noextract
val qinv_x8_x256 (x6 x_11 x_101 x_111 x_1111 x_10101 x_101111 a:felem) : Stack unit
  (requires fun h ->
    live h x6 /\ live h x_11 /\ live h x_101 /\ live h x_111 /\
    live h x_1111 /\ live h x_10101 /\ live h x_101111 /\ live h a /\
    disjoint x6 x_11 /\ disjoint x6 x_101 /\ disjoint x6 x_111 /\ disjoint x6 x_1111 /\
    disjoint x6 x_10101 /\ disjoint x6 x_101111 /\ disjoint x6 a /\
    as_nat h x6 < S.order /\ as_nat h x_11 < S.order /\
    as_nat h x_101 < S.order /\ as_nat h x_111 < S.order /\
    as_nat h x_1111 < S.order /\ as_nat h x_10101 < S.order /\
    as_nat h x_101111 < S.order /\ as_nat h a < S.order)
  (ensures fun h0 _ h1 -> modifies (loc x6) h0 h1 /\
    as_nat h1 x6 < S.order /\
    qmont_as_nat h1 x6 = SI.qinv_x8_x256
      (qmont_as_nat h0 a) (qmont_as_nat h0 x6) (qmont_as_nat h0 x_11)
        (qmont_as_nat h0 x_101) (qmont_as_nat h0 x_111) (qmont_as_nat h0 x_1111)
          (qmont_as_nat h0 x_10101) (qmont_as_nat h0 x_101111))

let qinv_x8_x256 x6 x_11 x_101 x_111 x_1111 x_10101 x_101111 a =
  push_frame ();
  let tmp = create_felem () in
  qinv_x8_x128 tmp x6 x_11;
  qinv_x134_x153 tmp x_11 x_111 x_1111 x_10101 x_101111;
  qinv_x153_x177 tmp x_101 x_111 x_101111;
  qinv_x177_x210 tmp x_111 x_1111 a;
  qinv_x210_x240 tmp x_11 x_101 x_101111;
  qinv_x240_x256 tmp x_1111 x_10101 a;
  copy x6 tmp;
  pop_frame ()


// x128 can be modified
inline_for_extraction noextract
val qinv_make_x (x6 x_11 x_101 x_111 x_1111 x_10101 x_101111 a:felem) : Stack unit
  (requires fun h ->
    live h x6 /\ live h x_11 /\ live h x_101 /\ live h x_111 /\
    live h x_1111 /\ live h x_10101 /\ live h x_101111 /\ live h a /\
    LowStar.Monotonic.Buffer.all_disjoint
      [ loc x6; loc x_11; loc x_101; loc x_111; loc x_1111; loc x_10101; loc x_101111; loc a ] /\
    as_nat h a < S.order)
  (ensures fun h0 _ h1 ->
    modifies (loc x6 |+| loc x_11 |+| loc x_101 |+| loc x_111 |+|
              loc x_1111 |+| loc x_10101 |+| loc x_101111) h0 h1 /\
    as_nat h1 x6 < S.order /\ as_nat h1 x_11 < S.order /\
    as_nat h1 x_101 < S.order /\ as_nat h1 x_111 < S.order /\
    as_nat h1 x_1111 < S.order /\ as_nat h1 x_10101 < S.order /\
    as_nat h1 x_101111 < S.order /\
    (let f = qmont_as_nat h0 a in
    let x_10_s = SI.qsquare_times f 1 in // x_10 is used 3x
    let x_11_s = S.qmul x_10_s f in
    let x_101_s = S.qmul x_10_s x_11_s in
    let x_111_s = S.qmul x_10_s x_101_s in

    let x_1010_s = SI.qsquare_times x_101_s 1 in // x_1010 is used 2x
    let x_1111_s = S.qmul x_101_s x_1010_s in
    let x_10101_s = S.qmul (SI.qsquare_times x_1010_s 1) f in

    let x_101010_s = SI.qsquare_times x_10101_s 1 in // x_101010 is used 2x
    let x_101111_s = S.qmul x_101_s x_101010_s in
    let x6_s = S.qmul x_10101_s x_101010_s in
    qmont_as_nat h1 x6 = x6_s /\ qmont_as_nat h1 x_11 = x_11_s /\
    qmont_as_nat h1 x_101 = x_101_s /\ qmont_as_nat h1 x_111 = x_111_s /\
    qmont_as_nat h1 x_1111 = x_1111_s /\ qmont_as_nat h1 x_10101 = x_10101_s /\
    qmont_as_nat h1 x_101111 = x_101111_s))

let qinv_make_x x6 x_11 x_101 x_111 x_1111 x_10101 x_101111 a =
  qsquare_times x6 a 1ul; // x_10
  qmul x_11 x6 a;
  qmul x_101 x6 x_11;
  qmul x_111 x6 x_101;

  qsquare_times x6 x_101 1ul; // x_1010
  qmul x_1111 x_101 x6;
  qsquare_times_in_place x6 1ul;
  qmul x_10101 x6 a;

  qsquare_times x6 x_10101 1ul; // x_101010
  qmul x_101111 x_101 x6;
  qmul x6 x_10101 x6


[@CInline]
let qinv res r =
  let h0 = ST.get () in
  push_frame ();
  let tmp = create 28ul (u64 0) in
  let x6       = sub tmp 0ul 4ul in
  let x_11     = sub tmp 4ul 4ul in
  let x_101    = sub tmp 8ul 4ul in
  let x_111    = sub tmp 12ul 4ul in
  let x_1111   = sub tmp 16ul 4ul in
  let x_10101  = sub tmp 20ul 4ul in
  let x_101111 = sub tmp 24ul 4ul in
  qinv_make_x x6 x_11 x_101 x_111 x_1111 x_10101 x_101111 r;
  qinv_x8_x256 x6 x_11 x_101 x_111 x_1111 x_10101 x_101111 r;
  copy res x6;
  let h1 = ST.get () in
  assert (qmont_as_nat h1 res == SI.qinv (qmont_as_nat h0 r));
  SI.qinv_is_qinv_lemma (qmont_as_nat h0 r);
  pop_frame ()
