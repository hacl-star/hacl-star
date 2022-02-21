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
module BN = Hacl.Bignum
module BM = Hacl.Bignum.Montgomery

module SD = Hacl.Spec.Bignum.Definitions
module SM = Hacl.Spec.Bignum.Montgomery
module M = Hacl.Spec.Montgomery.Lemmas

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

(** Montgomery arithmetic for modular exponentiation and field inversion *)

inline_for_extraction noextract
let km = BM.mk_runtime_mont #U64 qnlimb

inline_for_extraction noextract
let linv_ctx (a:LSeq.lseq uint64 4) : Type0 =
  SD.bn_v #U64 #4 a == S.q

inline_for_extraction noextract
let linv (a:LSeq.lseq uint64 4) : Type0 =
  SD.bn_v #U64 #4 a < S.q

inline_for_extraction noextract
let refl (aM:LSeq.lseq uint64 4{linv aM}) : GTot S.qelem =
  let mu = make_mu0 () in
  M.from_mont_lemma 64 4 S.q (v mu) (SD.bn_v aM);
  M.from_mont 64 4 S.q (v mu) (SD.bn_v aM)


inline_for_extraction noextract
let linv_ctxs (h:mem) (n:qelem) = linv_ctx (as_seq h n)
inline_for_extraction noextract
let linvs (h:mem) (aM:qelem) = linv (as_seq h aM)
inline_for_extraction noextract
let refls (h:mem) (aM:qelem{linvs h aM}) = refl (as_seq h aM)

inline_for_extraction noextract
let mk_to_k256_scalar_concrete_ops : BE.to_concrete_ops U64 4ul 4ul = {
  BE.t_spec = S.qelem;
  BE.concr_ops = SI.mk_nat_mod_concrete_ops;
  BE.linv_ctx = linv_ctx;
  BE.linv = linv;
  BE.refl = refl;
}


val qmul_mont : BE.lmul_st U64 4ul 4ul mk_to_k256_scalar_concrete_ops
[@CInline]
let qmul_mont n aM bM resM =
  let h0 = ST.get () in
  [@inline_let]
  let mu = make_mu0 () in
  SM.bn_mont_mul_lemma (as_seq h0 n) mu (as_seq h0 aM) (as_seq h0 bM);
  M.from_mont_mul_lemma 64 4 (qas_nat h0 n) (v mu) (qas_nat h0 aM) (qas_nat h0 bM);
  km.BM.mul n mu aM bM resM


val qsqr_mont : BE.lsqr_st U64 4ul 4ul mk_to_k256_scalar_concrete_ops
[@CInline]
let qsqr_mont n aM resM =
  let h0 = ST.get () in
  [@inline_let]
  let mu = make_mu0 () in
  SM.bn_mont_sqr_lemma (as_seq h0 n) mu (as_seq h0 aM);
  M.from_mont_mul_lemma 64 4 (qas_nat h0 n) (v mu) (qas_nat h0 aM) (qas_nat h0 aM);
  km.BM.sqr n mu aM resM


inline_for_extraction noextract
let mk_k256_scalar_concrete_ops : BE.concrete_ops U64 4ul 4ul = {
  BE.to = mk_to_k256_scalar_concrete_ops;
  BE.lmul = qmul_mont;
  BE.lsqr = qsqr_mont;
}


val to_mont (n a aM:qelem) : Stack unit
  (requires fun h ->
    live h n /\ live h a /\ live h aM /\
    disjoint n a /\ disjoint n aM /\ disjoint a aM /\
    linvs h a /\ linv_ctxs h n)
  (ensures  fun h0 _ h1 -> modifies (loc aM) h0 h1 /\
    linvs h1 aM /\ refls h1 aM == qas_nat h0 a)
[@CInline]
let to_mont n a aM =
  push_frame ();
  let r2 = create qnlimb (u64 0) in
  make_u64_4 r2 (make_r2_modq ());
  let h0 = ST.get () in
  [@inline_let]
  let mu = make_mu0 () in
  km.BM.to n mu r2 a aM;
  SM.bn_to_mont_lemma (as_seq h0 n) mu (as_seq h0 r2) (as_seq h0 a);
  M.from_to_mont_lemma 64 4 (qas_nat h0 n) (v mu) (qas_nat h0 a);
  pop_frame ()


val from_mont (n aM a:qelem) : Stack unit
  (requires fun h ->
    live h n /\ live h a /\ live h aM /\
    disjoint n a /\ disjoint n aM /\ disjoint a aM /\
    linvs h aM /\ linv_ctxs h n)
  (ensures  fun h0 _ h1 -> modifies (loc a) h0 h1 /\
    linvs h1 a /\ qas_nat h1 a == refls h0 aM)
[@CInline]
let from_mont n aM a =
  let h0 = ST.get () in
  [@inline_let]
  let mu = make_mu0 () in
  km.BM.from n mu aM a;
  SM.bn_from_mont_lemma (as_seq h0 n) mu (as_seq h0 aM)


val qsquare_times_in_place (n out:qelem) (b:size_t) : Stack unit
  (requires fun h ->
    live h n /\ live h out /\ disjoint n out /\
    linvs h out /\ linv_ctxs h n)
  (ensures  fun h0 _ h1 -> modifies (loc out) h0 h1 /\ linvs h1 out /\
    refls h1 out == SI.qsquare_times (refls h0 out) (v b))

[@CInline]
let qsquare_times_in_place n out b =
  BE.lexp_pow_in_place 4ul 4ul mk_k256_scalar_concrete_ops n out b


val qsquare_times (n out a:qelem) (b:size_t) : Stack unit
  (requires fun h ->
    live h out /\ live h a /\ live h n /\
    disjoint out a /\ disjoint out n /\ disjoint a n /\
    linvs h a /\ linv_ctxs h n)
  (ensures  fun h0 _ h1 -> modifies (loc out) h0 h1 /\ linvs h1 out /\
    refls h1 out == SI.qsquare_times (refls h0 a) (v b))

[@CInline]
let qsquare_times n out a b =
  BE.lexp_pow2 4ul 4ul mk_k256_scalar_concrete_ops n a b out


inline_for_extraction noextract
val qinv1 (n f x_10 x_11 x_101 x_111 x_1001 x_1011 x_1101:qelem) : Stack unit
  (requires fun h ->
    live h n /\ live h f /\ live h x_10 /\ live h x_11 /\ live h x_101 /\
    live h x_111 /\ live h x_1001 /\ live h x_1011 /\ live h x_1101 /\
    disjoint n f /\ disjoint n x_10 /\ disjoint n x_11 /\ disjoint n x_101 /\
    disjoint n x_111 /\ disjoint n x_1001 /\ disjoint n x_1011 /\ disjoint n x_1101 /\
    disjoint f x_10 /\ disjoint f x_11 /\ disjoint f x_101 /\
    disjoint f x_111 /\ disjoint f x_1001 /\ disjoint f x_1011 /\
    disjoint f x_1101 /\ disjoint x_10 x_11 /\ disjoint x_10 x_101 /\
    disjoint x_10 x_111 /\ disjoint x_10 x_1001 /\ disjoint x_10 x_1011 /\
    disjoint x_10 x_1101 /\ disjoint x_11 x_101 /\ disjoint x_11 x_111 /\
    disjoint x_11 x_1001 /\ disjoint x_11 x_1011 /\ disjoint x_11 x_1101 /\
    disjoint x_101 x_111 /\ disjoint x_101 x_1001 /\ disjoint x_101 x_1011 /\
    disjoint x_101 x_1101 /\ disjoint x_111 x_1001 /\ disjoint x_111 x_1011 /\
    disjoint x_111 x_1101 /\ disjoint x_1001 x_1011 /\ disjoint x_1001 x_1101 /\
    disjoint x_1011 x_1101 /\ linvs h f /\ linv_ctxs h n)
  (ensures  fun h0 _ h1 ->
    modifies (loc x_10 |+| loc x_11 |+| loc x_101 |+|
      loc x_111 |+| loc x_1001 |+| loc x_1011 |+| loc x_1101) h0 h1 /\
   (let _x_10 = SI.qsquare_times (refls h0 f) 1 in
    let _x_11 = S.qmul _x_10 (refls h0 f) in
    let _x_101 = S.qmul _x_10 _x_11 in
    let _x_111 = S.qmul _x_10 _x_101 in
    let _x_1001 = S.qmul _x_10 _x_111 in
    let _x_1011 = S.qmul _x_10 _x_1001 in
    let _x_1101 = S.qmul _x_10 _x_1011 in
    linvs h1 x_10 /\ refls h1 x_10 == _x_10 /\
    linvs h1 x_11 /\ refls h1 x_11 == _x_11 /\
    linvs h1 x_101 /\ refls h1 x_101 == _x_101 /\
    linvs h1 x_111 /\ refls h1 x_111 == _x_111 /\
    linvs h1 x_1001 /\ refls h1 x_1001 == _x_1001 /\
    linvs h1 x_1011 /\ refls h1 x_1011 == _x_1011 /\
    linvs h1 x_1101 /\ refls h1 x_1101 == _x_1101))

let qinv1 n f x_10 x_11 x_101 x_111 x_1001 x_1011 x_1101 =
  let h0 = ST.get () in
  qsquare_times n x_10 f 1ul;
  let h1 = ST.get () in
  assert (refls h1 x_10 == SI.qsquare_times (refls h0 f) 1);

  qmul_mont n x_10 f x_11;
  let h2 = ST.get () in
  assert (refls h2 x_11 == S.qmul (refls h1 x_10) (refls h0 f));

  qmul_mont n x_10 x_11 x_101;
  let h3 = ST.get () in
  assert (refls h3 x_101 == S.qmul (refls h1 x_10) (refls h2 x_11));

  qmul_mont n x_10 x_101 x_111;
  let h4 = ST.get () in
  assert (refls h4 x_111 == S.qmul (refls h1 x_10) (refls h3 x_101));

  qmul_mont n x_10 x_111 x_1001;
  let h5 = ST.get () in
  assert (refls h5 x_1001 == S.qmul (refls h1 x_10) (refls h4 x_111));

  qmul_mont n x_10 x_1001 x_1011;
  let h6 = ST.get () in
  assert (refls h6 x_1011 == S.qmul (refls h1 x_10) (refls h5 x_1001));

  qmul_mont n x_10 x_1011 x_1101;
  let h7 = ST.get () in
  assert (refls h7 x_1101 == S.qmul (refls h1 x_10) (refls h6 x_1011))


inline_for_extraction noextract
val qinv2 (n x_11 x_1011 x_1101 x6 x8 x14: qelem) : Stack unit
  (requires fun h ->
    live h n /\ live h x_11 /\ live h x_1011 /\
    live h x_1101 /\ live h x6 /\ live h x8 /\ live h x14 /\
    disjoint n x_11 /\ disjoint n x_1011 /\ disjoint n x_1101 /\
    disjoint n x6 /\ disjoint n x8 /\ disjoint n x14 /\
    disjoint x_11 x6 /\ disjoint x_11 x8 /\ disjoint x_11 x14 /\
    disjoint x_1011 x6 /\ disjoint x_1011 x8 /\ disjoint x_1011 x14 /\
    disjoint x_1101 x6 /\ disjoint x_1101 x8 /\ disjoint x_1101 x14 /\
    disjoint x6 x8 /\ disjoint x6 x14 /\ disjoint x8 x14 /\
    linvs h x_11 /\ linvs h x_1011 /\ linvs h x_1101 /\ linv_ctxs h n)
  (ensures fun h0 _ h1 -> modifies (loc x6 |+| loc x8 |+| loc x14) h0 h1 /\
   (let _x6 = S.qmul (SI.qsquare_times (refls h0 x_1101) 2) (refls h0 x_1011) in
    let _x8 = S.qmul (SI.qsquare_times _x6 2) (refls h0 x_11) in
    let _x14 = S.qmul (SI.qsquare_times _x8 6) _x6 in
    linvs h1 x6 /\ refls h1 x6 == _x6 /\
    linvs h1 x8 /\ refls h1 x8 == _x8 /\
    linvs h1 x14 /\ refls h1 x14 == _x14))

let qinv2 n x_11 x_1011 x_1101 x6 x8 x14 =
  let h0 = ST.get () in
  qsquare_times n x6 x_1101 2ul;
  qmul_mont n x6 x_1011 x6;
  let h1 = ST.get () in
  assert (refls h1 x6 == S.qmul (SI.qsquare_times (refls h0 x_1101) 2) (refls h0 x_1011));

  qsquare_times n x8 x6 2ul;
  qmul_mont n x8 x_11 x8;
  let h2 = ST.get () in
  assert (refls h2 x8 == S.qmul (SI.qsquare_times (refls h1 x6) 2) (refls h0 x_11));

  qsquare_times n x14 x8 6ul;
  qmul_mont n x14 x6 x14;
  let h3 = ST.get () in
  assert (refls h3 x14 == S.qmul (SI.qsquare_times (refls h2 x8) 6) (refls h1 x6))


inline_for_extraction noextract
val qinv3 (n tmp x14: qelem) : Stack unit
  (requires fun h ->
    live h n /\ live h tmp /\ live h x14 /\
    disjoint n tmp /\ disjoint n x14 /\ disjoint tmp x14 /\
    linvs h x14 /\ linv_ctxs h n)
  (ensures  fun h0 _ h1 -> modifies (loc tmp) h0 h1 /\
    linvs h1 tmp /\ refls h1 tmp == SI.qinv_r0_r1 (refls h0 x14))

let qinv3 n tmp x14 =
  push_frame ();
  let x56 = create_qelem () in

  let h0 = ST.get () in
  qsquare_times n tmp x14 14ul;
  qmul_mont n tmp x14 tmp; //tmp = x28
  let h1 = ST.get () in
  assert (refls h1 tmp == S.qmul (SI.qsquare_times (refls h0 x14) 14) (refls h0 x14));

  qsquare_times n x56 tmp 28ul;
  qmul_mont n x56 tmp x56;
  let h2 = ST.get () in
  assert (refls h2 x56 == S.qmul (SI.qsquare_times (refls h1 tmp) 28) (refls h1 tmp));

  qsquare_times n tmp x56 56ul; //tmp = r0
  qmul_mont n tmp x56 tmp;
  let h3 = ST.get () in
  assert (refls h3 tmp == S.qmul (SI.qsquare_times (refls h2 x56) 56) (refls h2 x56));

  qsquare_times_in_place n tmp 14ul; //tmp = r1
  qmul_mont n tmp x14 tmp;
  let h4 = ST.get () in
  assert (refls h4 tmp == S.qmul (SI.qsquare_times (refls h3 tmp) 14) (refls h0 x14));
  pop_frame ()


//r2; .. ;r8
inline_for_extraction noextract
val qinv4 (n tmp x_101 x_111 x_1011: qelem) : Stack unit
  (requires fun h ->
    live h n /\ live h tmp /\ live h x_101 /\ live h x_111 /\ live h x_1011 /\
    disjoint n tmp /\ disjoint n x_101 /\ disjoint n x_111 /\ disjoint n x_1011 /\
    disjoint tmp x_101 /\ disjoint tmp x_111 /\ disjoint tmp x_1011 /\
    linvs h tmp /\ linvs h x_101 /\ linvs h x_111 /\
    linvs h x_1011 /\ linv_ctxs h n)
  (ensures  fun h0 _ h1 -> modifies (loc tmp) h0 h1 /\
    linvs h1 tmp /\ refls h1 tmp == SI.qinv_r2_r8 (refls h0 tmp)
      (refls h0 x_101) (refls h0 x_111) (refls h0 x_1011))

let qinv4 n tmp x_101 x_111 x_1011 =
  let h0 = ST.get () in
  qsquare_times_in_place n tmp 3ul;
  qmul_mont n tmp x_101 tmp; //tmp = r2
  let h1 = ST.get () in
  assert (refls h1 tmp == S.qmul (SI.qsquare_times (refls h0 tmp) 3) (refls h0 x_101));

  qsquare_times_in_place n tmp 4ul;
  qmul_mont n tmp x_111 tmp; //tmp = r3
  let h2 = ST.get () in
  assert (refls h2 tmp == S.qmul (SI.qsquare_times (refls h1 tmp) 4) (refls h0 x_111));

  qsquare_times_in_place n tmp 4ul;
  qmul_mont n tmp x_101 tmp; //tmp = r4
  let h3 = ST.get () in
  assert (refls h3 tmp == S.qmul (SI.qsquare_times (refls h2 tmp) 4) (refls h0 x_101));

  qsquare_times_in_place n tmp 5ul;
  qmul_mont n tmp x_1011 tmp; //tmp = r5
  let h4 = ST.get () in
  assert (refls h4 tmp == S.qmul (SI.qsquare_times (refls h3 tmp) 5) (refls h0 x_1011));

  qsquare_times_in_place n tmp 4ul;
  qmul_mont n tmp x_1011 tmp; //tmp = r6
  let h5 = ST.get () in
  assert (refls h5 tmp == S.qmul (SI.qsquare_times (refls h4 tmp) 4) (refls h0 x_1011));

  qsquare_times_in_place n tmp 4ul;
  qmul_mont n tmp x_111 tmp; //tmp = r7
  let h6 = ST.get () in
  assert (refls h6 tmp == S.qmul (SI.qsquare_times (refls h5 tmp) 4) (refls h0 x_111));

  qsquare_times_in_place n tmp 5ul;
  qmul_mont n tmp x_111 tmp; //tmp = r8
  let h7 = ST.get () in
  assert (refls h7 tmp == S.qmul (SI.qsquare_times (refls h6 tmp) 5) (refls h0 x_111))


// r9; ..; r15
inline_for_extraction noextract
val qinv5 (n tmp x_101 x_111 x_1001 x_1101: qelem) : Stack unit
  (requires fun h ->
    live h n /\ live h tmp /\ live h x_101 /\ live h x_111 /\
    live h x_1001 /\ live h x_1101 /\ disjoint n tmp /\
    disjoint n x_101 /\ disjoint n x_111 /\ disjoint n x_1001 /\
    disjoint n x_1101 /\ disjoint tmp x_101 /\ disjoint tmp x_111 /\
    disjoint tmp x_1001 /\ disjoint tmp x_1101 /\
    linvs h tmp /\ linvs h x_101 /\ linvs h x_111 /\
    linvs h x_1001 /\ linvs h x_1101 /\ linv_ctxs h n)
  (ensures  fun h0 _ h1 -> modifies (loc tmp) h0 h1 /\
    linvs h1 tmp /\ refls h1 tmp == SI.qinv_r9_r15 (refls h0 tmp)
      (refls h0 x_101) (refls h0 x_111) (refls h0 x_1001) (refls h0 x_1101))

let qinv5 n tmp x_101 x_111 x_1001 x_1101 =
  let h0 = ST.get () in
  qsquare_times_in_place n tmp 6ul;
  qmul_mont n tmp x_1101 tmp; //tmp = r9
  let h1 = ST.get () in
  assert (refls h1 tmp == S.qmul (SI.qsquare_times (refls h0 tmp) 6) (refls h0 x_1101));

  qsquare_times_in_place n tmp 4ul;
  qmul_mont n tmp x_101 tmp; //tmp = r10
  let h2 = ST.get () in
  assert (refls h2 tmp == S.qmul (SI.qsquare_times (refls h1 tmp) 4) (refls h0 x_101));

  qsquare_times_in_place n tmp 3ul;
  qmul_mont n tmp x_111 tmp; //tmp = r11
  let h3 = ST.get () in
  assert (refls h3 tmp == S.qmul (SI.qsquare_times (refls h2 tmp) 3) (refls h0 x_111));

  qsquare_times_in_place n tmp 5ul;
  qmul_mont n tmp x_1001 tmp; //tmp = r12
  let h4 = ST.get () in
  assert (refls h4 tmp == S.qmul (SI.qsquare_times (refls h3 tmp) 5) (refls h0 x_1001));

  qsquare_times_in_place n tmp 6ul;
  qmul_mont n tmp x_101 tmp; //tmp = r13
  let h5 = ST.get () in
  assert (refls h5 tmp == S.qmul (SI.qsquare_times (refls h4 tmp) 6) (refls h0 x_101));

  qsquare_times_in_place n tmp 10ul;
  qmul_mont n tmp x_111 tmp; //tmp = r14
  let h6 = ST.get () in
  assert (refls h6 tmp == S.qmul (SI.qsquare_times (refls h5 tmp) 10) (refls h0 x_111));

  qsquare_times_in_place n tmp 4ul;
  qmul_mont n tmp x_111 tmp; //tmp = r15
  let h7 = ST.get () in
  assert (refls h7 tmp == S.qmul (SI.qsquare_times (refls h6 tmp) 4) (refls h0 x_111))


// r16; ..;r23
inline_for_extraction noextract
val qinv6 (n tmp x8 x_11 x_1001 x_1011 x_1101: qelem) : Stack unit
  (requires fun h ->
    live h n /\ live h tmp /\ live h x8 /\ live h x_11 /\
    live h x_1001 /\ live h x_1011 /\ live h x_1101 /\
    disjoint n tmp /\ disjoint n x8 /\ disjoint n x_11 /\
    disjoint n x_1001 /\ disjoint n x_1011 /\ disjoint n x_1101 /\
    disjoint tmp x8 /\ disjoint tmp x_11 /\ disjoint tmp x_1001 /\
    disjoint tmp x_1011 /\ disjoint tmp x_1101 /\
    linvs h tmp /\ linvs h x8 /\ linvs h x_11 /\ linvs h x_1001 /\
    linvs h x_1011 /\ linvs h x_1101 /\ linv_ctxs h n)
  (ensures  fun h0 _ h1 -> modifies (loc tmp) h0 h1 /\
    linvs h1 tmp /\ refls h1 tmp == SI.qinv_r16_r23 (refls h0 tmp)
      (refls h0 x8) (refls h0 x_11) (refls h0 x_1001) (refls h0 x_1011) (refls h0 x_1101))

let qinv6 n tmp x8 x_11 x_1001 x_1011 x_1101 =
  let h0 = ST.get () in
  qsquare_times_in_place n tmp 9ul;
  qmul_mont n tmp x8 tmp; //tmp = r16
  let h1 = ST.get () in
  assert (refls h1 tmp == S.qmul (SI.qsquare_times (refls h0 tmp) 9) (refls h0 x8));

  qsquare_times_in_place n tmp 5ul;
  qmul_mont n tmp x_1001 tmp; //tmp = r17
  let h2 = ST.get () in
  assert (refls h2 tmp == S.qmul (SI.qsquare_times (refls h1 tmp) 5) (refls h0 x_1001));

  qsquare_times_in_place n tmp 6ul;
  qmul_mont n tmp x_1011 tmp; //tmp = r18
  let h3 = ST.get () in
  assert (refls h3 tmp == S.qmul (SI.qsquare_times (refls h2 tmp) 6) (refls h0 x_1011));

  qsquare_times_in_place n tmp 4ul;
  qmul_mont n tmp x_1101 tmp; //tmp = r19
  let h4 = ST.get () in
  assert (refls h4 tmp == S.qmul (SI.qsquare_times (refls h3 tmp) 4) (refls h0 x_1101));

  qsquare_times_in_place n tmp 5ul;
  qmul_mont n tmp x_11 tmp; //tmp = r20
  let h5 = ST.get () in
  assert (refls h5 tmp == S.qmul (SI.qsquare_times (refls h4 tmp) 5) (refls h0 x_11));

  qsquare_times_in_place n tmp 6ul;
  qmul_mont n tmp x_1101 tmp; //tmp = r21
  let h6 = ST.get () in
  assert (refls h6 tmp == S.qmul (SI.qsquare_times (refls h5 tmp) 6) (refls h0 x_1101));

  qsquare_times_in_place n tmp 10ul;
  qmul_mont n tmp x_1101 tmp; //tmp = r22
  let h7 = ST.get () in
  assert (refls h7 tmp == S.qmul (SI.qsquare_times (refls h6 tmp) 10) (refls h0 x_1101));

  qsquare_times_in_place n tmp 4ul;
  qmul_mont n tmp x_1001 tmp; //tmp = r23
  let h8 = ST.get () in
  assert (refls h8 tmp == S.qmul (SI.qsquare_times (refls h7 tmp) 4) (refls h0 x_1001))


//r24; r25
inline_for_extraction noextract
val qinv7 (n tmp f x6: qelem) : Stack unit
  (requires fun h ->
    live h n /\ live h tmp /\ live h f /\ live h x6 /\
    disjoint n tmp /\ disjoint n f /\ disjoint n x6 /\
    disjoint tmp f /\ disjoint tmp x6 /\
    linvs h tmp /\ linvs h f /\ linvs h x6 /\ linv_ctxs h n)
  (ensures  fun h0 _ h1 -> modifies (loc tmp) h0 h1 /\
    linvs h1 tmp /\ refls h1 tmp == SI.qinv_r24_r25 (refls h0 tmp) (refls h0 f) (refls h0 x6))

let qinv7 n tmp f x6 =
  let h0 = ST.get () in
  qsquare_times_in_place n tmp 6ul;
  qmul_mont n tmp f tmp; //tmp = r23
  let h1 = ST.get () in
  assert (refls h1 tmp == S.qmul (SI.qsquare_times (refls h0 tmp) 6) (refls h0 f));

  qsquare_times_in_place n tmp 8ul;
  qmul_mont n tmp x6 tmp; //tmp = r24
  let h2 = ST.get () in
  assert (refls h2 tmp == S.qmul (SI.qsquare_times (refls h1 tmp) 8) (refls h0 x6))


inline_for_extraction noextract
val qinv8 (n tmp f x_11 x_101 x_111 x_1001 x_1011 x_1101: qelem) : Stack unit
  (requires fun h ->
    live h n /\ live h tmp /\ live h f /\ live h x_11 /\
    live h x_101 /\ live h x_111 /\ live h x_1001 /\
    live h x_1011 /\ live h x_1101 /\
    disjoint n tmp /\ disjoint n f /\ disjoint n x_11 /\
    disjoint n x_101 /\ disjoint n x_111 /\ disjoint n x_1001 /\
    disjoint n x_1011 /\ disjoint n x_1101 /\ disjoint tmp f /\
    disjoint tmp x_11 /\ disjoint tmp x_101 /\ disjoint tmp x_111 /\
    disjoint tmp x_1001 /\ disjoint tmp x_1011 /\ disjoint tmp x_1101 /\
    linvs h f /\ linvs h x_11 /\ linvs h x_101 /\ linvs h x_111 /\
    linvs h x_1001 /\ linvs h x_1011 /\ linvs h x_1101 /\ linv_ctxs h n)
  (ensures  fun h0 _ h1 -> modifies (loc tmp) h0 h1 /\
    linvs h1 tmp /\ refls h1 tmp == SI.qinv_r0_r25 (refls h0 f)
      (refls h0 x_11) (refls h0 x_101) (refls h0 x_111)
      (refls h0 x_1001) (refls h0 x_1011) (refls h0 x_1101))

let qinv8 n tmp f x_11 x_101 x_111 x_1001 x_1011 x_1101 =
  push_frame ();
  let x6 = create_qelem () in
  let x8 = create_qelem () in
  let x14 = create_qelem () in

  let h1 = ST.get () in
  qinv2 n x_11 x_1011 x_1101 x6 x8 x14; //x6; x8; x14
  let h2 = ST.get () in
  assert (modifies (loc x6 |+| loc x8 |+| loc x14) h1 h2);

  qinv3 n tmp x14; //x28; x56; r0; r1
  let h3 = ST.get () in
  assert (modifies (loc tmp) h2 h3);

  qinv4 n tmp x_101 x_111 x_1011; //r2; ..; r8
  let h4 = ST.get () in
  assert (modifies (loc tmp) h3 h4);

  qinv5 n tmp x_101 x_111 x_1001 x_1101; //r9; ..; r15
  let h5 = ST.get () in
  assert (modifies (loc tmp) h4 h5);

  qinv6 n tmp x8 x_11 x_1001 x_1011 x_1101; //r16; ..; r23
  let h6 = ST.get () in
  assert (modifies (loc tmp) h5 h6);

  qinv7 n tmp f x6; //r24; r25
  let h7 = ST.get () in
  assert (modifies (loc tmp) h6 h7);
  pop_frame ()


inline_for_extraction noextract
val qinv_ (n out f: qelem) : Stack unit
  (requires fun h ->
    live h n /\ live h out /\ live h f /\
    disjoint n out /\ disjoint n f /\ disjoint out f /\
    linvs h f /\ linv_ctxs h n)
  (ensures  fun h0 _ h1 -> modifies (loc out) h0 h1 /\
    linvs h1 out /\ refls h1 out == SI.qinv (refls h0 f))

#set-options "--z3rlimit 150"

let qinv_ n out f =
  push_frame ();
  let x_10 = create_qelem () in
  let x_11 = create_qelem () in
  let x_101 = create_qelem () in
  let x_111 = create_qelem () in
  let x_1001 = create_qelem () in
  let x_1011 = create_qelem () in
  let x_1101 = create_qelem () in

  qinv1 n f x_10 x_11 x_101 x_111 x_1001 x_1011 x_1101;
  qinv8 n out f x_11 x_101 x_111 x_1001 x_1011 x_1101;
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
  push_frame ();
  let fM = create_qelem () in
  let outM = create_qelem () in
  let n = create_qelem () in
  make_u64_4 n (make_order_k256 ());
  to_mont n f fM;
  let h0 = ST.get () in
  SI.qinv_is_qinv_lemma (refls h0 fM);
  qinv_ n outM fM;
  from_mont n outM out;
  pop_frame ()
