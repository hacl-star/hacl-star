module Hacl.Impl.K256.Finv

open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Mul

open Lib.IntTypes
open Lib.Buffer

open Hacl.K256.Field

module ST = FStar.HyperStack.ST
module LSeq = Lib.Sequence

module S = Spec.K256
module SI = Hacl.Spec.K256.Finv

module BE = Hacl.Impl.Exponentiation
module SD = Hacl.Spec.Bignum.Definitions

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

unfold
let linv_ctx (a:LSeq.lseq uint64 0) : Type0 = True

unfold
let linv (a:LSeq.lseq uint64 4) : Type0 =
  SD.bn_v #U64 #4 a < S.prime

unfold
let refl (a:LSeq.lseq uint64 4{linv a}) : GTot S.felem =
  SD.bn_v #U64 #4 a

inline_for_extraction noextract
let mk_to_k256_prime_concrete_ops : BE.to_concrete_ops U64 4ul 0ul = {
  BE.t_spec = S.felem;
  BE.concr_ops = SI.mk_nat_mod_concrete_ops;
  BE.linv_ctx = linv_ctx;
  BE.linv = linv;
  BE.refl = refl;
}


inline_for_extraction noextract
val mul_mod : BE.lmul_st U64 4ul 0ul mk_to_k256_prime_concrete_ops
let mul_mod ctx x y xy = fmul xy x y


inline_for_extraction noextract
val sqr_mod : BE.lsqr_st U64 4ul 0ul mk_to_k256_prime_concrete_ops
let sqr_mod ctx x xx = fsqr xx x


inline_for_extraction noextract
let mk_k256_prime_concrete_ops : BE.concrete_ops U64 4ul 0ul = {
  BE.to = mk_to_k256_prime_concrete_ops;
  BE.lmul = mul_mod;
  BE.lsqr = sqr_mod;
}


val fsquare_times_in_place (out:felem) (b:size_t) : Stack unit
  (requires fun h ->
    live h out /\ fe_lt_prime h out)
  (ensures  fun h0 _ h1 -> modifies (loc out) h0 h1 /\ fe_lt_prime h1 out /\
    as_nat h1 out == SI.fsquare_times (as_nat h0 out) (v b))

[@CInline]
let fsquare_times_in_place out b =
  BE.lexp_pow_in_place 4ul 0ul mk_k256_prime_concrete_ops (null uint64) out b


val fsquare_times (out a:felem) (b:size_t) : Stack unit
  (requires fun h ->
    live h out /\ live h a /\ disjoint out a /\
    fe_lt_prime h a)
  (ensures  fun h0 _ h1 -> modifies (loc out) h0 h1 /\ fe_lt_prime h1 a /\
    as_nat h1 out == SI.fsquare_times (as_nat h0 a) (v b))

[@CInline]
let fsquare_times out a b =
  BE.lexp_pow2 4ul 0ul mk_k256_prime_concrete_ops (null uint64) a b out


inline_for_extraction noextract
val finv1 (x2 x3 x22 x44 tmp:felem) : Stack unit
  (requires fun h ->
    live h x2 /\ live h x3 /\ live h x22 /\
    live h x44 /\ live h tmp /\
    disjoint x2 x3 /\ disjoint x2 x22 /\ disjoint x2 x44 /\
    disjoint x2 tmp /\ disjoint x3 x22 /\ disjoint x3 x44 /\
    disjoint x3 tmp /\ disjoint x22 x44 /\ disjoint x22 tmp /\
    disjoint x44 tmp /\ fe_lt_prime h x2 /\ fe_lt_prime h x3)
  (ensures fun h0 _ h1 -> modifies (loc x22 |+| loc x44 |+| loc tmp) h0 h1 /\
   (let _x2 = as_nat h0 x2 in
    let _x3 = as_nat h0 x3 in
    let _x6 = S.fmul (SI.fsquare_times _x3 3) _x3 in
    let _x9 = S.fmul (SI.fsquare_times _x6 3) _x3 in
    let _x11 = S.fmul (SI.fsquare_times _x9 2) _x2 in
    let _x22 = S.fmul (SI.fsquare_times _x11 11) _x11 in
    let _x44 = S.fmul (SI.fsquare_times _x22 22) _x22 in
    as_nat h1 tmp == _x11 /\ as_nat h1 x22 == _x22 /\ as_nat h1 x44 == _x44 /\
    fe_lt_prime h1 tmp /\ fe_lt_prime h1 x22 /\ fe_lt_prime h1 x44))

let finv1 x2 x3 x22 x44 tmp =
  let h2 = ST.get () in
  fsquare_times tmp x3 3ul;
  fmul tmp tmp x3; // tmp = x6 = S.fmul (fsquare_times x3 3) x3
  let h3 = ST.get () in
  assert (as_nat h3 tmp == S.fmul (SI.fsquare_times (as_nat h2 x3) 3) (as_nat h2 x3));

  fsquare_times_in_place tmp 3ul;
  fmul tmp tmp x3; // tmp = x9 = S.fmul (fsquare_times x6 3) x3
  let h4 = ST.get () in
  assert (as_nat h4 tmp == S.fmul (SI.fsquare_times (as_nat h3 tmp) 3) (as_nat h2 x3));

  fsquare_times_in_place tmp 2ul;
  fmul tmp tmp x2; // tmp = x11 = S.fmul (fsquare_times x9 2) x2
  let h5 = ST.get () in
  assert (as_nat h5 tmp == S.fmul (SI.fsquare_times (as_nat h4 tmp) 2) (as_nat h2 x2));

  fsquare_times x22 tmp 11ul;
  fmul x22 x22 tmp; // x22 = S.fmul (fsquare_times x11 11) x11
  let h6 = ST.get () in
  assert (as_nat h6 x22 == S.fmul (SI.fsquare_times (as_nat h5 tmp) 11) (as_nat h5 tmp));

  fsquare_times x44 x22 22ul;
  fmul x44 x44 x22; // x44 = S.fmul (fsquare_times x22 22) x22
  let h7 = ST.get () in
  assert (as_nat h7 x44 == S.fmul (SI.fsquare_times (as_nat h6 x22) 22) (as_nat h6 x22))


inline_for_extraction noextract
val finv2 (x3 x44 x88 tmp:felem) : Stack unit
  (requires fun h ->
    live h x3 /\ live h x44 /\ live h x88 /\ live h tmp /\
    disjoint x3 x44 /\ disjoint x3 x88 /\ disjoint x3 tmp /\
    disjoint x44 x88 /\ disjoint x44 tmp /\ disjoint x88 tmp /\
    fe_lt_prime h x3 /\ fe_lt_prime h x44)
  (ensures fun h0 _ h1 -> modifies (loc x88 |+| loc tmp) h0 h1 /\
   (let _x3 = as_nat h0 x3 in
    let _x44 = as_nat h0 x44 in
    let _x88 = S.fmul (SI.fsquare_times _x44 44) _x44 in
    let _x176 = S.fmul (SI.fsquare_times _x88 88) _x88 in
    let _x220 = S.fmul (SI.fsquare_times _x176 44) _x44 in
    let _x223 = S.fmul (SI.fsquare_times _x220 3) _x3 in
    as_nat h1 tmp == _x223 /\ as_nat h1 x88 == _x88 /\
    fe_lt_prime h1 tmp /\ fe_lt_prime h1 x88))

let finv2 x3 x44 x88 tmp =
  let h7 = ST.get () in
  fsquare_times x88 x44 44ul;
  fmul x88 x88 x44; // x88 = S.fmul (fsquare_times x44 44) x44
  let h8 = ST.get () in
  assert (as_nat h8 x88 == S.fmul (SI.fsquare_times (as_nat h7 x44) 44) (as_nat h7 x44));

  fsquare_times tmp x88 88ul;
  fmul tmp tmp x88; // tmp = x176 = S.fmul (fsquare_times x88 88) x88
  let h9 = ST.get () in
  assert (as_nat h9 tmp == S.fmul (SI.fsquare_times (as_nat h8 x88) 88) (as_nat h8 x88));

  fsquare_times_in_place tmp 44ul;
  fmul tmp tmp x44; // tmp = x220 = S.fmul (fsquare_times x176 44) x44
  let h10 = ST.get () in
  assert (as_nat h10 tmp == S.fmul (SI.fsquare_times (as_nat h9 tmp) 44) (as_nat h7 x44));

  fsquare_times_in_place tmp 3ul;
  fmul tmp tmp x3; // tmp = x223 = S.fmul (fsquare_times x220 3) x3
  let h11 = ST.get () in
  assert (as_nat h11 tmp == S.fmul (SI.fsquare_times (as_nat h10 tmp) 3) (as_nat h7 x3))


inline_for_extraction noextract
val finv3 (tmp x22 f x2:felem) : Stack unit
  (requires fun h ->
    live h tmp /\ live h x22 /\ live h f /\ live h x2 /\
    disjoint tmp x22 /\ disjoint tmp f /\ disjoint tmp x2 /\
    disjoint x22 f /\ disjoint x22 x2 /\ disjoint f x2 /\
    fe_lt_prime h tmp /\ fe_lt_prime h x22 /\
    fe_lt_prime h f /\ fe_lt_prime h x2)
  (ensures fun h0 _ h1 -> modifies (loc tmp) h0 h1 /\
   (let _x223 = as_nat h0 tmp in
    let _x22 = as_nat h0 x22 in
    let _f = as_nat h0 f in
    let _x2 = as_nat h0 x2 in
    let _r = S.fmul (SI.fsquare_times _x223 23) _x22 in
    let _r = S.fmul (SI.fsquare_times _r 5) _f in
    let _r = S.fmul (SI.fsquare_times _r 3) _x2 in
    let _r = S.fmul (SI.fsquare_times _r 2) _f in
    as_nat h1 tmp == _r /\ fe_lt_prime h1 tmp))

let finv3 tmp x22 f x2 =
  let h0 = ST.get () in
  fsquare_times_in_place tmp 23ul;
  fmul tmp tmp x22; // tmp = r = S.fmul (fsquare_times x223 23) x22
  let h1 = ST.get () in
  assert (as_nat h1 tmp == S.fmul (SI.fsquare_times (as_nat h0 tmp) 23) (as_nat h0 x22));

  fsquare_times_in_place tmp 5ul;
  fmul tmp tmp f; // tmp = r = S.fmul (fsquare_times r 5) f
  let h2 = ST.get () in
  assert (as_nat h2 tmp == S.fmul (SI.fsquare_times (as_nat h1 tmp) 5) (as_nat h0 f));

  fsquare_times_in_place tmp 3ul;
  fmul tmp tmp x2; // tmp = r = S.fmul (fsquare_times r 3) x2
  let h3 = ST.get () in
  assert (as_nat h3 tmp == S.fmul (SI.fsquare_times (as_nat h2 tmp) 3) (as_nat h0 x2));

  fsquare_times_in_place tmp 2ul;
  fmul tmp tmp f; // tmp = r = S.fmul (fsquare_times r 2) f
  let h4 = ST.get () in
  assert (as_nat h4 tmp == S.fmul (SI.fsquare_times (as_nat h3 tmp) 2) (as_nat h0 f))


inline_for_extraction noextract
val finv0123 (f x2 x3 x22 x44 x88 tmp:felem) : Stack unit
  (requires fun h ->
    live h f /\ live h x2 /\ live h x3 /\ live h x22 /\
    live h x44 /\ live h x88 /\ live h tmp /\
    disjoint f x2 /\ disjoint f x3 /\ disjoint f x22 /\
    disjoint f x44 /\ disjoint f x88 /\ disjoint f tmp /\
    disjoint x2 x3 /\ disjoint x2 x22 /\ disjoint x2 x44 /\
    disjoint x2 x88 /\ disjoint x2 tmp /\ disjoint x3 x22 /\
    disjoint x3 x44 /\ disjoint x3 x88 /\ disjoint x3 tmp /\
    disjoint x22 x44 /\ disjoint x22 x88 /\ disjoint x22 tmp /\
    disjoint x44 x88 /\ disjoint x44 tmp /\ disjoint x88 tmp /\
    fe_lt_prime h f)
  (ensures fun h0 _ h1 -> modifies (loc x2 |+| loc x3 |+| loc x22 |+| loc x44 |+| loc x88 |+| loc tmp) h0 h1 /\
    as_nat h1 tmp == SI.finv (as_nat h0 f) /\ fe_lt_prime h1 tmp)

let finv0123 f x2 x3 x22 x44 x88 tmp =
  let h0 = ST.get () in
  fsquare_times x2 f 1ul;
  fmul x2 x2 f; // x2 = S.fmul (fsquare_times f 1) f
  let h1 = ST.get () in
  assert (as_nat h1 x2 == S.fmul (SI.fsquare_times (as_nat h0 f) 1) (as_nat h0 f));
  assert (modifies (loc x2) h0 h1);

  fsquare_times x3 x2 1ul;
  fmul x3 x3 f; // x3 = S.fmul (fsquare_times x2 1) f
  let h2 = ST.get () in
  assert (as_nat h2 x3 == S.fmul (SI.fsquare_times (as_nat h1 x2) 1) (as_nat h0 f));
  assert (modifies (loc x3) h1 h2);

  finv1 x2 x3 x22 x44 tmp;
  finv2 x3 x44 x88 tmp;
  let h3 = ST.get () in
  assert (modifies (loc x22 |+| loc x44 |+| loc x88 |+| loc tmp) h2 h3);
  finv3 tmp x22 f x2;
  let h4 = ST.get () in
  assert (modifies (loc tmp) h3 h4)


#push-options "--z3rlimit 150"

inline_for_extraction noextract
val finv_ (out f: felem) : Stack unit
  (requires fun h ->
    live h out /\ live h f /\ disjoint out f /\
    fe_lt_prime h f)
  (ensures  fun h0 _ h1 -> modifies (loc out) h0 h1 /\
    as_nat h1 out == SI.finv (as_nat h0 f)  /\
    fe_lt_prime h1 out)

let finv_ out f =
  let h0 = ST.get () in
  push_frame ();
  let x2 = create_felem () in
  let x3 = create_felem () in
  let x22 = create_felem () in
  let x44 = create_felem () in
  let x88 = create_felem () in
  let tmp = create_felem () in

  finv0123 f x2 x3 x22 x44 x88 tmp;
  let h1 = ST.get () in
  assert (as_nat h1 tmp == SI.finv (as_nat h0 f) /\ fe_lt_prime h1 tmp);
  copy out tmp;
  let h2 = ST.get () in
  assert (as_nat h2 out == SI.finv (as_nat h0 f) /\ fe_lt_prime h2 out);
  pop_frame ()


val finv (out f: felem) : Stack unit
  (requires fun h ->
    live h out /\ live h f /\ disjoint out f /\
    fe_lt_prime h f)
  (ensures  fun h0 _ h1 -> modifies (loc out) h0 h1 /\
    as_nat h1 out == S.finv (as_nat h0 f)  /\
    fe_lt_prime h1 out)

[@CInline]
let finv out f =
  let h0 = ST.get () in
  SI.finv_is_finv_lemma (as_nat h0 f);
  finv_ out f
