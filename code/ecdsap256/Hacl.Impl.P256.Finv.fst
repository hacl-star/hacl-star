module Hacl.Impl.P256.Finv

open FStar.Mul
open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer

open Hacl.Impl.P256.Bignum
open Hacl.Impl.P256.Field

module SE = Spec.Exponentiation
module BE = Hacl.Impl.Exponentiation
module BD = Hacl.Spec.Bignum.Definitions
module LSeq = Lib.Sequence

module S = Spec.P256
module SI = Hacl.Spec.P256.Finv
module SM = Hacl.Spec.P256.Montgomery

#reset-options "--z3rlimit 50 --fuel 0 --ifuel 0"

unfold
let linv_ctx (a:LSeq.lseq uint64 0) : Type0 = True

unfold
let linv (a:LSeq.lseq uint64 4) : Type0 =
  BD.bn_v a < S.prime

unfold
let refl (a:LSeq.lseq uint64 4{linv a}) : GTot S.felem =
  SM.from_mont (BD.bn_v a)


inline_for_extraction noextract
let mk_to_p256_prime_comm_monoid : BE.to_comm_monoid U64 4ul 0ul = {
  BE.a_spec = S.felem;
  BE.comm_monoid = SI.nat_mod_comm_monoid;
  BE.linv_ctx = linv_ctx;
  BE.linv = linv;
  BE.refl = refl;
}


inline_for_extraction noextract
val one_mod : BE.lone_st U64 4ul 0ul mk_to_p256_prime_comm_monoid
let one_mod ctx one = make_fone one


inline_for_extraction noextract
val mul_mod : BE.lmul_st U64 4ul 0ul mk_to_p256_prime_comm_monoid
let mul_mod ctx x y xy = fmul xy x y


inline_for_extraction noextract
val sqr_mod : BE.lsqr_st U64 4ul 0ul mk_to_p256_prime_comm_monoid
let sqr_mod ctx x xx = fsqr xx x


inline_for_extraction noextract
let mk_p256_prime_concrete_ops : BE.concrete_ops U64 4ul 0ul = {
  BE.to = mk_to_p256_prime_comm_monoid;
  BE.lone = one_mod;
  BE.lmul = mul_mod;
  BE.lsqr = sqr_mod;
}


inline_for_extraction noextract
val fsquare_times_in_place (out:felem) (b:size_t) : Stack unit
  (requires fun h ->
    live h out /\ as_nat h out < S.prime)
  (ensures  fun h0 _ h1 -> modifies (loc out) h0 h1 /\
    as_nat h1 out < S.prime /\
    fmont_as_nat h1 out == SI.fsquare_times (fmont_as_nat h0 out) (v b))

let fsquare_times_in_place out b =
  let h0 = ST.get () in
  SE.exp_pow2_lemma SI.mk_nat_mod_concrete_ops (fmont_as_nat h0 out) (v b);
  BE.lexp_pow2_in_place 4ul 0ul mk_p256_prime_concrete_ops (null uint64) out b


inline_for_extraction noextract
val fsquare_times (out a:felem) (b:size_t) : Stack unit
  (requires fun h ->
    live h out /\ live h a /\ disjoint out a /\
    as_nat h a < S.prime)
  (ensures  fun h0 _ h1 -> modifies (loc out) h0 h1 /\
    as_nat h1 out < S.prime /\
    fmont_as_nat h1 out == SI.fsquare_times (fmont_as_nat h0 a) (v b))

let fsquare_times out a b =
  let h0 = ST.get () in
  SE.exp_pow2_lemma SI.mk_nat_mod_concrete_ops (fmont_as_nat h0 a) (v b);
  BE.lexp_pow2 4ul 0ul mk_p256_prime_concrete_ops (null uint64) a b out


inline_for_extraction noextract
val finv_30 (x30 x2 tmp1 tmp2 a:felem) : Stack unit
  (requires fun h ->
    live h a /\ live h x30 /\ live h x2 /\ live h tmp1 /\ live h tmp2 /\
    disjoint a x30 /\ disjoint a x2 /\ disjoint a tmp1 /\ disjoint a tmp2 /\
    disjoint x30 x2 /\ disjoint x30 tmp1 /\ disjoint x30 tmp2 /\
    disjoint x2 tmp1 /\ disjoint x2 tmp2 /\ disjoint tmp1 tmp2 /\
    as_nat h a < S.prime)
  (ensures fun h0 _ h1 -> modifies (loc x30 |+| loc x2 |+| loc tmp1 |+| loc tmp2) h0 h1 /\
    as_nat h1 x30 < S.prime /\ as_nat h1 x2 < S.prime /\
    (let f = fmont_as_nat h0 a in
    let x2_s = S.fmul (SI.fsquare_times f 1) f in
    let x3_s = S.fmul (SI.fsquare_times x2_s 1) f in
    let x6_s = S.fmul (SI.fsquare_times x3_s 3) x3_s in
    let x12_s = S.fmul (SI.fsquare_times x6_s 6) x6_s in
    let x15_s = S.fmul (SI.fsquare_times x12_s 3) x3_s in
    let x30_s = S.fmul (SI.fsquare_times x15_s 15) x15_s in
    fmont_as_nat h1 x30 = x30_s /\ fmont_as_nat h1 x2 = x2_s))

let finv_30 x30 x2 tmp1 tmp2 a =
  let h0 = ST.get () in
  fsquare_times x2 a 1ul;
  fmul x2 x2 a;
  let h1 = ST.get () in
  assert (fmont_as_nat h1 x2 ==
    S.fmul (SI.fsquare_times (fmont_as_nat h0 a) 1) (fmont_as_nat h0 a));

  fsquare_times x30 x2 1ul;
  fmul x30 x30 a;
  let h2 = ST.get () in
  assert (fmont_as_nat h2 x30 == // x3
    S.fmul (SI.fsquare_times (fmont_as_nat h1 x2) 1) (fmont_as_nat h0 a));

  fsquare_times tmp1 x30 3ul;
  fmul tmp1 tmp1 x30;
  let h3 = ST.get () in
  assert (fmont_as_nat h3 tmp1 == // x6
    S.fmul (SI.fsquare_times (fmont_as_nat h2 x30) 3) (fmont_as_nat h2 x30));

  fsquare_times tmp2 tmp1 6ul;
  fmul tmp2 tmp2 tmp1;
  let h4 = ST.get () in
  assert (fmont_as_nat h4 tmp2 == // x12
    S.fmul (SI.fsquare_times (fmont_as_nat h3 tmp1) 6) (fmont_as_nat h3 tmp1));

  fsquare_times tmp1 tmp2 3ul;
  fmul tmp1 tmp1 x30;
  let h5 = ST.get () in
  assert (fmont_as_nat h5 tmp1 == // x15
    S.fmul (SI.fsquare_times (fmont_as_nat h4 tmp2) 3) (fmont_as_nat h2 x30));

  fsquare_times x30 tmp1 15ul;
  fmul x30 x30 tmp1;
  let h6 = ST.get () in
  assert (fmont_as_nat h6 x30 == // x30
    S.fmul (SI.fsquare_times (fmont_as_nat h5 tmp1) 15) (fmont_as_nat h5 tmp1))


inline_for_extraction noextract
val finv_256 (x256 x2 x30 a:felem) : Stack unit
  (requires fun h ->
    live h a /\ live h x30 /\ live h x2 /\ live h x256 /\
    disjoint a x30 /\ disjoint a x2 /\ disjoint a x256 /\
    disjoint x30 x2 /\ disjoint x30 x256 /\ disjoint x2 x256 /\
    as_nat h a < S.prime /\ as_nat h x30 < S.prime /\ as_nat h x2 < S.prime)
  (ensures fun h0 _ h1 -> modifies (loc x256 |+| loc x2) h0 h1 /\
    as_nat h1 x256 < S.prime /\
   (let f = fmont_as_nat h0 a in
    let x30 = fmont_as_nat h0 x30 in
    let x2 = fmont_as_nat h0 x2 in
    let x32_s = S.fmul (SI.fsquare_times x30 2) x2 in
    let x64_s = S.fmul (SI.fsquare_times x32_s 32) f in
    let x192_s = S.fmul (SI.fsquare_times x64_s 128) x32_s in
    let x224_s = S.fmul (SI.fsquare_times x192_s 32) x32_s in
    let x254_s = S.fmul (SI.fsquare_times x224_s 30) x30 in
    let x256_s = S.fmul (SI.fsquare_times x254_s 2) f in
    fmont_as_nat h1 x256 = x256_s))

let finv_256 x256 x2 x30 a =
  let h0 = ST.get () in
  fsquare_times x256 x30 2ul;
  fmul x256 x256 x2;
  let h1 = ST.get () in
  assert (fmont_as_nat h1 x256 == // x32
    S.fmul (SI.fsquare_times (fmont_as_nat h0 x30) 2) (fmont_as_nat h0 x2));

  fsquare_times x2 x256 32ul;
  fmul x2 x2 a;
  let h2 = ST.get () in
  assert (fmont_as_nat h2 x2 == // x64
    S.fmul (SI.fsquare_times (fmont_as_nat h1 x256) 32) (fmont_as_nat h0 a));

  fsquare_times_in_place x2 128ul;
  fmul x2 x2 x256;
  let h3 = ST.get () in
  assert (fmont_as_nat h3 x2 == // x192
    S.fmul (SI.fsquare_times (fmont_as_nat h2 x2) 128) (fmont_as_nat h1 x256));

  fsquare_times_in_place x2 32ul;
  fmul x2 x2 x256;
  let h4 = ST.get () in
  assert (fmont_as_nat h4 x2 == // x224
    S.fmul (SI.fsquare_times (fmont_as_nat h3 x2) 32) (fmont_as_nat h1 x256));

  fsquare_times_in_place x2 30ul;
  fmul x2 x2 x30;
  let h5 = ST.get () in
  assert (fmont_as_nat h5 x2 == // x254
    S.fmul (SI.fsquare_times (fmont_as_nat h4 x2) 30) (fmont_as_nat h0 x30));

  fsquare_times_in_place x2 2ul;
  fmul x256 x2 a;
  let h6 = ST.get () in
  assert (fmont_as_nat h6 x256 == // x256
    S.fmul (SI.fsquare_times (fmont_as_nat h5 x2) 2) (fmont_as_nat h0 a))


[@CInline]
let finv res a =
  let h0 = ST.get () in
  push_frame ();
  let tmp  = create 16ul (u64 0) in
  let x30  = sub tmp 0ul 4ul in
  let x2   = sub tmp 4ul 4ul in
  let tmp1 = sub tmp 8ul 4ul in
  let tmp2 = sub tmp 12ul 4ul in
  finv_30 x30 x2 tmp1 tmp2 a;
  finv_256 tmp1 x2 x30 a;
  copy res tmp1;
  let h1 = ST.get () in
  assert (fmont_as_nat h1 res == SI.finv (fmont_as_nat h0 a));
  SI.finv_is_finv_lemma (fmont_as_nat h0 a);
  pop_frame ()


inline_for_extraction noextract
val fsqrt_254 (tmp2 tmp1 a:felem) : Stack unit
  (requires fun h ->
    live h a /\ live h tmp1 /\ live h tmp2 /\
    disjoint a tmp1 /\ disjoint a tmp2 /\ disjoint tmp1 tmp2 /\
    as_nat h a < S.prime)
  (ensures fun h0 _ h1 -> modifies (loc tmp1 |+| loc tmp2) h0 h1 /\
    as_nat h1 tmp2 < S.prime /\
    (let f = fmont_as_nat h0 a in
    let x2 = S.fmul (SI.fsquare_times f 1) f in
    let x4 = S.fmul (SI.fsquare_times x2 2) x2 in
    let x8 = S.fmul (SI.fsquare_times x4 4) x4 in
    let x16 = S.fmul (SI.fsquare_times x8 8) x8 in
    let x32 = S.fmul (SI.fsquare_times x16 16) x16 in
    let x64 = S.fmul (SI.fsquare_times x32 32) f in
    let x160 = S.fmul (SI.fsquare_times x64 96) f in
    let x254 = SI.fsquare_times x160 94 in
    fmont_as_nat h1 tmp2 == x254))

let fsqrt_254 tmp2 tmp1 a =
  let h0 = ST.get () in
  fsquare_times tmp1 a 1ul;
  fmul tmp1 tmp1 a;
  let h1 = ST.get () in
  assert (fmont_as_nat h1 tmp1 == // x2
    S.fmul (SI.fsquare_times (fmont_as_nat h0 a) 1) (fmont_as_nat h0 a));

  fsquare_times tmp2 tmp1 2ul;
  fmul tmp2 tmp2 tmp1;
  let h2 = ST.get () in
  assert (fmont_as_nat h2 tmp2 == // x4
    S.fmul (SI.fsquare_times (fmont_as_nat h1 tmp1) 2) (fmont_as_nat h1 tmp1));

  fsquare_times tmp1 tmp2 4ul;
  fmul tmp1 tmp1 tmp2;
  let h3 = ST.get () in
  assert (fmont_as_nat h3 tmp1 == // x8
    S.fmul (SI.fsquare_times (fmont_as_nat h2 tmp2) 4) (fmont_as_nat h2 tmp2));

  fsquare_times tmp2 tmp1 8ul;
  fmul tmp2 tmp2 tmp1;
  let h4 = ST.get () in
  assert (fmont_as_nat h4 tmp2 == // x16
    S.fmul (SI.fsquare_times (fmont_as_nat h3 tmp1) 8) (fmont_as_nat h3 tmp1));

  fsquare_times tmp1 tmp2 16ul;
  fmul tmp1 tmp1 tmp2;
  let h5 = ST.get () in
  assert (fmont_as_nat h5 tmp1 == // x32
    S.fmul (SI.fsquare_times (fmont_as_nat h4 tmp2) 16) (fmont_as_nat h4 tmp2));

  fsquare_times tmp2 tmp1 32ul;
  fmul tmp2 tmp2 a;
  let h6 = ST.get () in
  assert (fmont_as_nat h6 tmp2 == // x64
    S.fmul (SI.fsquare_times (fmont_as_nat h5 tmp1) 32) (fmont_as_nat h0 a));

  fsquare_times_in_place tmp2 96ul;
  fmul tmp2 tmp2 a;
  let h7 = ST.get () in
  assert (fmont_as_nat h7 tmp2 == // x160
    S.fmul (SI.fsquare_times (fmont_as_nat h6 tmp2) 96) (fmont_as_nat h0 a));

  fsquare_times_in_place tmp2 94ul


[@CInline]
let fsqrt res a =
  let h0 = ST.get () in
  push_frame ();
  let tmp  = create 8ul (u64 0) in
  let tmp1 = sub tmp 0ul 4ul in
  let tmp2 = sub tmp 4ul 4ul in
  fsqrt_254 tmp2 tmp1 a;
  copy res tmp2;
  let h1 = ST.get () in
  assert (fmont_as_nat h1 res == SI.fsqrt (fmont_as_nat h0 a));
  SI.fsqrt_is_fsqrt_lemma (fmont_as_nat h0 a);
  pop_frame ()
