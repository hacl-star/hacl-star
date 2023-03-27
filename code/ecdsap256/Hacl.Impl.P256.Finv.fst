module Hacl.Impl.P256.Finv

open FStar.Mul
open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer

open Hacl.Impl.P256.Bignum
open Hacl.Impl.P256.Field
open Hacl.Impl.P256.Core
open Hacl.Impl.P256.SolinasReduction

module LSeq = Lib.Sequence

module M = Lib.NatMod
module LE = Lib.Exponentiation
module SE = Spec.Exponentiation
module BE = Hacl.Impl.Exponentiation

module S = Spec.P256
module SI = Hacl.Spec.P256.Finv
module SB = Hacl.Spec.P256.Bignum
module SM = Hacl.Spec.P256.Montgomery

#reset-options "--z3rlimit 50 --fuel 0 --ifuel 0"

unfold
let linv_ctx (a:LSeq.lseq uint64 0) : Type0 = True

unfold
let linv (a:LSeq.lseq uint64 4) : Type0 =
  SB.felem_seq_as_nat a < S.prime

unfold
let refl (a:LSeq.lseq uint64 4{linv a}) : GTot S.felem =
  SM.from_mont (SB.felem_seq_as_nat a)


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


val fsquare_times (out a:felem) (b:size_t) : Stack unit
  (requires fun h ->
    live h out /\ live h a /\ disjoint out a /\
    as_nat h a < S.prime)
  (ensures  fun h0 _ h1 -> modifies (loc out) h0 h1 /\
    fmont_as_nat h1 out == SI.fsquare_times (fmont_as_nat h0 a) (v b))

[@CInline]
let fsquare_times out a b =
  let h0 = ST.get () in
  BE.lexp_pow2 4ul 0ul mk_p256_prime_concrete_ops (null uint64) a b out;
  let h1 = ST.get () in
  assert (fmont_as_nat h1 out == LE.exp_pow2 SI.nat_mod_comm_monoid (fmont_as_nat h0 a) (v b));
  SE.exp_pow2_lemma SI.mk_nat_mod_concrete_ops (fmont_as_nat h0 a) (v b)


// TODO: rm
val fexp_vartime (out a b:felem) : Stack unit
  (requires fun h ->
    live h out /\ live h a /\ live h b /\
    disjoint out a /\ disjoint out b /\
    as_nat h a < S.prime)
  (ensures  fun h0 _ h1 -> modifies (loc out) h0 h1 /\
    as_nat h1 out < S.prime /\
    fmont_as_nat h1 out == M.pow_mod #S.prime (fmont_as_nat h0 a) (as_nat h0 b))

[@CInline]
let fexp_vartime out a b =
  let h0 = ST.get () in
  assert_norm (pow2 5 = 32);
  SB.as_nat_bound (as_seq h0 b);
  SB.bn_v_is_as_nat (as_seq h0 b);
  BE.lexp_fw_vartime 4ul 0ul
    mk_p256_prime_concrete_ops 5ul (null uint64) a 4ul 256ul b out;
  let h1 = ST.get () in
  SE.exp_fw_lemma SI.mk_nat_mod_concrete_ops (fmont_as_nat h0 a) 256 (as_nat h0 b) 5;
  LE.exp_fw_lemma SI.nat_mod_comm_monoid (fmont_as_nat h0 a) 256 (as_nat h0 b) 5;
  assert (fmont_as_nat h1 out == LE.pow SI.nat_mod_comm_monoid (fmont_as_nat h0 a) (as_nat h0 b));
  M.lemma_pow_nat_mod_is_pow #S.prime (fmont_as_nat h0 a) (as_nat h0 b);
  assert (fmont_as_nat h1 out == M.pow (fmont_as_nat h0 a) (as_nat h0 b) % S.prime);
  M.lemma_pow_mod #S.prime (fmont_as_nat h0 a) (as_nat h0 b)


//--------------------------------
// TODO: use an addition chain from Hacl.Spec.P256.Finv
inline_for_extraction noextract
val make_prime_minus_2: b:felem -> Stack unit
  (requires fun h -> live h b)
  (ensures  fun h0 _ h1 -> modifies (loc b) h0 h1 /\
    as_nat h1 b == S.prime - 2)

let make_prime_minus_2 b =
  // 0xffffffff00000001000000000000000000000000fffffffffffffffffffffffd
  [@inline_let] let b0 = u64 0xfffffffffffffffd in
  [@inline_let] let b1 = u64 0xffffffff in
  [@inline_let] let b2 = u64 0x0 in
  [@inline_let] let b3 = u64 0xffffffff00000001 in
  assert_norm (v b0 + v b1 * pow2 64 + v b2 * pow2 128 + v b3 * pow2 192 = S.prime - 2);
  bn_make_u64_4 b b0 b1 b2 b3


[@CInline]
let finv res a =
  push_frame ();
  let b = create 4ul (u64 0) in
  make_prime_minus_2 b;

  let tmp = create 4ul (u64 0) in
  copy tmp a;
  fexp_vartime res tmp b;
  pop_frame ()


inline_for_extraction noextract
val make_prime_plus_1_div_4: b:felem -> Stack unit
  (requires fun h -> live h b)
  (ensures  fun h0 _ h1 -> modifies (loc b) h0 h1 /\
    as_nat h1 b == (S.prime + 1) / 4)

let make_prime_plus_1_div_4 b =
  // 0x3fffffffc0000000400000000000000000000000400000000000000000000000
  [@inline_let] let b0 = u64 0x0 in
  [@inline_let] let b1 = u64 0x40000000 in
  [@inline_let] let b2 = u64 0x4000000000000000 in
  [@inline_let] let b3 = u64 0x3fffffffc0000000 in
  assert_norm (v b0 + v b1 * pow2 64 + v b2 * pow2 128 + v b3 * pow2 192 = (S.prime + 1) / 4);
  bn_make_u64_4 b b0 b1 b2 b3


[@CInline]
let fsqrt res a =
  push_frame ();
  let b = create 4ul (u64 0) in
  make_prime_plus_1_div_4 b;

  let tmp = create 4ul (u64 0) in
  copy tmp a;
  fexp_vartime res tmp b;
  pop_frame ()
