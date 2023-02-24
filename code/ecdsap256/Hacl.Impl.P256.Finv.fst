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

open Hacl.Spec.P256.MontgomeryMultiplication
friend Hacl.Spec.P256.MontgomeryMultiplication

module LSeq = Lib.Sequence
module M = Lib.NatMod
module S = Spec.P256
module LE = Lib.Exponentiation
module SE = Spec.Exponentiation
module BE = Hacl.Impl.Exponentiation
module SI = Hacl.Spec.P256.Finv

#reset-options "--z3rlimit 50 --fuel 0 --ifuel 0"

unfold
let linv_ctx (a:LSeq.lseq uint64 0) : Type0 = True

unfold
let linv (a:LSeq.lseq uint64 4) : Type0 =
  let open Lib.Sequence in
  felem_seq_as_nat a < S.prime

unfold
let refl (a:LSeq.lseq uint64 4{linv a}) : GTot S.felem =
  felem_seq_as_nat a


inline_for_extraction noextract
let mk_to_p256_prime_comm_monoid : BE.to_comm_monoid U64 4ul 0ul = {
  BE.a_spec = S.felem;
  BE.comm_monoid = SI.nat_mod_comm_monoid;
  BE.linv_ctx = linv_ctx;
  BE.linv = linv;
  BE.refl = refl;
}

//------------------------
// TODO: compare the performance of mod_solinas and mod_montgomery

val mul_mod_solinas (x y res:felem) : Stack unit
  (requires fun h ->
    live h x /\ live h y /\ live h res /\
    eq_or_disjoint x y /\ eq_or_disjoint x res /\ eq_or_disjoint y res /\
    as_nat h x < S.prime /\ as_nat h y < S.prime)
  (ensures fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    as_nat h1 res == as_nat h0 x * as_nat h0 y % S.prime)

[@CInline]
let mul_mod_solinas x y res =
  push_frame ();
  let tmp = create 8ul (u64 0) in
  let h0 = ST.get () in
  bn_mul4 x y tmp;
  let h1 = ST.get () in
  assert (wide_as_nat h1 tmp == as_nat h0 x * as_nat h0 y);
  solinas_reduction_impl tmp res;
  let h2 = ST.get () in
  assert (as_nat h2 res == wide_as_nat h1 tmp % S.prime);
  pop_frame ()


val sqr_mod_solinas (x res:felem) : Stack unit
  (requires fun h ->
    live h x /\ live h res /\ eq_or_disjoint x res /\
    as_nat h x < S.prime)
  (ensures fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    as_nat h1 res == as_nat h0 x * as_nat h0 x % S.prime)

[@CInline]
let sqr_mod_solinas x res =
  push_frame ();
  let tmp = create 8ul (u64 0) in
  let h0 = ST.get () in
  bn_sqr4 x tmp;
  let h1 = ST.get () in
  assert (wide_as_nat h1 tmp == as_nat h0 x * as_nat h0 x);
  solinas_reduction_impl tmp res;
  let h2 = ST.get () in
  assert (as_nat h2 res == wide_as_nat h1 tmp % S.prime);
  pop_frame ()

//------------------------

inline_for_extraction noextract
val one_mod : BE.lone_st U64 4ul 0ul mk_to_p256_prime_comm_monoid
let one_mod ctx one = bn_set_one4 one


inline_for_extraction noextract
val mul_mod : BE.lmul_st U64 4ul 0ul mk_to_p256_prime_comm_monoid
let mul_mod ctx x y xy = mul_mod_solinas x y xy


inline_for_extraction noextract
val sqr_mod : BE.lsqr_st U64 4ul 0ul mk_to_p256_prime_comm_monoid
let sqr_mod ctx x xx = sqr_mod_solinas x xx


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
    as_nat h1 out == SI.fsquare_times (as_nat h0 a) (v b))

[@CInline]
let fsquare_times out a b =
  let h0 = ST.get () in
  SE.exp_pow2_lemma SI.mk_nat_mod_concrete_ops (as_nat h0 a) (v b);
  BE.lexp_pow2 4ul 0ul mk_p256_prime_concrete_ops (null uint64) a b out


// TODO: rm
val fexp_vartime (out a b:felem) : Stack unit
  (requires fun h ->
    live h out /\ live h a /\ live h b /\
    disjoint out a /\ disjoint out b /\
    as_nat h a < S.prime)
  (ensures  fun h0 _ h1 -> modifies (loc out) h0 h1 /\
    as_nat h1 out == M.pow_mod #S.prime (as_nat h0 a) (as_nat h0 b))

[@CInline]
let fexp_vartime out a b =
  let h0 = ST.get () in
  assert_norm (pow2 5 = 32);
  as_nat_bound h0 b;
  bignum_bn_v_is_as_nat h0 b;
  BE.lexp_fw_vartime 4ul 0ul
    mk_p256_prime_concrete_ops 5ul (null uint64) a 4ul 256ul b out;
  let h1 = ST.get () in
  SE.exp_fw_lemma SI.mk_nat_mod_concrete_ops (as_nat h0 a) 256 (as_nat h0 b) 5;
  LE.exp_fw_lemma SI.nat_mod_comm_monoid (as_nat h0 a) 256 (as_nat h0 b) 5;
  assert (as_nat h1 out == LE.pow SI.nat_mod_comm_monoid (as_nat h0 a) (as_nat h0 b));
  M.lemma_pow_nat_mod_is_pow #S.prime (as_nat h0 a) (as_nat h0 b);
  assert (as_nat h1 out == M.pow (as_nat h0 a) (as_nat h0 b) % S.prime);
  M.lemma_pow_mod #S.prime (as_nat h0 a) (as_nat h0 b)


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
  bn_make_u64_4 b0 b1 b2 b3 b


let finv a res =
  push_frame ();
  let b = create 4ul (u64 0) in
  make_prime_minus_2 b;

  let tmp = create 4ul (u64 0) in
  fromDomain a tmp;
  fexp_vartime res tmp b;
  toDomain res res;
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
  bn_make_u64_4 b0 b1 b2 b3 b


let fsqrt a res =
  push_frame ();
  let b = create 4ul (u64 0) in
  make_prime_plus_1_div_4 b;

  let tmp = create 4ul (u64 0) in
  fromDomain a tmp;
  fexp_vartime res tmp b;
  toDomain res res;
  pop_frame ()

//-----------------------------------------------
