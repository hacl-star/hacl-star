module Hacl.Impl.PCurves.Finv.P521

open FStar.Mul
open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer

open Hacl.Impl.PCurves.Bignum
open Hacl.Impl.PCurves.Field

module SE = Spec.Exponentiation
module LE = Lib.Exponentiation
module BE = Hacl.Impl.Exponentiation
module BD = Hacl.Spec.Bignum.Definitions
module LSeq = Lib.Sequence

module S = Spec.PCurves
module SI = Hacl.Spec.PCurves.Finv
module FI = Hacl.Impl.PCurves.Finv
module SM = Hacl.Spec.PCurves.Montgomery

open Hacl.Impl.PCurves.InvSqrt
open Spec.P521
open Hacl.Impl.PCurves.Constants
open Hacl.Impl.PCurves.Constants.P521
open Hacl.Impl.PCurves.Bignum.P521
open Hacl.Impl.PCurves.Field.P521
open Hacl.Impl.PCurves.Finv

module M = Lib.NatMod

#reset-options "--z3rlimit 50 --fuel 0 --ifuel 0"

inline_for_extraction noextract
val fexp_vartime (out a b:felem) : Stack unit
  (requires fun h ->
    live h out /\ live h a /\ live h b /\
    disjoint out a /\ disjoint out b /\
    as_nat h a < S.prime)
  (ensures  fun h0 _ h1 -> modifies (loc out) h0 h1 /\
    as_nat h1 out == M.pow_mod #S.prime (as_nat h0 a) (as_nat h0 b))

inline_for_extraction noextract
let fexp_vartime out a b =
  let h0 = ST.get () in
  assert_norm(pow2 5 == 32);
  bn_v_is_as_nat9 (as_seq h0 b);
  assume(as_nat h0 b < pow2 521);
//  BE.lexp_rl_vartime 9ul 0ul
//    mk_pcurve_prime_concrete_ops (null uint64) a 9ul 521ul b out;
  BE.lexp_fw_vartime 9ul 0ul
    mk_pcurve_prime_concrete_ops 5ul (null uint64) a 9ul 521ul b out;
  let h1 = ST.get () in
  SE.exp_fw_lemma SI.mk_nat_mod_concrete_ops (as_nat h0 a) 521 (as_nat h0 b) 5;
  LE.exp_fw_lemma SI.nat_mod_comm_monoid (as_nat h0 a) 521 (as_nat h0 b) 5;
  admit();
  assert (as_nat h1 out == LE.pow SI.nat_mod_comm_monoid (as_nat h0 a) (as_nat h0 b));
  M.lemma_pow_nat_mod_is_pow #S.prime (as_nat h0 a) (as_nat h0 b);
  assert (as_nat h1 out == M.pow (as_nat h0 a) (as_nat h0 b) % S.prime);
  M.lemma_pow_mod #S.prime (as_nat h0 a) (as_nat h0 b)


inline_for_extraction noextract
val make_prime521_minus_2: b:felem -> Stack unit
  (requires fun h -> live h b)
  (ensures  fun h0 _ h1 -> modifies (loc b) h0 h1 /\
    as_nat h1 b == S.prime - 2)

let make_prime521_minus_2 n =
    // prime = 0x01fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffd
    [@inline_let] let n0 = u64 0xfffffffffffffffd in
    [@inline_let] let n1 = u64 0xffffffffffffffff in
    [@inline_let] let n2 = u64 0xffffffffffffffff in
    [@inline_let] let n3 = u64 0xffffffffffffffff in
    [@inline_let] let n4 = u64 0xffffffffffffffff in
    [@inline_let] let n5 = u64 0xffffffffffffffff in
    [@inline_let] let n6 = u64 0xffffffffffffffff in
    [@inline_let] let n7 = u64 0xffffffffffffffff in
    [@inline_let] let n8 = u64 0x1ff in
    assert_norm (v n0 + v n1 * pow2 64 + v n2 * pow2 128 + v n3 * pow2 192 +
                 v n4 * pow2 256 + v n5 * pow2 320 + v n6 * pow2 384 + v n7 * pow2 448 + v n8 * pow2 512 = Spec.P521.p521_prime - 2);
    bn_make_u64_9 n n0 n1 n2 n3 n4 n5 n6 n7 n8

[@CInline]
val p521_finv: res:felem -> a:felem -> Stack unit
    (requires fun h ->
      live h a /\ live h res /\ eq_or_disjoint a res /\
      as_nat h a < S.prime)
    (ensures fun h0 _ h1 -> modifies (loc res) h0 h1 /\
      as_nat h1 res < S.prime /\
      fmont_as_nat h1 res = S.finv (fmont_as_nat h0 a))

let p521_finv res a =
  push_frame ();
  let b = create 9ul (u64 0) in
  make_prime521_minus_2 b;
  let tmp = create 9ul (u64 0) in
  copy tmp a;
  fexp_vartime res tmp b;
  admit();
  pop_frame ()


inline_for_extraction noextract
val make_prime521_plus_1_div_4: b:felem -> Stack unit
  (requires fun h -> live h b)
  (ensures  fun h0 _ h1 -> modifies (loc b) h0 h1 /\
    as_nat h1 b == (S.prime + 1) / 4)

let make_prime521_plus_1_div_4 n =    //0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
    [@inline_let] let n0 = u64 0x0 in
    [@inline_let] let n1 = u64 0x0 in
    [@inline_let] let n2 = u64 0x0 in
    [@inline_let] let n3 = u64 0x0 in
    [@inline_let] let n4 = u64 0x0 in
    [@inline_let] let n5 = u64 0x0 in
    [@inline_let] let n6 = u64 0x0 in
    [@inline_let] let n7 = u64 0x0 in
    [@inline_let] let n8 = u64 0x80 in
    assert_norm (v n0 + v n1 * pow2 64 + v n2 * pow2 128 + v n3 * pow2 192 +
                 v n4 * pow2 256 + v n5 * pow2 320 + v n6 * pow2 384 + v n7 * pow2 448 + v n8 * pow2 512 = (Spec.P521.p521_prime + 1)/4);
    bn_make_u64_9 n n0 n1 n2 n3 n4 n5 n6 n7 n8

[@CInline]
val p521_fsqrt: res:felem -> a:felem -> Stack unit
    (requires fun h ->
      live h a /\ live h res /\ eq_or_disjoint a res /\
      as_nat h a < S.prime)
    (ensures fun h0 _ h1 -> modifies (loc res) h0 h1 /\
      as_nat h1 res < S.prime /\
      fmont_as_nat h1 res = S.fsqrt (fmont_as_nat h0 a))

[@CInline]
let p521_fsqrt res a =
  push_frame ();
  let b = create 9ul (u64 0) in
  make_prime521_plus_1_div_4 b;
  let tmp = create 9ul (u64 0) in
  copy tmp a;
  fexp_vartime res tmp b;
  admit();
  pop_frame ()

