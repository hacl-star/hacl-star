module Hacl.Impl.PCurves.Finv

open FStar.Mul
open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer

open Hacl.Impl.PCurves.Bignum
open Hacl.Impl.PCurves.Field

module LSeq = Lib.Sequence
module BD = Hacl.Spec.Bignum.Definitions
module SM = Hacl.Spec.PCurves.Montgomery
module SE = Spec.Exponentiation
module BE = Hacl.Impl.Exponentiation
module SI = Hacl.Spec.PCurves.Finv
module S = Spec.PCurves
module CC = Hacl.Impl.PCurves.Constants

unfold
let linv_ctx (a:LSeq.lseq uint64 0) : Type0 = True

[@(strict_on_arguments [0])]
unfold
let f_linv {| cp:S.curve_params |} (a:LSeq.lseq uint64 (v cp.bn_limbs)) : Type0 =
  BD.bn_v a < S.prime

[@(strict_on_arguments [0])]
unfold
let f_refl {| cp:S.curve_params |} (a:LSeq.lseq uint64 (v cp.bn_limbs){f_linv a}) : GTot S.felem =
  SM.from_mont (BD.bn_v a)


[@(strict_on_arguments [0])]
inline_for_extraction noextract
let mk_to_pcurve_prime_comm_monoid {| cp:S.curve_params |} : BE.to_comm_monoid U64 cp.bn_limbs 0ul = {
  BE.a_spec = S.felem;
  BE.comm_monoid = SI.nat_mod_comm_monoid;
  BE.linv_ctx = linv_ctx;
  BE.linv = f_linv;
  BE.refl = f_refl;
}

#reset-options "--z3rlimit 50 --fuel 0 --ifuel 0"

[@(strict_on_arguments [0;1])]
inline_for_extraction noextract
val one_mod {| cp:S.curve_params |} {| CC.curve_constants |} : BE.lone_st U64 cp.bn_limbs 0ul mk_to_pcurve_prime_comm_monoid

let one_mod {| cp:S.curve_params |} {| cc:CC.curve_constants |} ctx one = cc.make_fone one


[@(strict_on_arguments [0;1;2;3])]
inline_for_extraction noextract
val mul_mod {| cp:S.curve_params |} {| CC.curve_constants |} {| bn_ops |} {| f:field_ops |} : BE.lmul_st U64 cp.bn_limbs 0ul mk_to_pcurve_prime_comm_monoid
let mul_mod {| cp:S.curve_params |} {| CC.curve_constants |} {| bn_ops |} {| f:field_ops |} ctx x y xy = f.fmul xy x y


[@(strict_on_arguments [0;1;2;3])]
inline_for_extraction noextract
val sqr_mod {| cp:S.curve_params |} {| CC.curve_constants |} {| bn_ops |} {| f:field_ops |} : BE.lsqr_st U64 cp.bn_limbs 0ul mk_to_pcurve_prime_comm_monoid
let sqr_mod {| cp:S.curve_params |} {| CC.curve_constants |} {| bn_ops |} {| f:field_ops |} ctx x xx = f.fsqr xx x


[@(strict_on_arguments [0;1;2;3])]
inline_for_extraction noextract
let mk_pcurve_prime_concrete_ops {| cp:S.curve_params |} {| CC.curve_constants |} {| bn_ops |} {| f:field_ops |} : BE.concrete_ops U64 cp.bn_limbs 0ul = {
  BE.to = mk_to_pcurve_prime_comm_monoid;
  BE.lone = one_mod;
  BE.lmul = mul_mod;
  BE.lsqr = sqr_mod;
}


[@(strict_on_arguments [0;1;2;3])]
inline_for_extraction noextract
val fsquare_times_in_place {| cp:S.curve_params |} {| CC.curve_constants |} {| bn_ops |} {| f:field_ops |} (out:felem) (b:size_t) : Stack unit
  (requires fun h ->
    live h out /\ as_nat h out < S.prime)
  (ensures  fun h0 _ h1 -> modifies (loc out) h0 h1 /\
    as_nat h1 out < S.prime /\
    CC.fmont_as_nat h1 out == SI.fsquare_times (CC.fmont_as_nat h0 out) (v b))

let fsquare_times_in_place {| cp:S.curve_params |} {| CC.curve_constants |} {| bn_ops |} {| f:field_ops |} out b =
  let h0 = ST.get () in
  SE.exp_pow2_lemma SI.mk_nat_mod_concrete_ops (CC.fmont_as_nat h0 out) (v b);
  BE.lexp_pow2_in_place cp.bn_limbs 0ul mk_pcurve_prime_concrete_ops (null uint64) out b


[@(strict_on_arguments [0;1;2;3])]
inline_for_extraction noextract
val fsquare_times {| cp:S.curve_params |} {| CC.curve_constants |} {| bn_ops |} {| f:field_ops |} (out a:felem) (b:size_t) : Stack unit
  (requires fun h ->
    live h out /\ live h a /\ disjoint out a /\
    as_nat h a < S.prime)
  (ensures  fun h0 _ h1 -> modifies (loc out) h0 h1 /\
    as_nat h1 out < S.prime /\
    CC.fmont_as_nat h1 out == SI.fsquare_times (CC.fmont_as_nat h0 a) (v b))

let fsquare_times {| cp:S.curve_params |} {| CC.curve_constants |} {| bn_ops |} {| f:field_ops |} out a b =
  let h0 = ST.get () in
  SE.exp_pow2_lemma SI.mk_nat_mod_concrete_ops (CC.fmont_as_nat h0 a) (v b);
  BE.lexp_pow2 cp.bn_limbs 0ul mk_pcurve_prime_concrete_ops (null uint64) a b out
