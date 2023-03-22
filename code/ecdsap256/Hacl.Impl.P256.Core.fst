module Hacl.Impl.P256.Core

open FStar.Mul
open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer

open Hacl.Impl.P256.Bignum
open Hacl.Impl.P256.SolinasReduction

module S = Spec.P256
module SM = Hacl.Spec.P256.MontgomeryMultiplication

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

// TODO: mv to Hacl.Impl.P256.Field
inline_for_extraction noextract
val toDomain: f:felem -> res:felem -> Stack unit
  (requires fun h ->
    live h f /\live h res /\ eq_or_disjoint f res /\
    as_nat h f < S.prime)
  (ensures fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    as_nat h1 res = SM.to_mont (as_nat h0 f))

let toDomain f res =
  push_frame ();
  let tmp = create_widefelem () in
  bn_lshift256 f tmp;
  solinas_reduction_impl tmp res;
  pop_frame()
