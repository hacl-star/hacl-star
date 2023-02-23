module Hacl.Impl.P256.Core

open FStar.Mul
open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer

open Spec.P256
open Spec.P256.Lemmas
open Spec.P256.Constants
open Spec.P256.MontgomeryMultiplication

open Hacl.Spec.P256.Felem

#set-options "--z3rlimit 30 --fuel 0 --ifuel 0"

// TODO: mv to Hacl.Impl.P256.Field
inline_for_extraction noextract
val toDomain: f:felem -> res:felem -> Stack unit
  (requires fun h ->
    live h f /\live h res /\ eq_or_disjoint f res /\
    as_nat h f < prime)
  (ensures fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    as_nat h1 res = toDomain_ (as_nat h0 f))


// TODO: mv to Hacl.Impl.P256.Field
inline_for_extraction noextract
val fromDomain: f:felem -> res:felem -> Stack unit
  (requires fun h -> live h f /\ live h res /\ as_nat h f < prime)
  (ensures fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    as_nat h1 res = (as_nat h0 f * modp_inv2 (pow2 256)) % prime /\
    as_nat h1 res = fromDomain_ (as_nat h0 f))
