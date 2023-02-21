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
val toDomain: value: felem -> result: felem ->  Stack unit
  (requires fun h ->  as_nat h value < prime /\ live h value /\live h result /\ eq_or_disjoint value result)
  (ensures fun h0 _ h1 -> modifies (loc result) h0 h1 /\ as_nat h1 result = toDomain_ (as_nat h0 value))


// TODO: mv to Hacl.Impl.P256.Field
inline_for_extraction noextract
val fromDomain: f: felem-> result: felem-> Stack unit
  (requires fun h -> live h f /\ live h result /\ as_nat h f < prime)
  (ensures fun h0 _ h1 -> modifies (loc result) h0 h1 /\
    as_nat h1 result = (as_nat h0 f * modp_inv2(pow2 256)) % prime /\
    as_nat h1 result = fromDomain_ (as_nat h0 f))
