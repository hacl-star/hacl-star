module Hacl.Impl.P256.Finv

open FStar.Mul
open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer

open Spec.P256
open Spec.P256.MontgomeryMultiplication
open Hacl.Spec.P256.Felem

module M = Lib.NatMod
module S = Spec.P256.Constants

#set-options "--z3rlimit 30 --fuel 0 --ifuel 0"

val finv: a:felem -> res:felem -> Stack unit
  (requires fun h ->
    live h a /\ live h res /\ disjoint a res /\
    as_nat h a < S.prime256)
  (ensures fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    as_nat h1 res < S.prime256 /\
    as_nat h1 res = toDomain_ (S.finv (fromDomain_ (as_nat h0 a))))


val fsqrt: a:felem -> res:felem -> Stack unit
  (requires fun h -> live h a /\ live h res /\ as_nat h a < S.prime256)
  (ensures fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    as_nat h1 res < S.prime256 /\
    as_nat h1 res = toDomain_ (S.fsqrt (fromDomain_ (as_nat h0 a))))
