module Hacl.Impl.P256.Finv // before: Hacl.Impl.P256.MM.Exponent

open FStar.Mul
open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer


open Spec.P256
open Spec.P256.Constants
open Spec.P256.Lemmas
open Spec.P256.MontgomeryMultiplication

open Hacl.Spec.P256.Felem

#set-options "--z3rlimit 30 --fuel 0 --ifuel 0"

val exponent: a:felem -> result:felem -> tempBuffer:lbuffer uint64 (size 20) -> Stack unit
  (requires fun h ->
    live h a /\ live h tempBuffer /\ live h result /\
    disjoint tempBuffer result /\ disjoint a tempBuffer /\
    as_nat h a < prime256)
  (ensures fun h0 _ h1 -> modifies (loc result |+| loc tempBuffer) h0 h1 /\
    as_nat h1 result = toDomain_ ((pow (fromDomain_ (as_nat h0 a)) (prime256 - 2)) % prime256))


val square_root: a:felem -> result:felem -> Stack unit
  (requires fun h -> live h a /\ live h result /\ as_nat h a < prime)
  (ensures fun h0 _ h1 -> modifies (loc a |+| loc result) h0 h1 /\
    as_nat h1 result < prime /\
    fromDomain_ (as_nat h1 result) = sq_root_spec (fromDomain_ (as_nat h0 a)) /\
    fromDomain_ (as_nat h1 result) = pow (fromDomain_ (as_nat h0 a)) ((prime256 + 1) / 4) % prime256)
