module Hacl.Impl.P256.Finv

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

val finv: a:felem -> res:felem -> tmp:lbuffer uint64 (size 20) -> Stack unit
  (requires fun h ->
    live h a /\ live h tmp /\ live h res /\
    disjoint tmp res /\ disjoint a tmp /\
    as_nat h a < prime256)
  (ensures fun h0 _ h1 -> modifies (loc res |+| loc tmp) h0 h1 /\
    as_nat h1 res = toDomain_ ((pow (fromDomain_ (as_nat h0 a)) (prime256 - 2)) % prime256))


val fsqrt: a:felem -> res:felem -> Stack unit
  (requires fun h -> live h a /\ live h res /\ as_nat h a < prime)
  (ensures fun h0 _ h1 -> modifies (loc a |+| loc res) h0 h1 /\
    as_nat h1 res < prime /\
    fromDomain_ (as_nat h1 res) = sq_root_spec (fromDomain_ (as_nat h0 a)) /\
    fromDomain_ (as_nat h1 res) = pow (fromDomain_ (as_nat h0 a)) ((prime256 + 1) / 4) % prime256)
