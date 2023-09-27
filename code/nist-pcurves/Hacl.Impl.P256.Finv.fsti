module Hacl.Impl.P256.Finv

open FStar.Mul
open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer

open Hacl.Impl.P256.Bignum
open Hacl.Impl.P256.Field

module S = Spec.P256

#set-options "--z3rlimit 30 --fuel 0 --ifuel 0"

val finv: res:felem -> a:felem -> Stack unit
  (requires fun h ->
    live h a /\ live h res /\ eq_or_disjoint a res /\
    as_nat h a < S.prime)
  (ensures fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    as_nat h1 res < S.prime /\
    fmont_as_nat h1 res = S.finv (fmont_as_nat h0 a))


val fsqrt: res:felem -> a:felem -> Stack unit
  (requires fun h ->
    live h a /\ live h res /\ eq_or_disjoint a res /\
    as_nat h a < S.prime)
  (ensures fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    as_nat h1 res < S.prime /\
    fmont_as_nat h1 res = S.fsqrt (fmont_as_nat h0 a))
