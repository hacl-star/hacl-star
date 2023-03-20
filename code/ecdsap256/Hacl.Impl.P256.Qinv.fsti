module Hacl.Impl.P256.Qinv

open FStar.Mul
open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer

open Hacl.Spec.P256.Bignum
open Hacl.Impl.P256.Scalar

module S = Spec.P256

#set-options "--z3rlimit 30 --fuel 0 --ifuel 0"

val qinv: res:felem -> a:felem -> Stack unit
  (requires fun h ->
    live h a /\ live h res /\ eq_or_disjoint a res /\
    as_nat h a < S.order)
  (ensures fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    as_nat h1 res < S.order /\
    qmont_as_nat h1 res == S.qinv (qmont_as_nat h0 a))


// TODO: rm
val multPowerPartial: s:felem -> a:felem -> b:felem -> result:felem -> Stack unit
  (requires fun h ->
    live h a /\ live h b /\ live h result /\
    as_nat h a < S.order /\ as_nat h b < S.order /\
    fromDomain_ (as_nat h a) == S.qinv (fromDomain_ (fromDomain_ (as_nat h s))))
  (ensures fun h0 _ h1 -> modifies (loc result) h0 h1 /\
    as_nat h1 result = (S.pow (as_nat h0 s) (S.order - 2) * (as_nat h0 b)) % S.order)
