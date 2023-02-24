module Hacl.Impl.P256.PointDouble

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer

open Hacl.Spec.P256.MontgomeryMultiplication
open Hacl.Spec.P256.Felem
open Hacl.Impl.P256.Point

module S = Spec.P256

#set-options "--z3rlimit 30 --fuel 0 --ifuel 0"

val point_double: p:point -> result:point -> tempBuffer:lbuffer uint64 (size 88) -> Stack unit
  (requires fun h -> live h p /\ live h tempBuffer /\ live h result /\
    disjoint p tempBuffer /\ disjoint result tempBuffer /\
    eq_or_disjoint p result /\
    as_nat h (gsub p (size 8) (size 4)) < S.prime /\
    as_nat h (gsub p (size 0) (size 4)) < S.prime /\
    as_nat h (gsub p (size 4) (size 4)) < S.prime)
  (ensures fun h0 _ h1 -> modifies (loc tempBuffer |+| loc result)  h0 h1 /\
    as_nat h1 (gsub result (size 8) (size 4)) < S.prime /\
    as_nat h1 (gsub result (size 0) (size 4)) < S.prime /\
    as_nat h1 (gsub result (size 4) (size 4)) < S.prime /\
    (
      let x, y, z = gsub p (size 0) (size 4),  gsub p (size 4) (size 4), gsub p (size 8) (size 4) in
      let x3, y3, z3 = gsub result (size 0) (size 4), gsub result (size 4) (size 4), gsub result (size 8) (size 4) in

      let xD, yD, zD = fromDomain_ (as_nat h0 x), fromDomain_ (as_nat h0 y), fromDomain_ (as_nat h0 z) in
      let x3D, y3D, z3D = fromDomain_ (as_nat h1 x3), fromDomain_ (as_nat h1 y3), fromDomain_ (as_nat h1 z3) in

      let xN, yN, zN = S.point_double (xD, yD, zD) in
      x3D == xN /\ y3D == yN /\ z3D == zN
  )
)
