module Hacl.Impl.P256.Arithmetics

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer

(* open Spec.P256.Lemmas *)
open Hacl.Spec.P256.Definition

open Hacl.Impl.P256.LowLevel 
open Hacl.Impl.P256.LowLevel.PrimeSpecific
open Hacl.Impl.P256.MontgomeryMultiplication
open Spec.P256

open Hacl.Spec.P256.MontgomeryMultiplication

open FStar.Math.Lemmas

open FStar.Mul

val cube: a: felem -> result: felem -> Stack unit
  (requires fun h -> live h a /\ live h result /\ disjoint a result /\ as_nat h a < prime256)
  (ensures fun h0 _ h1 -> modifies (loc result) h0 h1 /\ 
    as_nat h1 result < prime256 /\
    as_nat h1 result = toDomain_ (fromDomain_ (as_nat h0 a) * fromDomain_ (as_nat h0 a) * fromDomain_ (as_nat h0 a) % prime256) /\ 
    as_nat h1 result = toDomain_ (fromDomain_ (as_nat h0 a) * fromDomain_ (as_nat h0 a) * fromDomain_ (as_nat h0 a)))

inline_for_extraction noextract
val quatre: a: felem -> result: felem -> Stack unit
  (requires fun h -> live h a /\ live h result /\ disjoint a result /\ as_nat h a < prime256)
  (ensures fun h0 _ h1 -> modifies (loc result) h0 h1 /\ 
    as_nat h1 result = toDomain_ (fromDomain_ (as_nat h0 a) * fromDomain_ (as_nat h0 a) * fromDomain_ (as_nat h0 a) * fromDomain_ (as_nat h0 a) % prime256) /\ 
    as_nat h1 result = toDomain_ (fromDomain_ (as_nat h0 a) * fromDomain_ (as_nat h0 a) * fromDomain_ (as_nat h0 a) * fromDomain_ (as_nat h0 a)))

val multByTwo: a: felem -> result: felem -> Stack unit 
  (requires fun h -> live h a /\ live h result /\ eq_or_disjoint a result /\ as_nat h a < prime256 )
  (ensures fun h0 _ h1 -> modifies (loc result) h0 h1 /\ 
    as_nat h1 result == toDomain_ (2 * fromDomain_ (as_nat h0 a) % prime256) /\ 
    as_nat h1 result == toDomain_ (2 * fromDomain_ (as_nat h0 a)) /\ 
    as_nat h1 result < prime256)

val multByThree: a: felem -> result: felem -> Stack unit 
  (requires fun h -> live h a /\ live h result /\ disjoint a result /\ as_nat h a < prime256 )
  (ensures fun h0 _ h1 -> modifies (loc result) h0 h1 /\ as_nat h1 result < prime256 /\ 
    as_nat h1 result == toDomain_ (3 * fromDomain_ (as_nat h0 a) % prime256) /\ 
    as_nat h1 result == toDomain_ (3 * fromDomain_ (as_nat h0 a))
  )


val multByFour: a: felem -> result: felem -> Stack unit 
  (requires fun h -> live h a /\ live h result /\ eq_or_disjoint a result /\ as_nat h a < prime256 )
  (ensures fun h0 _ h1 -> modifies (loc result) h0 h1 /\ as_nat h1 result < prime256 /\ 
    as_nat h1 result == toDomain_ (4 * fromDomain_ (as_nat h0 a) % prime256) /\ 
    as_nat h1 result == toDomain_ (4 * fromDomain_ (as_nat h0 a))
)

val multByEight: a: felem -> result: felem -> Stack unit 
  (requires fun h -> live h a /\ live h result /\ disjoint a result /\ as_nat h a < prime256 )
  (ensures fun h0 _ h1 -> modifies (loc result) h0 h1 /\ as_nat h1 result < prime256 /\ 
    as_nat h1 result == toDomain_ (8 * fromDomain_ (as_nat h0 a) % prime256) /\ 
    as_nat h1 result == toDomain_ (8 * fromDomain_ (as_nat h0 a))
)

val multByMinusThree: a: felem -> result: felem -> Stack unit 
  (requires fun h -> live h a /\ live h result /\ disjoint a result /\ as_nat h a < prime256 )
  (ensures fun h0 _ h1 -> modifies (loc result) h0 h1 /\ 
    as_nat h1 result < prime256 /\ 
    as_nat h1 result == toDomain_ ((-3) * fromDomain_ (as_nat h0 a) % prime256) /\
    as_nat h1 result == toDomain_ ((-3) * fromDomain_ (as_nat h0 a)))
