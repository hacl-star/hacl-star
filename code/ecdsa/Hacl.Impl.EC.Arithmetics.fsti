module Hacl.Impl.EC.Arithmetics

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer

(* open Spec.ECC.Lemmas *)
open Hacl.Spec.EC.Definition

open Hacl.Impl.EC.MontgomeryMultiplication
open Spec.ECC
open Spec.ECC.Curves

open Hacl.Spec.MontgomeryMultiplication

open FStar.Math.Lemmas

open FStar.Mul


val cube: #c: curve -> a: felem c -> result: felem c -> Stack unit
  (requires fun h -> live h a /\ live h result /\ disjoint a result /\ as_nat c h a < getPrime c)
  (ensures fun h0 _ h1 -> modifies (loc result) h0 h1 /\ 
    as_nat c h1 result < getPrime c /\
    as_nat c h1 result = toDomain_ #c (fromDomain_ #c (as_nat c h0 a) * fromDomain_ #c (as_nat c h0 a) * fromDomain_ #c (as_nat c h0 a) % getPrime c) /\ 
    as_nat c h1 result = toDomain_ #c (fromDomain_ #c (as_nat c h0 a) * fromDomain_ #c (as_nat c h0 a) * fromDomain_ #c (as_nat c h0 a)))


val quatre: #c: curve -> a: felem c -> result: felem c -> Stack unit
  (requires fun h -> live h a /\ live h result /\ disjoint a result /\ as_nat c h a < getPrime c)
  (ensures fun h0 _ h1 -> modifies (loc result) h0 h1 /\ 
    as_nat c h1 result = toDomain_ #c (fromDomain_ #c (as_nat c h0 a) * fromDomain_ #c (as_nat c h0 a) * fromDomain_ #c (as_nat c h0 a) * fromDomain_ #c (as_nat c h0 a) % getPrime c) /\ 
    as_nat c h1 result = toDomain_ #c (fromDomain_ #c (as_nat c h0 a) * fromDomain_ #c (as_nat c h0 a) * fromDomain_ #c (as_nat c h0 a) * fromDomain_ #c (as_nat c h0 a)))


val multByTwo: #c: curve -> a: felem c -> result: felem c -> Stack unit 
  (requires fun h -> live h a /\ live h result /\ eq_or_disjoint a result /\ as_nat c h a < getPrime c)
  (ensures fun h0 _ h1 -> modifies (loc result) h0 h1 /\ 
    as_nat c h1 result == toDomain_ #c (2 * fromDomain_ #c (as_nat c h0 a) % getPrime c) /\ 
    as_nat c h1 result == toDomain_ #c (2 * fromDomain_ #c (as_nat c h0 a)) /\ 
    as_nat c h1 result < getPrime c)


val multByThree: #c: curve -> a: felem c -> result: felem c -> Stack unit 
  (requires fun h -> live h a /\ live h result /\ disjoint a result /\ as_nat c h a < getPrime c)
  (ensures fun h0 _ h1 -> modifies (loc result) h0 h1 /\ as_nat c h1 result < getPrime c /\ 
    as_nat c h1 result == toDomain_ #c (3 * fromDomain_ #c (as_nat c h0 a) % getPrime c) /\ 
    as_nat c h1 result == toDomain_ #c (3 * fromDomain_ #c (as_nat c h0 a))
  )


val multByFour: #c: curve -> a: felem c -> result: felem c -> Stack unit 
  (requires fun h -> live h a /\ live h result /\ eq_or_disjoint a result /\ as_nat c h a < getPrime c)
  (ensures fun h0 _ h1 -> modifies (loc result) h0 h1 /\ as_nat c h1 result < getPrime c /\ 
    as_nat c h1 result == toDomain_ #c (4 * fromDomain_ #c (as_nat c h0 a) % getPrime c) /\ 
    as_nat c h1 result == toDomain_ #c (4 * fromDomain_ #c (as_nat c h0 a))
)


val multByEight: #c: curve -> a: felem c -> result: felem c -> Stack unit 
  (requires fun h -> live h a /\ live h result /\ disjoint a result /\ as_nat c h a < getPrime c)
  (ensures fun h0 _ h1 -> modifies (loc result) h0 h1 /\ as_nat c h1 result < getPrime c /\ 
    as_nat c h1 result == toDomain_ #c (8 * fromDomain_ #c (as_nat c h0 a) % getPrime c) /\ 
    as_nat c h1 result == toDomain_ #c (8 * fromDomain_ #c (as_nat c h0 a))
)


val multByMinusThree: #c: curve -> a: felem c -> result: felem c -> Stack unit 
  (requires fun h -> live h a /\ live h result /\ disjoint a result /\ as_nat c h a < getPrime c)
  (ensures fun h0 _ h1 -> modifies (loc result) h0 h1 /\ 
    as_nat c h1 result < getPrime c /\ 
    as_nat c h1 result == toDomain_ #c ((-3) * fromDomain_ #c (as_nat c h0 a) % getPrime c) /\
    as_nat c h1 result == toDomain_ #c ((-3) * fromDomain_ #c (as_nat c h0 a)))
