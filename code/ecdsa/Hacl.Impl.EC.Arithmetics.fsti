module Hacl.Impl.EC.Arithmetics

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer

open Hacl.Spec.EC.Definition
open Spec.ECC
open Spec.ECC.Curves
open Hacl.Spec.MontgomeryMultiplication

open FStar.Mul


let fromDomain #c = fromDomain_ #c #DH
let toDomain #c = toDomain_ #c #DH


val cube: #c: curve -> a: felem c -> result: felem c -> Stack unit
  (requires fun h -> live h a /\ live h result /\ disjoint a result /\ as_nat c h a < getPrime c)
  (ensures fun h0 _ h1 -> modifies (loc result) h0 h1 /\ 
    as_nat c h1 result < getPrime c /\
    as_nat c h1 result = toDomain #c (fromDomain #c (as_nat c h0 a) * fromDomain #c (as_nat c h0 a) * fromDomain #c (as_nat c h0 a) % getPrime c) /\ 
    as_nat c h1 result = toDomain #c (fromDomain #c (as_nat c h0 a) * fromDomain #c (as_nat c h0 a) * fromDomain #c (as_nat c h0 a)))


val quatre: #c: curve -> a: felem c -> result: felem c -> Stack unit
  (requires fun h -> live h a /\ live h result /\ disjoint a result /\ as_nat c h a < getPrime c)
  (ensures fun h0 _ h1 -> modifies (loc result) h0 h1 /\ 
    as_nat c h1 result = toDomain #c (fromDomain #c (as_nat c h0 a) * fromDomain #c (as_nat c h0 a) * fromDomain #c (as_nat c h0 a) * fromDomain #c (as_nat c h0 a) % getPrime c) /\ 
    as_nat c h1 result = toDomain #c (fromDomain #c (as_nat c h0 a) * fromDomain #c (as_nat c h0 a) * fromDomain #c (as_nat c h0 a) * fromDomain #c (as_nat c h0 a)))


val multByTwo: #c: curve -> a: felem c -> result: felem c -> Stack unit 
  (requires fun h -> live h a /\ live h result /\ eq_or_disjoint a result /\ as_nat c h a < getPrime c)
  (ensures fun h0 _ h1 -> modifies (loc result) h0 h1 /\ 
    as_nat c h1 result == toDomain #c (2 * fromDomain #c (as_nat c h0 a) % getPrime c) /\ 
    as_nat c h1 result == toDomain #c (2 * fromDomain #c (as_nat c h0 a)) /\ 
    as_nat c h1 result < getPrime c)


val multByThree: #c: curve -> a: felem c -> result: felem c -> Stack unit 
  (requires fun h -> live h a /\ live h result /\ disjoint a result /\ as_nat c h a < getPrime c)
  (ensures fun h0 _ h1 -> modifies (loc result) h0 h1 /\ as_nat c h1 result < getPrime c /\ 
    as_nat c h1 result == toDomain #c (3 * fromDomain #c (as_nat c h0 a) % getPrime c) /\ 
    as_nat c h1 result == toDomain #c (3 * fromDomain #c (as_nat c h0 a)))


val multByFour: #c: curve -> a: felem c -> result: felem c -> Stack unit 
  (requires fun h -> live h a /\ live h result /\ eq_or_disjoint a result /\ as_nat c h a < getPrime c)
  (ensures fun h0 _ h1 -> modifies (loc result) h0 h1 /\ as_nat c h1 result < getPrime c /\ 
    as_nat c h1 result == toDomain #c (4 * fromDomain #c (as_nat c h0 a) % getPrime c) /\ 
    as_nat c h1 result == toDomain #c (4 * fromDomain #c (as_nat c h0 a)))


val multByEight: #c: curve -> a: felem c -> result: felem c -> Stack unit 
  (requires fun h -> live h a /\ live h result /\ disjoint a result /\ as_nat c h a < getPrime c)
  (ensures fun h0 _ h1 -> modifies (loc result) h0 h1 /\ as_nat c h1 result < getPrime c /\ 
    as_nat c h1 result == toDomain #c (8 * fromDomain #c (as_nat c h0 a) % getPrime c) /\ 
    as_nat c h1 result == toDomain #c (8 * fromDomain #c (as_nat c h0 a)))


val multByMinusThree: #c: curve -> a: felem c -> result: felem c -> Stack unit 
  (requires fun h -> live h a /\ live h result /\ disjoint a result /\ as_nat c h a < getPrime c)
  (ensures fun h0 _ h1 -> modifies (loc result) h0 h1 /\ 
    as_nat c h1 result < getPrime c /\ 
    as_nat c h1 result == toDomain #c ((-3) * fromDomain #c (as_nat c h0 a) % getPrime c) /\
    as_nat c h1 result == toDomain #c ((-3) * fromDomain #c (as_nat c h0 a)))
