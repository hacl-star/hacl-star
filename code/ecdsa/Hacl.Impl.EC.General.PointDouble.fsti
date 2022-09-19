module Hacl.Impl.EC.General.PointDouble

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer

open Spec.ECC
open Spec.ECC.Curves

open Hacl.Impl.EC.LowLevel
open Hacl.Spec.EC.Definition


open Hacl.Spec.MontgomeryMultiplication

open FStar.Mul

#set-options "--z3rlimit 300 --ifuel 0 --fuel 0" 


inline_for_extraction noextract
val point_double_x3: #c: curve -> x3: felem c -> alpha: felem c -> fourBeta: felem c 
  -> beta: felem c -> eightBeta: felem c ->
  Stack unit
  (requires fun h ->
    live h x3 /\ live h alpha /\ live h fourBeta /\ live h beta /\ live h eightBeta /\
    LowStar.Monotonic.Buffer.all_disjoint [loc x3; loc alpha; loc fourBeta; loc beta; loc eightBeta] /\ 
    felem_eval c h alpha /\ felem_eval c h beta)
  (ensures fun h0 _ h1 -> modifies (loc x3 |+| loc fourBeta |+| loc eightBeta) h0 h1 /\ (
    let prime = getPrime c in 
    as_nat c h1 fourBeta = toDomain #c (4 * fromDomain #c (as_nat c h0 beta) % prime) /\
    as_nat c h1 x3 = toDomain #c ((fromDomain #c (as_nat c h0 alpha) * fromDomain #c (as_nat c h0 alpha) - 8 * (fromDomain #c (as_nat c h0 beta))) % prime))) 


inline_for_extraction noextract
val point_double_z3: #c: curve -> z3: felem c -> pY: felem c -> pZ: felem c -> gamma: felem c 
  -> delta: felem c ->
  Stack unit 
  (requires fun h -> live h z3 /\ live h pY /\ live h pZ /\ live h gamma /\ live h delta /\ disjoint pY pZ /\
    eq_or_disjoint pZ z3 /\ disjoint z3 gamma /\ disjoint z3 delta /\ disjoint pY z3 /\
    felem_eval c h gamma /\ felem_eval c h delta /\ felem_eval c h pY /\ felem_eval c h pZ)
  (ensures fun h0 _ h1 -> modifies (loc z3) h0 h1 /\ (
    let prime = getPrime c in 
    let y = fromDomain #c (as_nat c h0 pY) in 
    let z = fromDomain #c (as_nat c h0 pZ) in 
    as_nat c h1 z3 = toDomain #c (((y + z) * (y + z) - fromDomain #c (as_nat c h0 gamma) - fromDomain #c (as_nat c h0 delta)) % prime)))


inline_for_extraction noextract
val point_double_y3: #c: curve -> y3: felem c -> x3: felem c -> alpha: felem c -> gamma: felem c 
  -> eightGamma: felem c -> fourBeta: felem c ->
  Stack unit 
  (requires fun h -> 
    live h y3 /\ live h x3 /\ live h alpha /\ live h gamma /\ live h eightGamma /\ 
    live h fourBeta /\
    LowStar.Monotonic.Buffer.all_disjoint [loc y3; loc x3; loc alpha; loc gamma; loc eightGamma; loc fourBeta] /\
    felem_eval c h x3 /\ felem_eval c h alpha /\ felem_eval c h gamma /\ felem_eval c h fourBeta)
  (ensures fun h0 _ h1 -> modifies (loc y3 |+| loc gamma |+| loc eightGamma) h0 h1 /\ (
    let alphaD = fromDomain #c (as_nat c h0 alpha) in 
    let gammaD = fromDomain #c (as_nat c h0 gamma) in 
    as_nat c h1 y3 == toDomain #c ((alphaD * (fromDomain #c (as_nat c h0 fourBeta) - fromDomain #c (as_nat c h0 x3)) - 8 * gammaD * gammaD) % getPrime c)))


