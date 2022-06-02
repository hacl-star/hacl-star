module Hacl.Impl.EC.NIST.PointDouble

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Hacl.Impl.EC.Arithmetics

open Lib.Buffer

open Hacl.EC.Lemmas
open Spec.ECC
open Hacl.Spec.EC.Definition
open Hacl.Spec.MontgomeryMultiplication
open Hacl.Impl.EC.LowLevel
open Hacl.Impl.EC.MontgomeryMultiplication

open Hacl.Impl.EC.Math 

open FStar.Tactics 
open FStar.Tactics.Canon

open FStar.Math.Lemmas

friend Hacl.Spec.MontgomeryMultiplication
open FStar.Mul

open Hacl.Impl.P.PointDouble.Aux


#set-options "--z3rlimit 300 --ifuel 0 --fuel 0" 

inline_for_extraction noextract
val point_double_a_b_g: #c: curve 
  -> p: point c 
  -> alpha: felem c 
  -> beta: felem c 
  -> gamma: felem c
  -> delta: felem c 
  -> tempBuffer: lbuffer uint64 (getCoordinateLenU64 c *! 3ul) -> 
  Stack unit
  (requires fun h -> 
    live h p /\ live h alpha /\ live h beta /\ live h gamma /\ live h delta /\ live h tempBuffer /\ 
    LowStar.Monotonic.Buffer.all_disjoint [loc p; loc alpha; loc beta; loc gamma; loc delta; loc tempBuffer] /\
    point_eval c h p
  )
    (ensures fun h0 _ h1 -> modifies (loc alpha |+| loc beta |+| loc gamma |+| loc delta |+| loc tempBuffer) h0 h1 /\ (
    let len = getCoordinateLenU64 c in 
    let prime = getPrime c in 
	
    let x = fromDomain #c (point_x_as_nat c h0 p) in 
    let y = fromDomain #c (point_y_as_nat c h0 p) in 
    let z = fromDomain #c (point_z_as_nat c h0 p) in 
	
    as_nat c h1 delta = toDomain #c (z * z % prime) /\
    as_nat c h1 gamma = toDomain #c (y * y % prime) /\
    as_nat c h1 beta = toDomain #c (x * fromDomain #c (as_nat c h1 gamma) % prime) /\
    as_nat c h1 alpha = toDomain #c (3 * (x - fromDomain #c (as_nat c h1 delta)) * (x + fromDomain #c (as_nat c h1 delta)) % prime)
      )
    )


let point_double_a_b_g #c p alpha beta gamma delta tempBuffer = 
  let coordinateLen = getCoordinateLenU64 c in 
  
  let pX = sub p (size 0) coordinateLen in 
  let pY = sub p (coordinateLen) (coordinateLen) in 
  let pZ = sub p (size 2 *! coordinateLen) coordinateLen in 

  let a0 = sub tempBuffer (size 0) (coordinateLen) in 
  let a1 = sub tempBuffer (coordinateLen) (coordinateLen) in 
  let alpha0 = sub tempBuffer (size 2 *! coordinateLen) (coordinateLen) in 

  montgomery_square_buffer_dh pZ delta; (* delta = z * z*)
  montgomery_square_buffer_dh pY gamma; (* gamma = y * y *)
  montgomery_multiplication_buffer_dh pX gamma beta; (* beta = x * gamma *)
  
  let h0 = ST.get() in 

  felem_sub pX delta a0; (* a0 = x - delta *)
  felem_add pX delta a1; (* a1 = x + delta *)

  montgomery_multiplication_buffer_dh #c a0 a1 alpha0; (* alpha = (x - delta) * (x + delta) *)
  multByThree alpha0 alpha;

    let prime = getPrime c in 
    let open FStar.Tactics.Canon in 
    let xD = fromDomain #c (as_nat c h0 pX) in 
    let dlt = fromDomain #c (as_nat c h0 delta) in 

    calc (==) 
    {
      (3 * (((xD - dlt) % prime) *  ((xD + dlt) % prime) % prime) % prime);
   
      (==) {lemma_mod_mul_distr_l (xD - dlt) ((xD + dlt) % prime) prime; lemma_mod_mul_distr_r (xD - dlt) (xD + dlt) prime}
      
      (3 * ((xD - dlt) *  (xD + dlt) % prime) % prime);
    
    (==) {lemma_mod_mul_distr_r 3 ((xD - dlt) * (xD + dlt)) prime}
    
      (3 * ((xD - dlt) * (xD + dlt)) % prime);
    
    (==) {lemma_point_abd xD dlt}
    
      (3 * (xD - dlt) * (xD + dlt)) % prime;
  }


#reset-options "--z3rlimit 400 --ifuel 0 --fuel 0" 


val lemma_pd_to_spec: #c: curve -> x: nat -> y: nat -> z: nat -> x3: nat -> y3: nat -> z3: nat -> 
  Lemma
  (requires (  
    let prime = getPrime c in 
    let xD, yD, zD = fromDomain #c x, fromDomain #c y, fromDomain #c z in 
    let alpha = 3 * (xD - zD * zD) * (xD + zD * zD) in 
    
    x3 == toDomain #c ((alpha * alpha - 8 * (xD * (yD * yD))) % prime) /\
    y3 == toDomain #c ((alpha * (4 * xD * (yD * yD) - fromDomain #c x3) - 8 * (yD * yD) * (yD * yD)) % prime) /\
    z3 = toDomain #c (((yD + zD) * (yD + zD) - zD * zD - yD * yD) % prime)))
 (ensures (
   let xD, yD, zD = fromDomain #c x, fromDomain #c y, fromDomain #c z in 
   let x3D, y3D, z3D = fromDomain #c x3, fromDomain #c y3, fromDomain #c z3 in 
   let xN, yN, zN = _point_double #c (xD, yD, zD) in 
   x3D == xN /\ y3D == yN /\ z3D == zN))

let lemma_pd_to_spec #c x y z x3 y3 z3 = ()


let point_double #c p result tempBuffer = 
  let len = getCoordinateLenU64 c in 

  let pX = sub p (size 0) len in 
  let pY = sub p len len in 
  let pZ = sub p (size 2 *! len) len in 

  let x3 = sub result (size 0) len in 
  let y3 = sub result len len in 
  let z3 = sub result (size 2 *! len) len in 
  
  let delta = sub tempBuffer (size 0) len in 
  let gamma = sub tempBuffer len len in 
  let beta = sub tempBuffer (size 2 *! len) len in 
  let alpha = sub tempBuffer (size 3 *! len) len in 
  let fourBeta = sub tempBuffer (size 4 *! len) len in 
  let eightBeta = sub tempBuffer (size 5 *! len) len in 
  let eightGamma = sub tempBuffer (size 6 *! len) len in 

  let tmp = sub tempBuffer (7ul *! len) (3ul *! len) in 
    let h0 = ST.get() in 

    point_double_a_b_g #c p alpha beta gamma delta tmp;  
    Hacl.Impl.EC.General.PointDouble.point_double_x3 #c x3 alpha fourBeta beta eightBeta; 
    Hacl.Impl.EC.General.PointDouble.point_double_z3 #c z3 pY pZ gamma delta;
    Hacl.Impl.EC.General.PointDouble.point_double_y3 #c y3 x3 alpha gamma eightGamma fourBeta;

  let h1 = ST.get() in

  let x = fromDomain #c (point_x_as_nat c h0 p) in 
  let y = fromDomain #c (point_y_as_nat c h0 p) in 
  let z = fromDomain #c (point_z_as_nat c h0 p) in 

  lemma_x3 #c x y z;
  lemma_z3 #c x y z; 
  lemma_y3 #c x y z (fromDomain #c (as_nat c h1 x3));

  lemma_pd_to_spec #c (point_x_as_nat c h0 p) (point_y_as_nat c h0 p) (point_z_as_nat c h0 p)
  (point_x_as_nat c h1 result) (point_y_as_nat c h1 result) (point_z_as_nat c h1 result)
