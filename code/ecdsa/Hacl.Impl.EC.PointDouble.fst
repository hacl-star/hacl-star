module Hacl.Impl.EC.PointDouble

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Hacl.Impl.EC.Arithmetics

open Lib.Buffer

open Hacl.EC.Lemmas
open Hacl.Spec.EC.Definition
open Hacl.Spec.MontgomeryMultiplication
open Hacl.Impl.EC.LowLevel
open Hacl.Impl.EC.MontgomeryMultiplication
open Spec.ECC
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

let point_double_x3 #c x3 alpha fourBeta beta eightBeta  = 
    let h0 = ST.get() in 
  montgomery_square_buffer_dh alpha x3; (* x3 = alpha ** 2 *)
  multByFour beta fourBeta; (*  fourBeta = beta * 4 *)
  multByTwo fourBeta eightBeta; (* eightBeta = beta * 8 *)
  felem_sub x3 eightBeta x3 (* x3 = alpha ** 2 - beta * 8 *);


  let prime = getPrime c in 
  calc(==)
  {
     toDomain #c (((fromDomain #c (as_nat c h0 alpha) * fromDomain #c (as_nat c h0 alpha) % prime) - (2 *  (4 * fromDomain #c (as_nat c h0 beta) % prime) % prime)) % prime);
     
     (==) {lemma_mod_mul_distr_r 2 (4 * fromDomain #c (as_nat c h0 beta)) prime}
  
     toDomain #c (((fromDomain #c (as_nat c h0 alpha) * fromDomain #c (as_nat c h0 alpha) % prime) - (8 * fromDomain #c (as_nat c h0 beta)) % prime) % prime);
     
     (==) {lemma_mod_sub_distr (fromDomain #c (as_nat c h0 alpha) * fromDomain #c (as_nat c h0 alpha) % prime) (8 * fromDomain #c (as_nat c h0 beta)) prime}
     
    toDomain #c (((fromDomain #c (as_nat c h0 alpha) * fromDomain #c (as_nat c h0 alpha) % prime) - (8 * fromDomain #c (as_nat c h0 beta))) % prime);
 
    (==) {lemma_mod_add_distr (- 8 * fromDomain #c (as_nat c h0 beta)) (fromDomain #c (as_nat c h0 alpha) * fromDomain #c (as_nat c h0 alpha)) prime}
      
    toDomain #c ((fromDomain #c (as_nat c h0 alpha) * fromDomain #c (as_nat c h0 alpha) - 8 * fromDomain #c (as_nat c h0 beta)) % prime);
  }

inline_for_extraction noextract
val point_double_z3: #c: curve -> z3: felem c -> pY: felem c -> pZ: felem c -> gamma: felem c 
  -> delta: felem c ->
  Stack unit 
  (requires fun h -> live h z3 /\ live h pY /\ live h pZ /\ live h gamma /\ live h delta /\
    eq_or_disjoint pZ z3 /\ disjoint z3 gamma /\ disjoint z3 delta /\ disjoint pY z3 /\
    felem_eval c h gamma /\ felem_eval c h delta /\ felem_eval c h pY /\ felem_eval c h pZ)
  (ensures fun h0 _ h1 -> modifies (loc z3) h0 h1 /\ (
    let prime = getPrime c in 
    let y = fromDomain #c (as_nat c h0 pY) in 
    let z = fromDomain #c (as_nat c h0 pZ) in 
    as_nat c h1 z3 = toDomain #c (((y + z) * (y + z) - fromDomain #c (as_nat c h0 gamma) - fromDomain #c (as_nat c h0 delta)) % prime)))


let point_double_z3 #c z3 pY pZ gamma delta  = 
    let h0 = ST.get() in 

  felem_add pY pZ z3; (* z3 = py + pz *) 
  montgomery_square_buffer_dh z3 z3; (* z3 = (py + pz) ** 2 *) 
  felem_sub z3 gamma z3; (* z3 =  (py + pz) ** 2 - gamma  *)
  felem_sub z3 delta z3 (* z3 = (py + pz) ** 2 - gamma - delta *);


    let pyD = fromDomain #c (as_nat c h0 pY) in 
    let pzD = fromDomain #c (as_nat c h0 pZ) in 
    
    let prime = getPrime c in 

    calc (==)
    {
      toDomain #c (((((( ((pyD + pzD) % prime) * ((pyD + pzD) % prime) % prime)) - fromDomain #c (as_nat c h0 gamma)) % prime) - fromDomain #c (as_nat c h0 delta)) % prime);
  
    (==) {lemma_mod_mul_distr_l (pyD + pzD) ((pyD + pzD) % prime) prime; 
      lemma_mod_mul_distr_r (pyD + pzD) (pyD + pzD) prime}
    
    toDomain #c ((((((pyD + pzD) * (pyD + pzD) % prime) - fromDomain #c (as_nat c h0 gamma)) % prime) - fromDomain #c (as_nat c h0 delta)) % prime);
    
    (==) {lemma_mod_add_distr (- fromDomain #c (as_nat c h0 gamma)) ((pyD + pzD) * (pyD + pzD)) prime }
    
    toDomain #c (((((pyD + pzD) * (pyD + pzD) - fromDomain #c (as_nat c h0 gamma)) % prime) - fromDomain #c (as_nat c h0 delta)) % prime);
 
    (==) {lemma_mod_add_distr (- fromDomain #c (as_nat c h0 delta)) ((pyD + pzD) * (pyD + pzD) - fromDomain #c (as_nat c h0 gamma)) prime}
    
    toDomain #c (((pyD + pzD) * (pyD + pzD) - fromDomain #c (as_nat c h0 gamma) - fromDomain #c (as_nat c h0 delta)) % prime);
  }

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
    as_nat c h1 y3 == toDomain #c ((alphaD *  (fromDomain #c (as_nat c h0 fourBeta) - fromDomain #c (as_nat c h0 x3)) - 8 * gammaD * gammaD) % getPrime c)))



let point_double_y3 #c y3 x3 alpha gamma eightGamma fourBeta = 
    let h0 = ST.get() in 
  felem_sub fourBeta x3 y3; (* y3 = 4 * beta - x3 *)
  montgomery_multiplication_buffer_dh alpha y3 y3; (* y3 = alpha * (4 * beta - x3) *)
  montgomery_square_buffer_dh gamma gamma; (* gamma = gamma ** 2 *)
  multByEight gamma eightGamma; (* gamma = 8 * gamma ** 2 *)
  felem_sub y3 eightGamma y3; (* y3 = alpha * y3 - 8 * gamma **2 *)


  let alphaD = fromDomain #c (as_nat c h0 alpha) in 
  let gammaD = fromDomain #c (as_nat c h0 gamma) in  

  let open FStar.Tactics.Canon in 

  let prime = getPrime c in 

  calc(==)
  {
     toDomain #c (((fromDomain #c (as_nat c h0 alpha) *  ((fromDomain #c (as_nat c h0 fourBeta) - fromDomain #c (as_nat c h0 x3)) % prime) % prime) - (8 *  (fromDomain #c (as_nat c h0 gamma) * fromDomain #c (as_nat c h0 gamma) % prime) % prime)) % prime);
 
     (==) {lemma_mod_mul_distr_r (fromDomain #c (as_nat c h0 alpha)) (((fromDomain #c (as_nat c h0 fourBeta) - fromDomain #c (as_nat c h0 x3)))) prime}
    
    toDomain #c (((fromDomain #c (as_nat c h0 alpha) *  (fromDomain #c (as_nat c h0 fourBeta) - fromDomain #c (as_nat c h0 x3)) % prime) - (8 *  (fromDomain #c (as_nat c h0 gamma) * fromDomain #c (as_nat c h0 gamma) % prime) % prime)) % prime);
    
    (==) {lemma_mod_mul_distr_r 8 (fromDomain #c (as_nat c h0 gamma) * (fromDomain #c (as_nat c h0 gamma))) prime}
    
    toDomain #c (((alphaD *  (fromDomain #c (as_nat c h0 fourBeta) - fromDomain #c (as_nat c h0 x3)) % prime) - (8 * (gammaD * gammaD) % prime)) % prime);
  
    (==) {lemma_mod_add_distr (-(8 * (gammaD * gammaD) % prime)) (alphaD *  (fromDomain #c (as_nat c h0 fourBeta) - fromDomain #c (as_nat c h0 x3))) prime  }
    
    toDomain #c (((alphaD *  (fromDomain #c (as_nat c h0 fourBeta) - fromDomain #c (as_nat c h0 x3))) - (8 * (gammaD * gammaD) % prime)) % prime);
    
    (==) {lemma_mod_sub_distr (alphaD *  (fromDomain #c (as_nat c h0 fourBeta) - fromDomain #c (as_nat c h0 x3))) (8 * (gammaD * gammaD)) prime}
    
    toDomain #c (((alphaD *  (fromDomain #c (as_nat c h0 fourBeta) - fromDomain #c (as_nat c h0 x3))) - (8 * (gammaD * gammaD))) % prime);
    
    (==) {assert_by_tactic (8 * (gammaD * gammaD) == 8 * gammaD * gammaD) canon}
    
    toDomain #c ((alphaD *  (fromDomain #c (as_nat c h0 fourBeta) - fromDomain #c (as_nat c h0 x3)) - 8 * gammaD * gammaD) % prime);
}


val lemma_pd_to_spec: #c: curve -> x: nat -> y: nat -> z: nat -> x3: nat -> y3: nat -> z3: nat -> Lemma 
  (requires (  
    let prime = getPrime c in 
    let xD, yD, zD = fromDomain #c x, fromDomain #c y, fromDomain #c z in 
    x3 == toDomain #c (((3 * (xD - zD * zD) * (xD + zD * zD)) * (3 * (xD - zD * zD) * (xD + zD * zD)) - 8 * xD * (yD * yD)) % prime) /\
    y3 == toDomain #c ((3 * (xD - zD * zD) * (xD + zD * zD) *  (4 * xD * (yD * yD) - fromDomain #c x3) - 8 * (yD * yD) * (yD * yD)) % prime) /\
    z3 = toDomain #c (((yD + zD) * (yD + zD) - zD * zD - yD * yD) % prime)
  )
)
 (ensures(
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
    point_double_x3 #c x3 alpha fourBeta beta eightBeta; 
    point_double_z3 #c z3 pY pZ gamma delta;
    point_double_y3 #c y3 x3 alpha gamma eightGamma fourBeta;

  let h1 = ST.get() in

  let x = fromDomain #c (point_x_as_nat c h0 p) in 
  let y = fromDomain #c (point_y_as_nat c h0 p) in 
  let z = fromDomain #c (point_z_as_nat c h0 p) in 

  lemma_x3 #c x y z;
  lemma_z3 #c x y z; 
  lemma_y3 #c x y z (fromDomain #c (as_nat c h1 x3));

  lemma_pd_to_spec #c (point_x_as_nat c h0 p) (point_y_as_nat c h0 p) (point_z_as_nat c h0 p)
  (point_x_as_nat c h1 result) (point_y_as_nat c h1 result) (point_z_as_nat c h1 result)

