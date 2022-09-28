module Hacl.Impl.EC.General.PointDouble


open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Hacl.Impl.EC.Arithmetics

open Lib.Buffer

open Spec.ECC
open Hacl.EC.Lemmas
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

open Hacl.Impl.EC.General.PointDouble.Aux

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
    point_eval c h p)
  (ensures fun h0 _ h1 -> modifies (loc alpha |+| loc beta |+| loc gamma |+| loc delta |+| loc tempBuffer) h0 h1 /\ (
    let len = getCoordinateLenU64 c in 
    let prime = getPrime c in 
	
    let x = fromDomain #c (point_x_as_nat c h0 p) in 
    let y = fromDomain #c (point_y_as_nat c h0 p) in 
    let z = fromDomain #c (point_z_as_nat c h0 p) in 
	
    as_nat c h1 delta = toDomain #c (z * z % prime) /\
    as_nat c h1 gamma = toDomain #c (y * y % prime) /\
    as_nat c h1 beta = toDomain #c (x * fromDomain #c (as_nat c h1 gamma) % prime) /\
    as_nat c h1 alpha = toDomain_ #c #DH ((3 * x * x + aCoordinate #c * (z * z) * (z * z)) % prime)))


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

  Hacl.Impl.EC.Setup.uploadA #c alpha0; (* aplha0 = a*)
  montgomery_square_buffer_dh  delta a0; (* a0 = delta * delta *)
  montgomery_multiplication_buffer_dh #c alpha0 a0 a0; (* a0 = a * delta * delta*)

  montgomery_square_buffer_dh #c pX alpha0; (* alpha0 = x * x *)
  multByThree alpha0 alpha; (* alpha = 3 * x * x*)
  felem_add alpha a0 alpha; (* alpha = a * delta * delta + 3 * x * x*)
    let h3 = ST.get() in 

    let prime = getPrime c in 
    let a = aCoordinate #c in 
    let open FStar.Tactics.Canon in 
    let xD = fromDomain #c (as_nat c h0 pX) in 
    let zD = fromDomain #c (as_nat c h0 pZ) in 
    let deltaD = fromDomain_ #c #DH (as_nat c h0 delta) in 

  calc (==) {as_nat c h3 alpha;
    (==) {}
  toDomain_ #c #DH (((3 * (xD * xD % prime) % prime) + (((a % prime) * (deltaD * deltaD % prime) % prime))) % prime);
    (==) {lemma_mod_mul_distr_r 3 (xD * xD) prime}
  toDomain_ #c #DH (((3 * (xD * xD) % prime) + (((a % prime) * (deltaD * deltaD % prime) % prime))) % prime);
    (==) {lemma_mod_mul_distr_l a (deltaD * deltaD % prime) prime}
  toDomain_ #c #DH (((3 * (xD * xD) % prime) + ((a * (deltaD * deltaD % prime) % prime))) % prime);
    (==) {lemma_mod_mul_distr_r a (deltaD * deltaD) prime}
  toDomain_ #c #DH (((3 * (xD * xD) % prime) + ((a * (deltaD * deltaD) % prime))) % prime);  
    (==) {lemma_mod_add_distr (3 * (xD * xD) % prime) (a * (deltaD * deltaD)) prime}
  toDomain_ #c #DH (((3 * (xD * xD) % prime) + a * (deltaD * deltaD)) % prime);    
    (==) {lemma_mod_add_distr (a * (deltaD * deltaD)) (3 * (xD * xD)) prime}
  toDomain_ #c #DH ((3 * (xD * xD) + a * (deltaD * deltaD)) % prime);    
    (==) {
      assert_by_tactic (3 * (xD * xD) == 3 * xD * xD) canon;
      assert_by_tactic (a * (deltaD * deltaD) == a * deltaD * deltaD) canon}
  toDomain_ #c #DH ((3 * xD * xD + a * deltaD * deltaD) % prime); 
    (==) {}
  toDomain_ #c #DH ((3 * xD * xD + (a * (zD * zD % prime) * (zD * zD % prime)))  % prime);
    (==) {lemma_mod_add_distr (3 * xD * xD) (a * (zD * zD % prime) * (zD * zD % prime)) prime}
  toDomain_ #c #DH ((3 * xD * xD + a * (zD * zD % prime) * (zD * zD % prime) % prime) % prime);
    (==) {lemma_mod_mul_distr_r (a * (zD * zD % prime)) (zD * zD) prime}
  toDomain_ #c #DH ((3 * xD * xD + a * (zD * zD % prime) * (zD * zD) % prime) % prime);
    (==) {assert_by_tactic (a * (zD * zD % prime) * (zD * zD) == a  * (zD * zD) * (zD * zD % prime)) canon}
  toDomain_ #c #DH ((3 * xD * xD + a * (zD * zD) * (zD * zD % prime) % prime) % prime);
    (==) {lemma_mod_mul_distr_r (a * (zD * zD)) (zD * zD) prime}
  toDomain_ #c #DH ((3 * xD * xD + a * (zD * zD) * (zD * zD) % prime) % prime);
    (==) {lemma_mod_add_distr (3 * xD * xD) (a * (zD * zD) * (zD * zD)) prime}
  toDomain_ #c #DH ((3 * xD * xD + a * (zD * zD) * (zD * zD)) % prime);  }


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
