module Hacl.Impl.P256.PointDouble

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Hacl.Impl.P256.Arithmetics

open Lib.Buffer

open Spec.P256.Lemmas
open Spec.P256.Definitions
open Hacl.Impl.SolinasReduction
open Spec.P256.MontgomeryMultiplication
open Spec.P256.MontgomeryMultiplication.PointDouble
open Spec.P256.MontgomeryMultiplication.PointAdd
open Hacl.Impl.P256.LowLevel 
open Hacl.Impl.P256.LowLevel.PrimeSpecific
open Hacl.Impl.P256.MontgomeryMultiplication
open Spec.P256
open Hacl.Impl.P256.Math 

open FStar.Tactics 
open FStar.Tactics.Canon

open FStar.Math.Lemmas

friend Spec.P256.MontgomeryMultiplication
open FStar.Mul

#set-options "--z3rlimit 500 --ifuel 0 --fuel 0" 

val lemma_x3_0: x: int -> y: int -> z: int -> Lemma (
  ((3 * (x - (z * z % prime)) * (x + (z * z % prime)) % prime) * (3 * (x - (z * z % prime)) * (x + (z * z % prime)) % prime)  - 8 * (x * (y * y % prime) % prime)) % prime ==  ((3 * (x - (z * z % prime)) * (x + (z * z % prime)) % prime) * (3 * (x - (z * z % prime)) * (x + (z * z % prime)) % prime) - 8 * x * y * y) % prime)

let lemma_x3_0 x y z = 
  let open FStar.Tactics.Canon in 
  
  let t0 = (3 * (x - (z * z % prime)) * (x + (z * z % prime)) % prime) in 
  calc (==)
  {
    (t0 * t0 - 8 * (x * (y * y % prime) % prime)) % prime;
    (==) {lemma_mod_mul_distr_r x (y * y) prime}
    (t0 * t0 - 8 * ((x * (y * y)) % prime)) % prime;
    (==) {assert_by_tactic (x * (y * y) == x * y * y) canon}
    (t0 * t0 - 8 * (x * y * y % prime)) % prime;
    (==) {lemma_mod_sub_distr (t0 * t0) (8 * (x * y * y % prime)) prime}
    (t0 * t0 - (8 * (x * y * y % prime)) % prime) % prime;
    (==) {lemma_mod_mul_distr_r 8 (x * y * y) prime}
    (t0 * t0 - (8 * (x * y * y)) % prime) % prime;
    (==) {assert_by_tactic (8 * (x * y * y) == 8 * x * y * y) canon}
    (t0 * t0 - (8 * x * y * y) % prime) % prime;
    (==) {lemma_mod_sub_distr (t0 * t0) (8 * x * y * y) prime}
    (t0 * t0 - 8 * x * y * y) % prime;

  }

val lemma_x3_1: a: int -> b: int -> Lemma (((a % prime) * (a % prime) - b) % prime == (a * a - b) % prime)

let lemma_x3_1 a b = 
  calc (==)
  {
    ((a % prime) * (a % prime) - b) % prime;
    (==) {lemma_mod_add_distr (- b) ((a % prime) * (a % prime)) prime}
    ((a % prime) * (a % prime) % prime - b) % prime;
    (==) {lemma_mod_mul_distr_l a (a % prime) prime; lemma_mod_mul_distr_r a a prime}
    (a * a % prime - b) % prime;
    (==) {lemma_mod_add_distr (- b) (a * a) prime}
    (a * a - b) % prime;
  }
  



val lemma_x3: x: int -> y: int -> z: int -> Lemma (
  ((3 * (x - (z * z % prime)) * (x + (z * z % prime)) % prime) * (3 * (x - (z * z % prime)) * (x + (z * z % prime)) % prime) - 8 * (x * (y * y % prime) % prime)) % prime == 
  ((3 * (x - z * z) * (x + z * z)) * (3 * (x - z * z) * (x + z * z)) - 8 * x * (y * y)) % prime
)

let lemma_x3 x y z = 
  lemma_x3_0 x y z;

  calc (==)
  {
    (
      (3 * (x - (z * z % prime)) * (x + (z * z % prime)) % prime) * 
      (3 * (x - (z * z % prime)) * (x + (z * z % prime)) % prime) - 8 * x * y * y) % prime;
    
    (==) {lemma_mod_mul_distr_l (3 * (x - (z * z % prime))) (x + (z * z % prime)) prime}
    
    (
      (3 * (x - (z * z % prime)) % prime * (x + (z * z % prime)) % prime) * 
      (3 * (x - (z * z % prime)) % prime * (x + (z * z % prime)) % prime) - 8 * x * y * y) % prime;
    
  (==) {lemma_mod_mul_distr_r 3 (x - (z * z % prime)) prime}
  
     (
       (3 * ((x - (z * z % prime)) % prime) % prime * (x + (z * z % prime)) % prime) * 
       (3 * ((x - (z * z % prime)) % prime) % prime * (x + (z * z % prime)) % prime) - 8 * x * y * y) % prime;

   (==) {lemma_mod_sub_distr x (z * z) prime}

     (
       (3 * ((x - z * z) % prime) % prime * (x + (z * z % prime)) % prime) *
       (3 * ((x - z * z) % prime) % prime * (x + (z * z % prime)) % prime) - 8 * x * y * y) % prime;

  (==) {lemma_mod_mul_distr_r 3 (x - (z * z)) prime}

     (
       (3 * ((x - z * z)) % prime * (x + (z * z % prime)) % prime) * 
       (3 * ((x - z * z)) % prime * (x + (z * z % prime)) % prime) - 8 * x * y * y) % prime;

  (==) {lemma_mod_mul_distr_l (3 * (x - z * z)) (x + (z * z % prime)) prime}

     (
       (3 * (x - z * z) * (x + (z * z % prime)) % prime) * 
       (3 * (x - z * z) * (x + (z * z % prime)) % prime) - 8 * x * y * y) % prime;
     
  (==) {lemma_mod_mul_distr_r (3 * (x - z * z)) (x + (z * z % prime)) prime; 
       lemma_mod_add_distr x (z * z) prime; 
       lemma_mod_mul_distr_r (3 * (x - z * z)) (x + z * z) prime}

    (  
      (3 * (x - z * z) * (x + (z * z)) % prime) * 
      (3 * (x - z * z) * (x + (z * z)) % prime) - 8 * x * y * y) % prime;
  
  (==) {lemma_x3_1 (3 * (x - z * z) * (x + (z * z))) (8 * x * y * y)}

    (  
      (3 * (x - z * z) * (x + z * z)) * 
      (3 * (x - z * z) * (x + z * z)) - 8 * x * y * y) % prime;

}

val y3_lemma_0: x: int ->  y: int -> z: int -> x3: int -> t0: int -> Lemma (
   (t0 - 8 * (y * y % prime) * (y * y % prime)) % prime == (t0 - 8 * y * y * y * y) % prime)

let y3_lemma_0 x y z x3 t0 = 
  calc (==) {
    (t0 - 8 * (y * y % prime) * (y * y % prime)) % prime;
  (==) {lemma_mod_sub_distr t0 (8 * (y * y % prime) * (y * y % prime)) prime}
    (t0 - (8 * (y * y % prime) * (y * y % prime)) % prime) % prime;
  (==) {lemma_mod_mul_distr_r (8 * (y * y % prime)) (y * y) prime}
    (t0 - (8 * (y * y % prime) * (y * y)) % prime) % prime;
  (==) {lemma_mod_mul_distr_r (8 * (y * y)) (y * y) prime}
    (t0 - (8 * (y * y) * (y * y)) % prime) % prime;
  (==) {assert_by_tactic (8 * (y * y) * (y * y) == 8 * y * y * y * y) canon}
    (t0 - (8 * y * y * y * y) % prime) % prime;
  (==) {lemma_mod_sub_distr t0 (8 * y * y * y * y) prime}
    (t0 - 8 * y * y * y * y) % prime;
  }


val y3_lemma_1: x: int ->  y: int -> z: int ->  
  Lemma (3 * (x - (z * z % prime)) * (x + (z * z % prime)) % prime == 3 * (x + z * z) * (x - z * z)  % prime)

let y3_lemma_1 x y z = 
  let open FStar.Tactics.Canon in 
  calc (==)
  {
    3 * (x - (z * z % prime)) * (x + (z * z % prime)) % prime;
    (==) {lemma_mod_mul_distr_r (3 * (x - (z * z % prime))) (x + (z * z % prime)) prime}
      3 * (x - (z * z % prime)) * ((x + (z * z % prime)) % prime) % prime;
    (==) {lemma_mod_add_distr x (z * z) prime}
      3 * (x - (z * z % prime)) * ((x + z * z) % prime) % prime;
    (==) {lemma_mod_mul_distr_r (3 * (x - (z * z % prime))) (x + z * z) prime}
      3 * (x - (z * z % prime)) * (x + z * z) % prime;
    (==) {assert_by_tactic (3 * (x - (z * z % prime)) * (x + z * z) == 3 * (x + z * z) * (x - (z * z % prime))) canon}
      3 * (x + z * z) * (x - (z * z % prime)) % prime;
    (==) {lemma_mod_mul_distr_r (3 * (x + z * z)) (x - (z * z % prime)) prime}
      3 * (x + z * z) * ((x - (z * z % prime))  % prime)  % prime;
    (==) {lemma_mod_sub_distr x (z * z) prime}
      3 * (x + z * z) * ((x - z * z) % prime)  % prime;
    (==) {lemma_mod_mul_distr_r (3 * (x + z * z)) (x - z * z) prime}
      3 * (x - z * z) * (x + z * z)  % prime;
    (==) {assert_by_tactic (3 * (x + z * z) * (x - z * z) == 3 * (x - z * z) * (x + z * z)) canon}
      3 * (x + z * z) * (x - z * z)  % prime; 
    }


val lemma_y3: x: int -> y: int -> z: int -> x3: int -> Lemma (
  ((3 * (x - (z * z % prime)) * (x + (z * z % prime)) % prime) *  ((4 * (x * (y * y % prime) % prime) % prime) - x3) - 8 * (y * y % prime) * (y * y % prime)) % prime == (3 * (x + z * z) * (x - z * z) *  (4 * x * (y * y) - x3) - 8 * (y * y) * (y * y)) % prime)
  

let lemma_y3 x y z x3 = 
  let open FStar.Tactics.Canon in 
  let t = ((3 * (x - (z * z % prime)) * (x + (z * z % prime)) % prime) *  ((4 * (x * (y * y % prime) % prime) % prime) - x3) - 8 * (y * y % prime) * (y * y % prime)) % prime in 
  let t0 = (3 * (x - (z * z % prime)) * (x + (z * z % prime)) % prime) *  ((4 * (x * (y * y % prime) % prime) % prime) - x3) in 
  assert(t == (t0 - 8 * (y * y % prime) * (y * y % prime)) % prime);

  y3_lemma_0 x y z x3 t0;
  y3_lemma_1 x y z;


  calc (==)
  {
      4 * (x * (y * y % prime) % prime) % prime;
    (==) {lemma_mod_mul_distr_r x (y * y) prime}
       4 * ((x * (y * y)) % prime) % prime;
    (==) {assert_by_tactic (x * (y * y) == x * y * y) canon}
      (4 * ((x * y * y) % prime)) % prime;
    (==) {lemma_mod_mul_distr_r 4 (x * y * y) prime}
      (4 * (x * y * y)) % prime;
    (==) {assert_by_tactic (4 * (x * y * y) == 4 * x * y * y) canon}
      4 * x * y * y % prime;
      
   };

  calc (==)
  {
    ((3 * (x + z * z) * (x - z * z)  % prime) *  (4 * x * y * y % prime - x3) - 8 * y * y * y * y) % prime;
    (==) {lemma_mod_add_distr (- 8 * y * y * y * y) ((3 * (x + z * z) * (x - z * z)  % prime) *  (4 * x * y * y % prime - x3)) prime}
    ((((3 * (x + z * z) * (x - z * z)) % prime) *  (4 * x * y * y % prime - x3)) % prime - 8 * y * y * y * y) % prime;
    (==) {lemma_mod_mul_distr_l (3 * (x + z * z) * (x - z * z))  (4 * x * y * y % prime - x3) prime}
    (((3 * (x + z * z) * (x - z * z)) *  (4 * x * y * y % prime - x3)) % prime - 8 * y * y * y * y) % prime;
    (==) {lemma_mod_mul_distr_r (3 * (x + z * z) * (x - z * z)) (4 * x * y * y % prime - x3) prime}
    (((3 * (x + z * z) * (x - z * z)) *  ((4 * x * y * y % prime - x3) % prime)) % prime - 8 * y * y * y * y) % prime;
    (==) {lemma_mod_add_distr (- x3) (4 * x * y * y) prime}
    (((3 * (x + z * z) * (x - z * z)) *  ((4 * x * y * y - x3) % prime)) % prime - 8 * y * y * y * y) % prime;
    (==) {lemma_mod_mul_distr_r (3 * (x + z * z) * (x - z * z)) (4 * x * y * y - x3) prime}
    ((3 * (x + z * z) * (x - z * z) *  (4 * x * y * y - x3)) % prime - 8 * y * y * y * y) % prime;
    (==) {lemma_mod_add_distr (- 8 * y * y * y * y) (3 * (x + z * z) * (x - z * z) *  (4 * x * y * y - x3)) prime}
    (3 * (x + z * z) * (x - z * z) *  (4 * x * y * y - x3) - 8 * y * y * y * y) % prime;
    (==) {assert_by_tactic (8 * y * y * y * y == 8 * (y * y) * (y * y)) canon}
    (3 * (x + z * z) * (x - z * z) *  (4 * x * y * y - x3) - 8 * (y * y) * (y * y)) % prime;
    (==) {assert_by_tactic (4 * x * y * y == 4 * x * (y * y)) canon}
    (3 * (x + z * z) * (x - z * z) *  (4 * x * (y * y) - x3) - 8 * (y * y) * (y * y)) % prime;
    
  }
 

val lemma_z3: x: int -> y: int -> z: int -> Lemma 
  (((y + z) * (y + z) - (y * y % prime) - (z * z % prime)) % prime == ((y + z) * (y + z) - z * z - y * y) % prime)


let lemma_z3 x y z = 
  let t = ((y + z) * (y + z) - (y * y % prime) - (z * z % prime)) % prime in 

  calc (==) 
    {
      ((y + z) * (y + z) - (y * y % prime) - (z * z % prime)) % prime;
      (==) {lemma_mod_sub_distr ((y + z) * (y + z) - (y * y % prime)) (z * z) prime}
      ((y + z) * (y + z) - (y * y % prime) - z * z) % prime;
      (==) {lemma_mod_sub_distr ((y + z) * (y + z) - z * z) (y * y) prime}
      ((y + z) * (y + z) - z * z - y * y) % prime;}



(*   delta:=Z1^2;
     gamma:=Y1^2;
     beta:=X1*gamma;
     alpha:=3*(X1-delta)*(X1+delta);
     X3:=alpha^2-8*beta;
     Z3:=(Y1+Z1)^2-gamma-delta;
     Y3:=alpha*(4*beta-X3)-8*gamma^2;
     SS!(x3-X3/Z3^2); SS!(y3-Y3/Z3^3); *)

val point_double_a_b_g: p: point -> alpha: felem -> beta: felem -> gamma: felem -> delta: felem -> tempBuffer: lbuffer uint64 (size 12) -> 
  Stack unit
    (requires fun h -> 
      live h p /\ live h alpha /\ live h beta /\ live h gamma /\ live h delta /\ live h tempBuffer /\ 
      LowStar.Monotonic.Buffer.all_disjoint [loc p; loc alpha; loc beta; loc gamma; loc delta; loc tempBuffer] /\
      as_nat h (gsub p (size 8) (size 4)) < prime /\ 
      as_nat h (gsub p (size 0) (size 4)) < prime /\ 
      as_nat h (gsub p (size 4) (size 4)) < prime
    )
    (ensures fun h0 _ h1 -> modifies (loc alpha |+| loc beta |+| loc gamma |+| loc delta |+| loc tempBuffer) h0 h1 /\
      (
	let x = fromDomain_ (as_nat h0 (gsub p (size 0) (size 4))) in 
	let y = fromDomain_ (as_nat h0 (gsub p (size 4) (size 4))) in 
	let z = fromDomain_ (as_nat h0 (gsub p (size 8) (size 4))) in 
	as_nat h1 delta = toDomain_ (z * z % prime) /\
	as_nat h1 gamma = toDomain_ (y * y % prime) /\
	as_nat h1 beta = toDomain_ (x * fromDomain_(as_nat h1 gamma) % prime) /\
	as_nat h1 alpha = toDomain_ (3 * (x - fromDomain_ (as_nat h1 delta)) * (x + fromDomain_ (as_nat h1 delta)) % prime)
      )
    )

let point_double_a_b_g p alpha beta gamma delta tempBuffer = 
  let pX = sub p (size 0) (size 4) in 
  let pY = sub p (size 4) (size 4) in 
  let pZ = sub p (size 8) (size 4) in 

  let a0 = sub tempBuffer (size 0) (size 4) in 
  let a1 = sub tempBuffer (size 4) (size 4) in 
  let alpha0 = sub tempBuffer (size 8) (size 4) in 

  montgomery_square_buffer pZ delta; (* delta = z * z*)
  montgomery_square_buffer pY gamma; (* gamma = y * y *)
  montgomery_multiplication_buffer pX gamma beta; (* beta = x * gamma *)

  let h0 = ST.get() in 

  p256_sub pX delta a0; (* a0 = x - delta *)
  p256_add pX delta a1; (* a1 = x + delta *)
  montgomery_multiplication_buffer a0 a1 alpha0; (* alpha = (x - delta) * (x + delta) *)
  multByThree alpha0 alpha;

    let open FStar.Tactics.Canon in 
    let xD = fromDomain_ (as_nat h0 pX) in 
    let dlt = fromDomain_ (as_nat h0 delta) in 

    calc (==) 
    {
      toDomain_ (3 * (((xD - dlt) % prime) *  ((xD + dlt) % prime) % prime) % prime);
    (==) {lemma_mod_mul_distr_l (xD - dlt) ((xD + dlt) % prime) prime; lemma_mod_mul_distr_r (xD - dlt) (xD + dlt) prime}
      toDomain_ (3 * ((xD - dlt) *  (xD + dlt) % prime) % prime);
    (==) {lemma_mod_mul_distr_r 3 ((xD - dlt) * (xD + dlt)) prime}
      toDomain_ (3 * ((xD - dlt) * (xD + dlt)) % prime);
    (==) {assert_by_tactic (3 * (xD - dlt) * (xD + dlt) == 3 * ((xD - dlt) * (xD + dlt))) canon}
      toDomain_ (3 * (xD - dlt) * (xD + dlt) % prime);
    }

val point_double_x3: x3: felem -> alpha: felem -> fourBeta: felem -> beta: felem -> eightBeta: felem ->
  Stack unit
    (requires fun h -> live h x3 /\ live h alpha /\ live h fourBeta /\ live h beta /\ live h eightBeta /\
      LowStar.Monotonic.Buffer.all_disjoint [loc x3; loc alpha; loc fourBeta; loc beta; loc eightBeta] /\
      as_nat h alpha < prime /\
      as_nat h beta < prime
    )
    (ensures fun h0 _ h1 -> modifies (loc x3 |+| loc fourBeta |+| loc eightBeta) h0 h1 /\
      as_nat h1 fourBeta = toDomain_ (4 * fromDomain_ (as_nat h0 beta) % prime256) /\
      as_nat h1 x3 = toDomain_ ((fromDomain_ (as_nat h0 alpha) * fromDomain_ (as_nat h0 alpha) - 8 * (fromDomain_ (as_nat h0 beta))) % prime)
    )

let point_double_x3 x3 alpha fourBeta beta eightBeta  = 
    let h0 = ST.get() in 
  montgomery_square_buffer alpha x3; (* x3 = alpha ** 2 *)
  multByFour beta fourBeta; (*  fourBeta = beta * 4 *)
  multByTwo fourBeta eightBeta; (* eightBeta = beta * 8 *)
  p256_sub x3 eightBeta x3 (* x3 = alpha ** 2 - beta * 8 *);

  calc(==)
  {
     toDomain_ (((fromDomain_ (as_nat h0 alpha) * fromDomain_ (as_nat h0 alpha) % prime) - (2 *  (4 * fromDomain_ (as_nat h0 beta) % prime256) % prime256)) % prime256);
  (==) {lemma_mod_mul_distr_r 2 (4 * fromDomain_ (as_nat h0 beta)) prime256}
  toDomain_ (((fromDomain_ (as_nat h0 alpha) * fromDomain_ (as_nat h0 alpha) % prime) - (8 * fromDomain_ (as_nat h0 beta)) % prime256) % prime256);
  (==) {lemma_mod_sub_distr (fromDomain_ (as_nat h0 alpha) * fromDomain_ (as_nat h0 alpha) % prime) (8 * fromDomain_ (as_nat h0 beta)) prime256}
    toDomain_ (((fromDomain_ (as_nat h0 alpha) * fromDomain_ (as_nat h0 alpha) % prime) - (8 * fromDomain_ (as_nat h0 beta))) % prime256);
  (==) {lemma_mod_add_distr (- 8 * fromDomain_ (as_nat h0 beta)) (fromDomain_ (as_nat h0 alpha) * fromDomain_ (as_nat h0 alpha)) prime}
    toDomain_ ((fromDomain_ (as_nat h0 alpha) * fromDomain_ (as_nat h0 alpha) - 8 * fromDomain_ (as_nat h0 beta)) % prime256);
  }


val point_double_z3: z3: felem -> pY: felem -> pZ: felem -> gamma: felem -> delta: felem ->
  Stack unit 
    (requires fun h -> live h z3 /\ live h pY /\ live h pZ /\ live h gamma /\ live h delta /\
      eq_or_disjoint pZ z3 /\ disjoint z3 gamma /\ disjoint z3 delta /\ disjoint pY z3 /\
      as_nat h gamma < prime /\
      as_nat h delta < prime /\
      as_nat h pY < prime /\ 
      as_nat h pZ < prime 
    )
    (ensures fun h0 _ h1 -> modifies (loc z3) h0 h1 /\
      (
	let y = fromDomain_ (as_nat h0 pY) in 
	let z = fromDomain_ (as_nat h0 pZ) in 
	as_nat h1 z3 = toDomain_ (((y + z) * (y + z) - fromDomain_ (as_nat h0 gamma) - fromDomain_ (as_nat h0 delta)) % prime)
      )
    )

let point_double_z3 z3 pY pZ gamma delta  = 
    let h0 = ST.get() in 

  p256_add pY pZ z3; (* z3 = py + pz *) 
  montgomery_square_buffer z3 z3; (* z3 = (py + pz) ** 2 *) 
  p256_sub z3 gamma z3; (* z3 =  (py + pz) ** 2 - gamma  *)
  p256_sub z3 delta z3 (* z3 = (py + pz) ** 2 - gamma - delta *);

    let pyD = fromDomain_ (as_nat h0 pY) in 
    let pzD = fromDomain_ (as_nat h0 pZ) in 

  calc (==)
  {
    toDomain_ (((((( ((pyD + pzD) % prime) * ((pyD + pzD) % prime) % prime)) - fromDomain_ (as_nat h0 gamma)) % prime) - fromDomain_ (as_nat h0 delta)) % prime);
  (==) {lemma_mod_mul_distr_l (pyD + pzD) ((pyD + pzD) % prime) prime; lemma_mod_mul_distr_r (pyD + pzD) (pyD + pzD) prime}
    toDomain_ ((((((pyD + pzD) * (pyD + pzD) % prime) - fromDomain_ (as_nat h0 gamma)) % prime) - fromDomain_ (as_nat h0 delta)) % prime);
  (==) {lemma_mod_add_distr (- fromDomain_ (as_nat h0 gamma)) ((pyD + pzD) * (pyD + pzD)) prime }
    toDomain_ (((((pyD + pzD) * (pyD + pzD) - fromDomain_ (as_nat h0 gamma)) % prime) - fromDomain_ (as_nat h0 delta)) % prime);
  (==) {lemma_mod_add_distr (- fromDomain_ (as_nat h0 delta)) ((pyD + pzD) * (pyD + pzD) - fromDomain_ (as_nat h0 gamma)) prime}
    toDomain_ (((pyD + pzD) * (pyD + pzD) - fromDomain_ (as_nat h0 gamma) - fromDomain_ (as_nat h0 delta)) % prime);
  }


val point_double_y3: y3: felem -> x3: felem -> alpha: felem -> gamma: felem -> eightGamma: felem -> fourBeta: felem ->
  Stack unit 
  (requires fun h -> live h y3 /\ live h x3 /\ live h alpha /\ live h gamma /\ live h eightGamma /\ live h fourBeta /\
    LowStar.Monotonic.Buffer.all_disjoint [loc y3; loc x3; loc alpha; loc gamma; loc eightGamma; loc fourBeta] /\
    as_nat h x3 < prime /\
    as_nat h alpha < prime /\
    as_nat h gamma < prime /\
    as_nat h fourBeta < prime
  )
  (ensures fun h0 _ h1 -> modifies (loc y3 |+| loc gamma |+| loc eightGamma) h0 h1 /\
    (
      let alphaD = fromDomain_ (as_nat h0 alpha) in 
      let gammaD = fromDomain_ (as_nat h0 gamma) in 
      as_nat h1 y3 == toDomain_ ((alphaD *  (fromDomain_ (as_nat h0 fourBeta) - fromDomain_ (as_nat h0 x3)) - 8 * gammaD * gammaD) % prime)
    )
  )



let point_double_y3 y3 x3 alpha gamma eightGamma fourBeta = 
    let h0 = ST.get() in 
  p256_sub fourBeta x3 y3; (* y3 = 4 * beta - x3 *)
  montgomery_multiplication_buffer alpha y3 y3; (* y3 = alpha * (4 * beta - x3) *)
  montgomery_square_buffer gamma gamma; (* gamma = gamma ** 2 *)
  multByEight gamma eightGamma; (* gamma = 8 * gamma ** 2 *)
  p256_sub y3 eightGamma y3 (* y3 = alpha * y3 - 8 * gamma **2 *);


  let alphaD = fromDomain_ (as_nat h0 alpha) in 
  let gammaD = fromDomain_ (as_nat h0 gamma) in 

  let open FStar.Tactics.Canon in 

  calc(==)
  {
     toDomain_ (((fromDomain_ (as_nat h0 alpha) *  ((fromDomain_ (as_nat h0 fourBeta) - fromDomain_ (as_nat h0 x3)) % prime) % prime) - (8 *  (fromDomain_ (as_nat h0 gamma) * fromDomain_ (as_nat h0 gamma) % prime) % prime)) % prime);
  (==) {lemma_mod_mul_distr_r (fromDomain_ (as_nat h0 alpha)) (((fromDomain_ (as_nat h0 fourBeta) - fromDomain_ (as_nat h0 x3)))) prime}
    toDomain_ (((fromDomain_ (as_nat h0 alpha) *  (fromDomain_ (as_nat h0 fourBeta) - fromDomain_ (as_nat h0 x3)) % prime) - (8 *  (fromDomain_ (as_nat h0 gamma) * fromDomain_ (as_nat h0 gamma) % prime) % prime)) % prime);
  (==) {lemma_mod_mul_distr_r 8 (fromDomain_ (as_nat h0 gamma) * (fromDomain_ (as_nat h0 gamma))) prime}
    toDomain_ (((alphaD *  (fromDomain_ (as_nat h0 fourBeta) - fromDomain_ (as_nat h0 x3)) % prime) - (8 * (gammaD * gammaD) % prime)) % prime);
  (==) {lemma_mod_add_distr (-(8 * (gammaD * gammaD) % prime)) (alphaD *  (fromDomain_ (as_nat h0 fourBeta) - fromDomain_ (as_nat h0 x3))) prime  }
      toDomain_ (((alphaD *  (fromDomain_ (as_nat h0 fourBeta) - fromDomain_ (as_nat h0 x3))) - (8 * (gammaD * gammaD) % prime)) % prime);
  (==) {lemma_mod_sub_distr (alphaD *  (fromDomain_ (as_nat h0 fourBeta) - fromDomain_ (as_nat h0 x3))) (8 * (gammaD * gammaD)) prime}
       toDomain_ (((alphaD *  (fromDomain_ (as_nat h0 fourBeta) - fromDomain_ (as_nat h0 x3))) - (8 * (gammaD * gammaD))) % prime);
  (==) {assert_by_tactic (8 * (gammaD * gammaD) == 8 * gammaD * gammaD) canon}
    toDomain_ ((alphaD *  (fromDomain_ (as_nat h0 fourBeta) - fromDomain_ (as_nat h0 x3)) - 8 * gammaD * gammaD) % prime);
}


let point_double p result tempBuffer = 
  let pX = sub p (size 0) (size 4) in 
  let pY = sub p (size 4) (size 4) in 
  let pZ = sub p (size 8) (size 4) in 

  let x3 = sub result (size 0) (size 4) in 
  let y3 = sub result (size 4) (size 4) in 
  let z3 = sub result (size 8) (size 4) in 

  let delta = sub tempBuffer (size 0) (size 4) in 
  let gamma = sub tempBuffer (size 4) (size 4) in 
  let beta = sub tempBuffer (size 8) (size 4) in 
  let alpha = sub tempBuffer (size 16) (size 4) in 
  
  let fourBeta = sub tempBuffer (size 20) (size 4) in 
  let eightBeta = sub tempBuffer (size 24) (size 4) in 
  let eightGamma = sub tempBuffer (size 28) (size 4) in 

  let tmp = sub tempBuffer (size 32) (size 12) in 
  

  let h0 = ST.get() in 
    point_double_a_b_g p alpha beta gamma delta tmp;
    point_double_x3 x3 alpha fourBeta beta eightBeta; 
    point_double_z3 z3 pY pZ gamma delta;
    point_double_y3 y3 x3 alpha gamma eightGamma fourBeta;

  let h4 = ST.get() in 

  let x = fromDomain_ (as_nat h0 (gsub p (size 0) (size 4))) in 
  let y = fromDomain_ (as_nat h0 (gsub p (size 4) (size 4))) in 
  let z = fromDomain_ (as_nat h0 (gsub p (size 8) (size 4))) in 
  
  lemma_x3 x y z;
  lemma_z3 x y z;
  lemma_y3 x y z (fromDomain_ (as_nat h4 x3))
