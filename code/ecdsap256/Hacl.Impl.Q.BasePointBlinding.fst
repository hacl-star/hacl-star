module Hacl.Impl.Q.BasePointBlinding

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST


open Lib.IntTypes
open Lib.Buffer

open Spec.P256
open Spec.P256.Definitions
open Spec.P256.Lemmas

open FStar.Mul

open Spec.P256.MontgomeryMultiplication
open Hacl.Impl.P256.MontgomeryMultiplication

open FStar.Math.Lemmas 

open FStar.Tactics.Canon 

#set-options "--z3rlimit 200" 



val basePointRandomisation: result: point -> r: felem ->
  Stack unit 
    (requires fun h -> live h result /\ live h r /\ 
      as_nat h r < prime256 /\ disjoint result r /\
      as_nat h (gsub result (size 0) (size 4)) < prime256 /\
      as_nat h (gsub result (size 4) (size 4)) < prime256 /\
      as_nat h (gsub result (size 8) (size 4)) < prime256)
    (ensures fun h0 _ h1 -> 
      let resultPoint = point_prime_to_coordinates (as_seq h1 result) in 
      let resultFromDomain = fromDomainPoint resultPoint in 
      let resultNormalized = _norm resultFromDomain in 
      let basePoint = point_prime_to_coordinates (as_seq h0 result) in 
      basePoint == resultNormalized)


val lemma_bp_r: x0: nat -> x1: nat -> b: nat -> Lemma 
  (pow (x0 * x1 * x0 * x1) b % prime256 == 
  pow ((x0 * x0) * (x1 * x1)) b % prime256)

let lemma_bp_r x0 x1 b = 
  let open FStar.Tactics in 
  assert_by_tactic ((x0 * x0) * (x1 * x1) == x0 * x1 * x0 * x1) canon


val lemma_pow2: x: nat -> Lemma (x * x == pow x 2)

let lemma_pow2 x = ()



#set-options "--z3rlimit 200 --ifuel 0 --fuel 0" 


val lemma_bp0: z0D: nat -> r: nat ->  Lemma (
  let primeMinusTwo = prime256 - 2 in 
  pow ((z0D * r % prime256) * (z0D * r % prime256)) primeMinusTwo % prime256 ==
  ((pow (z0D * z0D) primeMinusTwo) * (pow r (2 * primeMinusTwo))) % prime256)

let lemma_bp0 z0D r = 
  let primeMinusTwo: nat = prime256 - 2 in 

  calc (==) {
    pow ((z0D * r % prime256) * (z0D * r % prime256)) primeMinusTwo % prime256;
    (==) {power_distributivity ((z0D * r % prime256) * (z0D * r % prime256)) primeMinusTwo prime256}
    pow ((z0D * r % prime256) * (z0D * r % prime256) % prime256) primeMinusTwo % prime256;
    (==) {lemma_mod_mul_distr_l (z0D * r) (z0D * r % prime256) prime256}
    pow (z0D * r * (z0D * r % prime256) % prime256) primeMinusTwo % prime256;
    (==) {lemma_mod_mul_distr_r (z0D * r) (z0D * r) prime256}
    pow ((z0D * r) * (z0D * r) % prime256) primeMinusTwo % prime256;
    (==) {power_distributivity ((z0D * r) * (z0D * r)) primeMinusTwo prime256}
    pow (z0D * r * (z0D * r)) primeMinusTwo % prime256;
    (==) {_ by (canon())}
    pow (z0D * r * z0D * r) primeMinusTwo % prime256;
    (==) {lemma_bp_r z0D r primeMinusTwo}
    pow ((z0D * z0D) * (r * r)) primeMinusTwo % prime256; 
    (==) {power_distributivity_2 (z0D * z0D) (r * r) primeMinusTwo}
    ((pow (z0D * z0D) primeMinusTwo) * (pow (r * r) primeMinusTwo)) % prime256; 
    (==) {lemma_pow2 r}
    ((pow (z0D * z0D) primeMinusTwo) * (pow (pow r 2) primeMinusTwo)) % prime256;
    (==) {power_mult r 2 primeMinusTwo}
    ((pow (z0D * z0D) primeMinusTwo) * (pow r (2 * primeMinusTwo))) % prime256;}


val lemma_bp_y3_reduction: z0D: nat -> r: nat -> Lemma (
  let primeMinusTwo = prime256 - 2  in 
  pow ((z0D * r % prime256) * (z0D * r % prime256) * (z0D * r % prime256)) primeMinusTwo % prime256 ==     
  pow ((z0D * r) * (z0D * r) * (z0D * r)) primeMinusTwo % prime256)

let lemma_bp_y3_reduction z0D r = 
  let primeMinusTwo = prime256 - 2 in
  calc (==)
  {
    pow ((z0D * r % prime256) * (z0D * r % prime256) * (z0D * r % prime256)) primeMinusTwo % prime256;
    (==) {power_distributivity ((z0D * r % prime256) * (z0D * r % prime256) * (z0D * r % prime256)) primeMinusTwo prime256}
    pow ((z0D * r % prime256) * (z0D * r % prime256) * (z0D * r % prime256) % prime256) primeMinusTwo % prime256;
    (==) {lemma_mod_mul_distr_r ((z0D * r % prime256) * (z0D * r % prime256)) (z0D * r) prime256}
    pow ((z0D * r % prime256) * (z0D * r % prime256) * (z0D * r) % prime256) primeMinusTwo % prime256;
    (==) {_ by (canon())}
    pow ((z0D * r) * (z0D * r % prime256) * (z0D * r % prime256) % prime256) primeMinusTwo % prime256;
    (==) {lemma_mod_mul_distr_r ((z0D * r) * (z0D * r % prime256)) (z0D * r) prime256}
    pow ((z0D * r) * (z0D * r % prime256) * (z0D * r) % prime256) primeMinusTwo % prime256;
    (==) {_ by (canon())}
    pow ((z0D * r) * (z0D * r) * (z0D * r % prime256) % prime256) primeMinusTwo % prime256;
    (==) {lemma_mod_mul_distr_r ((z0D * r) * (z0D * r)) (z0D * r) prime256}
    pow ((z0D * r) * (z0D * r) * (z0D * r) % prime256) primeMinusTwo % prime256;
    (==) {power_distributivity ((z0D * r) * (z0D * r) * (z0D * r)) primeMinusTwo prime256}
    pow ((z0D * r) * (z0D * r) * (z0D * r)) primeMinusTwo % prime256;
  }


(*TODO: extend to z *)
val lemma_bp_random: x0: nat -> y0: nat 
  -> z0: nat -> r: nat 
  -> x1: nat {x1 = toDomain_ (fromDomain_ x0 * (r * r % prime256) % prime256)}
  -> y1: nat {y1 = toDomain_ (fromDomain_ y0 * ((r * r % prime256) * r % prime256) % prime256)} 
  -> z1: nat {z1 = toDomain_ (fromDomain_ z0 * r % prime256) /\
     isPointAtInfinity (fromDomain_ x1, fromDomain_ y1, fromDomain_ z1) == false} 
  -> Lemma (
  let realPoint = fromDomain_ x0, fromDomain_ y0, fromDomain_ z0 in 
  let rX, rY, rZ = _norm realPoint in 
  let hiddenPoint = fromDomain_ x1, fromDomain_ y1, fromDomain_ z1 in 
  let hX, hY, hZ = _norm hiddenPoint in 
    rX == hX /\ rY == hY)


let lemma_bp_random x0 y0 z0 r x1 y1 z1 = 

  let open Spec.P256.Lemmas in 
  
  let x1D, y1D, z1D = fromDomain_ x1, fromDomain_ y1, fromDomain_ z1 in 
  
  let z0D = fromDomain_ z0 in 
  let rrr = r * r * r in 
  
  let primeMinusTwo: nat = prime256 - 2 in 
  let primeMinusOne: nat = prime256 -1 in 

  lemma_bp0 z0D r;
  lemma_bp_y3_reduction z0D r;

  assume ((r * r * r) % prime256 <> 0 /\ (r * r) % prime256 <> 0 /\ FStar.Math.Euclid.is_prime prime256);


  let bpHiddenX, bpHiddenY, bpHiddenZ = _norm (fromDomain_ x0, fromDomain_ y0, fromDomain_ z0) in 

  calc (==)
  {
   (pow (z0D * z0D) primeMinusTwo % prime256 * fromDomain_ x0) % prime256;
   (==) {lemma_mod_mul_distr_l (pow (z0D * z0D) primeMinusTwo) (fromDomain_ x0) prime256}
   (pow (z0D * z0D) primeMinusTwo * fromDomain_ x0) % prime256;
   (==) {_ by (canon())}
   (fromDomain_ x0 * pow (z0D * z0D) primeMinusTwo) % prime256;
  };


  calc (==)
  {
     (pow (fromDomain_ z0 * fromDomain_ z0 * fromDomain_ z0) primeMinusTwo % prime256 * fromDomain_ y0) % prime256;
     (==) {lemma_mod_mul_distr_l (pow (fromDomain_ z0 * fromDomain_ z0 * fromDomain_ z0) primeMinusTwo) (fromDomain_ y0) prime256}
     (pow (z0D * z0D * z0D) primeMinusTwo * fromDomain_ y0) % prime256;
     (==) {_ by (canon())}
     (fromDomain_ y0 * pow (z0D * z0D * z0D) primeMinusTwo) % prime256; 
  };

  calc (==)
  {
    (pow ((z0D * r) * (z0D * r) * (z0D * r)) primeMinusTwo % prime256 * (fromDomain_ y0 * ((r * r % prime256) * r % prime256) % prime256)) % prime256;
    (==) {_ by (canon())}
    (pow (z0D * z0D * z0D * (r * r * r)) primeMinusTwo % prime256 * (fromDomain_ y0 * ((r * r % prime256) * r % prime256) % prime256)) % prime256;
    (==) {}
    (pow (z0D * z0D * z0D * rrr) primeMinusTwo % prime256 * (fromDomain_ y0 * ((r * r % prime256) * r % prime256) % prime256)) % prime256; 
    (==) {lemma_mod_mul_distr_l (r * r) r prime256}
    (pow (z0D * z0D * z0D * rrr) primeMinusTwo % prime256 * (fromDomain_ y0 * (r * r * r % prime256) % prime256)) % prime256; 
    (==) {}
    (pow (z0D * z0D * z0D * rrr) primeMinusTwo % prime256 * (fromDomain_ y0 * (rrr % prime256) % prime256)) % prime256; 
    (==) {lemma_mod_mul_distr_r (fromDomain_ y0) rrr prime256}
    (pow (z0D * z0D * z0D * rrr) primeMinusTwo % prime256 * (fromDomain_ y0 * rrr % prime256)) % prime256; 
    (==) {lemma_mod_mul_distr_l (pow (z0D * z0D * z0D * rrr) primeMinusTwo) (fromDomain_ y0 * rrr % prime256) prime256}
    (pow (z0D * z0D * z0D * rrr) primeMinusTwo * (fromDomain_ y0 * rrr % prime256)) % prime256; 
    (==) {power_distributivity_2 (z0D * z0D * z0D) rrr primeMinusTwo}
    (pow (z0D * z0D * z0D) primeMinusTwo * pow rrr primeMinusTwo * (fromDomain_ y0 * rrr % prime256)) % prime256; 
    (==) {lemma_mod_mul_distr_r (pow (z0D * z0D * z0D) primeMinusTwo * pow rrr primeMinusTwo) (fromDomain_ y0 * rrr) prime256}
    (pow (z0D * z0D * z0D) primeMinusTwo * pow rrr primeMinusTwo * (fromDomain_ y0 * rrr)) % prime256; 
    (==) { _ by (canon())}
    (fromDomain_ y0 * pow (z0D * z0D * z0D) primeMinusTwo * (pow rrr primeMinusTwo * rrr)) % prime256; 
    (==) {power_one2 rrr}
    (fromDomain_ y0 * pow (z0D * z0D * z0D) primeMinusTwo * (pow rrr primeMinusTwo * pow rrr 1)) % prime256; 
    (==) {pow_plus rrr primeMinusTwo 1}
    (fromDomain_ y0 * pow (z0D * z0D * z0D) primeMinusTwo * (pow rrr primeMinusOne)) % prime256; 
    (==) {assume (pow rrr primeMinusOne == FStar.Math.Fermat.pow rrr primeMinusOne)}
    (fromDomain_ y0 * pow (z0D * z0D * z0D) primeMinusTwo * (FStar.Math.Fermat.pow rrr primeMinusOne)) % prime256; 
    (==) {lemma_mod_mul_distr_r (fromDomain_ y0 * pow (z0D * z0D * z0D) primeMinusTwo) (FStar.Math.Fermat.pow rrr primeMinusOne) prime256}
    (fromDomain_ y0 * pow (z0D * z0D * z0D) primeMinusTwo * (FStar.Math.Fermat.pow rrr primeMinusOne % prime256)) % prime256; 
    (==) {FStar.Math.Fermat.fermat_alt prime256 rrr}
    (fromDomain_ y0 * pow (z0D * z0D * z0D) primeMinusTwo) % prime256; 
 };


  calc (==)
  {
    (pow (z0D * z0D) primeMinusTwo * pow r (2 * primeMinusTwo) % prime256 *  (fromDomain_ x0 * (r * r % prime256) % prime256)) % prime256;
    (==) {lemma_mod_mul_distr_r (fromDomain_ x0) (r * r) prime256}
    (((pow (z0D * z0D) primeMinusTwo * pow r (2 * primeMinusTwo)) % prime256) * ((fromDomain_ x0 * (r * r)) % prime256)) % prime256;
    (==) {lemma_mod_mul_distr_r (((pow (z0D * z0D) primeMinusTwo * pow r (2 * primeMinusTwo)) % prime256)) (fromDomain_ x0 * (r * r)) prime256}
    (((pow (z0D * z0D) primeMinusTwo * pow r (2 * primeMinusTwo)) % prime256) * (fromDomain_ x0 * (r * r))) % prime256;
    (==) {lemma_mod_mul_distr_l ((pow (z0D * z0D) primeMinusTwo * pow r (2 * primeMinusTwo))) (fromDomain_ x0 * (r * r)) prime256}
    (pow (z0D * z0D) primeMinusTwo * pow r (2 * primeMinusTwo) * (fromDomain_ x0 * (r * r))) % prime256;
    (==) {_ by (canon())}
    (pow (z0D * z0D) primeMinusTwo * pow r (2 * primeMinusTwo) * fromDomain_ x0 * (r * r)) % prime256;
    (==) {lemma_pow2 r}
    (pow (z0D * z0D) primeMinusTwo * pow r (2 * primeMinusTwo) * fromDomain_ x0 * pow r 2) % prime256;
    (==) {_ by (canon())}
    (fromDomain_ x0 * pow (z0D * z0D) primeMinusTwo * (pow r (2 * primeMinusTwo)  * pow r 2)) % prime256;
    (==) {pow_plus r (2 * primeMinusTwo) 2}
    (fromDomain_ x0 * pow (z0D * z0D) primeMinusTwo * (pow r (2 * primeMinusOne))) % prime256;
    (==) {lemma_pow_double r primeMinusOne}
    ((fromDomain_ x0 * pow (z0D * z0D) primeMinusTwo) * (pow (r * r) primeMinusOne)) % prime256;
    (==) {lemma_mod_mul_distr_r (fromDomain_ x0 * pow (z0D * z0D) primeMinusTwo) (pow (r * r) primeMinusOne) prime256}
    ((fromDomain_ x0 * pow (z0D * z0D) primeMinusTwo) * (pow (r * r) primeMinusOne % prime256)) % prime256;
    (==) {assume (Math.Fermat.pow (r * r) primeMinusOne == pow (r * r) primeMinusOne)}
    ((fromDomain_ x0 * pow (z0D * z0D) primeMinusTwo) * (Math.Fermat.pow (r * r) primeMinusOne % prime256)) % prime256;
    (==) {FStar.Math.Fermat.fermat_alt prime256 (r * r)}
    ((fromDomain_ x0 * pow (z0D * z0D) primeMinusTwo)) % prime256; }






let basePointRandomisation result r = 
  push_frame(); 
    let rTemp = create (size 4) (u64 0) in 
    let h0 = ST.get() in 

    let x = sub result (size 0) (size 4) in 
    let y = sub result (size 4) (size 4) in
    let z = sub result (size 8) (size 4) in 

    montgomery_multiplication_buffer z r z;
    montgomery_square_buffer r rTemp;
    montgomery_multiplication_buffer x rTemp x;
    montgomery_multiplication_buffer rTemp r rTemp;
    montgomery_multiplication_buffer y rTemp y;
    let h6 = ST.get() in 
  pop_frame();

  lemma_bp_random (as_nat h0 x) (as_nat h0 y) (as_nat h0 z) (fromDomain_ (as_nat h0 r)) (as_nat h6 x) (as_nat h6 y) (as_nat h6 z);
  admit()
