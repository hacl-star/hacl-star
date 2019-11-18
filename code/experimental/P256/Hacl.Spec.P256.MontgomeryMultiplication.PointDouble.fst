module Hacl.Spec.P256.MontgomeryMultiplication.PointDouble

open Lib.IntTypes
open FStar.Math.Lemmas
open FStar.Math.Lib
open Hacl.Spec.P256.Lemmas
open Hacl.Spec.P256.Definitions
open Hacl.Spec.P256.Core
open Lib.Sequence
open Hacl.Spec.P256.Core
open Hacl.Spec.P256.MontgomeryMultiplication
open Lib.Loops
open FStar.Mul
open Hacl.Spec.P256


#set-options "--z3rlimit 300" 

let prime = prime256

val computeS:
  px: felem_seq_prime -> 
  py: felem_seq_prime -> 
  Lemma ((
    let pxD = fromDomain_ (felem_seq_as_nat px) in 
    let pyD = fromDomain_(felem_seq_as_nat py) in 
    let s = mm_byFour_seq (montgomery_multiplication_seq px (montgomery_multiplication_seq py py)) in 
    fromDomain_(felem_seq_as_nat s) == (4 * pxD * pyD * pyD) % prime)
 )   

let computeS px py = 
  let open FStar.Tactics in 
  let open FStar.Tactics.Canon in 
  let pxD = fromDomain_ (felem_seq_as_nat px) in 
  let pyD = fromDomain_ (felem_seq_as_nat py) in 
  let a = montgomery_multiplication_seq py py in 
  let b = montgomery_multiplication_seq px a in 
    lemma_mod_mul_distr_r pxD (pyD * pyD) prime;  
  let s = mm_byFour_seq b in 
  
  assert_by_tactic (pxD * (pyD * pyD) == pxD * pyD * pyD) canon;
  assert_by_tactic (4 * (pxD * pyD * pyD) == 4 * pxD * pyD * pyD) canon;
  
  lemma_mod_mul_distr_r 4 (pxD * pyD * pyD) prime


val computeM: px: felem_seq_prime -> 
  pz: felem_seq_prime -> 
  Lemma (
    (
      let pxD = fromDomain_ (felem_seq_as_nat px) in 
      let pzD = fromDomain_(felem_seq_as_nat pz) in 
      let m = felem_add_seq (mm_byMinusThree_seq(mm_quatre_seq pz)) (mm_byThree_seq(montgomery_multiplication_seq px px)) in  
      fromDomain_(felem_seq_as_nat m) = (((-3) * pzD * pzD * pzD * pzD + 3 * pxD * pxD) % prime)
    )
) 

let computeM px pz = 
  let open FStar.Tactics in 
  let open FStar.Tactics.Canon in 

  let pxD = fromDomain_ (felem_seq_as_nat px) in 
  let pzD = fromDomain_ (felem_seq_as_nat pz) in 
  let a = mm_quatre_seq pz in 
  let b = mm_byMinusThree_seq a in 
  let c = montgomery_multiplication_seq px px in 
  let d = mm_byThree_seq c in
  let e = felem_add_seq b d in 

  assert_by_tactic ((-3) * (pzD * pzD * pzD * pzD) == (-3) * pzD * pzD * pzD * pzD) canon;
  assert_by_tactic (3 * (pxD * pxD) == 3 * pxD * pxD) canon;

  lemma_mod_mul_distr_r (-3) (pzD * pzD * pzD * pzD) prime;
  lemma_mod_mul_distr_r 3 (pxD * pxD) prime;
  modulo_distributivity ((-3) * pzD * pzD * pzD * pzD) (3 * pxD * pxD) prime

val computeZ3: 
  py: felem_seq_prime -> 
  pz: felem_seq_prime-> 
  Lemma (
    let z3 = mm_byTwo_seq(montgomery_multiplication_seq py pz) in 
    let pyD = fromDomain_ (felem_seq_as_nat py) in 
    let pzD = fromDomain_(felem_seq_as_nat pz) in 
    fromDomain_(felem_seq_as_nat z3) = 2 * pyD * pzD % prime)

let computeZ3 py pz = 
  let open FStar.Tactics in 
  let open FStar.Tactics.Canon in 

  let pyD = fromDomain_ (felem_seq_as_nat py) in 
    lemmaFromDomain (felem_seq_as_nat py);
  let pzD = fromDomain_ (felem_seq_as_nat pz) in 
    lemmaFromDomain (felem_seq_as_nat pz);
 
  let a = montgomery_multiplication_seq py pz in 
  let b = mm_byTwo_seq a in 
      assert(felem_seq_as_nat a = toDomain_ (fromDomain_ (felem_seq_as_nat py) * fromDomain_ (felem_seq_as_nat pz) % prime));
      lemmaToDomainAndBackIsTheSame (fromDomain_ (felem_seq_as_nat py) * fromDomain_ (felem_seq_as_nat pz) % prime);
      assert(felem_seq_as_nat b = toDomain_ (2 * (fromDomain_ (felem_seq_as_nat py) * fromDomain_ (felem_seq_as_nat pz) % prime) % prime));
      lemma_mod_mul_distr_r 2 (fromDomain_ (felem_seq_as_nat py) * fromDomain_ (felem_seq_as_nat pz)) prime;
  assert_by_tactic (2 * (pyD * pzD) = 2 * pyD * pzD) canon;
  lemmaToDomainAndBackIsTheSame (2 * pyD * pzD % prime)


#reset-options "--z3rlimit 100" 
val lemma_xToSpecification: pxD: nat -> pyD: nat -> pzD: nat -> 
  s: felem_seq{fromDomain_ (felem_seq_as_nat s) = 4 * pxD * pyD * pyD % prime} -> 
  m: felem_seq{fromDomain_ (felem_seq_as_nat m) = (((-3) * pzD * pzD * pzD * pzD + 3 * pxD * pxD)) % prime} -> 
  x3: felem_seq{
    (let mD = fromDomain_ (felem_seq_as_nat m) in 
    let sD = fromDomain_ (felem_seq_as_nat s) in 
    fromDomain_(felem_seq_as_nat x3) = (mD * mD - 2*sD) % prime)} -> 
  Lemma (
    (let (xN, yN, zN) = _point_double (pxD, pyD, pzD) in 
      fromDomain_(felem_seq_as_nat x3) = xN)
    )

let lemma_xToSpecification pxD pyD pzD s m x3  = ()


val lemma_yToSpecification: pxD: nat -> pyD: nat -> pzD: nat ->
  s: felem_seq{felem_seq_as_nat s = toDomain_ (4 * pxD * pyD * pyD % prime)} -> 
  m: felem_seq{felem_seq_as_nat m = toDomain_ ((((-3) * pzD * pzD * pzD * pzD + 3 * pxD * pxD) % prime))} ->
  x3: felem_seq{(let mD = fromDomain_ (felem_seq_as_nat m) in let sD = fromDomain_ (felem_seq_as_nat s) in 
    fromDomain_(felem_seq_as_nat x3) = (mD * mD - 2*sD) % prime)} -> 
  y3: felem_seq{(let mD = fromDomain_ (felem_seq_as_nat m) in let sD = fromDomain_ (felem_seq_as_nat s) in 
    let x3D = fromDomain_ (felem_seq_as_nat x3) in 
    fromDomain_ (felem_seq_as_nat y3) = ((mD * (sD - x3D) - (8 * pyD * pyD * pyD * pyD)) % prime))} -> 
  Lemma(let (xN, yN, zN) = _point_double (pxD, pyD, pzD) in  fromDomain_(felem_seq_as_nat y3) = yN)  

let lemma_yToSpecification pxD pyD pzD s m x3 y3 = ()


val lemma_zToSpecification: pxD: nat ->  pyD: nat -> pzD: nat -> 
  z3: felem_seq{fromDomain_(felem_seq_as_nat z3) = 2 * pyD * pzD % prime} -> 
  Lemma (
    let (xN, yN, zN) = _point_double (pxD, pyD, pzD) in 
    fromDomain_(felem_seq_as_nat z3) = zN
  )

let lemma_zToSpecification pxD pyD pzD z3 = ()


noextract
val copy_point_seq: p: point_seq -> Tot (r: point_seq{p == r})

#reset-options "--z3rlimit 100" 
let copy_point_seq p = p


noextract
val point_double_compute_s_m_seq:  
  p: point_prime -> 
  Tot (r: tuple2 felem_seq felem_seq{let s, m = r in 
      let px = Lib.Sequence.sub p 0 4 in 
      let py = Lib.Sequence.sub p 4 4 in 
      let pz = Lib.Sequence.sub p 8 4 in   
      let pxD = fromDomain_ (felem_seq_as_nat px) in 
      let pyD = fromDomain_ (felem_seq_as_nat py) in 
      let pzD = fromDomain_ (felem_seq_as_nat pz) in 
      fromDomain_(felem_seq_as_nat s) == 4 * pxD * pyD * pyD % prime /\
      fromDomain_(felem_seq_as_nat m) == (((-3) * pzD * pzD * pzD * pzD + 3 * pxD * pxD) % prime)
  })

let point_double_compute_s_m_seq p = 
  let px = Lib.Sequence.sub p 0 4 in 
  let py = Lib.Sequence.sub p 4 4 in 
  let pz = Lib.Sequence.sub p 8 4 in 

  let yy = montgomery_multiplication_seq py py in 
  let xyy = montgomery_multiplication_seq px yy in 
  let s = mm_byFour_seq xyy in 
 
  let zzzz = mm_quatre_seq pz in 
  let minThreeZzzz = mm_byMinusThree_seq zzzz in 
  let xx = montgomery_multiplication_seq px px in 
  let threeXx = mm_byThree_seq xx in 
  let m = felem_add_seq minThreeZzzz threeXx in 
  computeS px py;
  computeM px pz;
  
  (s, m)


noextract
val point_double_compute_x3_seq: 
  s: felem_seq_prime ->  
  m: felem_seq_prime -> 
  Tot (x3: felem_seq_prime {
    let mD = fromDomain_ (felem_seq_as_nat m) in 
    let sD = fromDomain_ (felem_seq_as_nat s) in 
    fromDomain_ (felem_seq_as_nat x3) = ((mD * mD - 2 * sD) % prime)}
  )

let point_double_compute_x3_seq s m = 
  let twoS = mm_byTwo_seq s in 
  let mm = montgomery_multiplication_seq m m in 
  let x3 = felem_sub_seq mm twoS in 
  lemma_minus_distr ((fromDomain_ (felem_seq_as_nat m)) * (fromDomain_ (felem_seq_as_nat m))) (2 * (fromDomain_ (felem_seq_as_nat s))); 
  x3


noextract
val point_double_compute_y3_seq: 
  p_y: felem_seq_prime -> 
  x3: felem_seq_prime-> 
  s: felem_seq_prime -> 
  m: felem_seq_prime -> 
  Tot (y3: felem_seq_prime {
   let mD = fromDomain_ (felem_seq_as_nat m) in 
   let sD = fromDomain_ (felem_seq_as_nat s) in 
   let x3D = fromDomain_ (felem_seq_as_nat x3) in 
   let pyD = fromDomain_ (felem_seq_as_nat p_y) in
   fromDomain_ (felem_seq_as_nat y3) = ((mD * (sD - x3D) - (8 * pyD * pyD * pyD * pyD))% prime)
  })

let point_double_compute_y3_seq py x3 s m = 
    let open FStar.Tactics in 
    let open FStar.Tactics.Canon in 

    let yyyy = mm_quatre_seq py in 
    let eightYyyy = mm_byEight_seq yyyy in 
    let sx3 = felem_sub_seq s x3 in 
    let msx3 = montgomery_multiplication_seq m sx3 in 
    let y3 = felem_sub_seq msx3 eightYyyy in 
    
    let mD = fromDomain_ (felem_seq_as_nat m) in 
    let sD = fromDomain_ (felem_seq_as_nat s) in 
    let x3D = fromDomain_ (felem_seq_as_nat x3) in 
    let pyD = fromDomain_ (felem_seq_as_nat py) in 

    assert_by_tactic (8 * (pyD * pyD * pyD * pyD) == 8 * pyD * pyD * pyD * pyD) canon;

    lemma_mod_mul_distr_r mD (sD - x3D) prime;
    lemma_mod_mul_distr_r 8 (pyD * pyD * pyD * pyD) prime;
    lemma_minus_distr (mD * (sD - x3D)) (8 * pyD * pyD * pyD * pyD);
    y3


noextract
val point_double_seq: p: point_prime -> 
  Tot (r: point_prime  {
    let x3, y3, z3 = felem_seq_as_nat(sub r 0 4), felem_seq_as_nat(sub r 4 4), felem_seq_as_nat(sub r 8 4) in 
    let x, y, z = felem_seq_as_nat(sub p 0 4), felem_seq_as_nat(sub p 4 4) , felem_seq_as_nat(sub p 8 4) in 
    
    let xD, yD, zD = fromDomainPoint(x, y, z) in 
    let x3D, y3D, z3D = fromDomainPoint (x3, y3, z3) in
    let (xN, yN, zN) = _point_double (xD, yD, zD) in 
    x3D = xN /\ y3D = yN /\ z3D = zN
  }) 


let point_double_seq p =
  let open FStar.Tactics in 
  let open FStar.Tactics.Canon in 

  let px = Lib.Sequence.sub p 0 4 in 
  let py = Lib.Sequence.sub p 4 4 in 
  let pz = Lib.Sequence.sub p 8 4 in 

  let (s, m) = point_double_compute_s_m_seq p in 
  let x3 = point_double_compute_x3_seq s m in 
  let y3 = point_double_compute_y3_seq py x3 s m in
  let pypz = montgomery_multiplication_seq py pz in 
  let z3 = mm_byTwo_seq pypz in 
  
  let r = concat (concat x3 y3) z3 in
  
  computeZ3 py pz;
  lemma_xToSpecification (fromDomain_ (felem_seq_as_nat px)) (fromDomain_ (felem_seq_as_nat py)) (fromDomain_ (felem_seq_as_nat pz)) s m x3;
  lemma_yToSpecification (fromDomain_ (felem_seq_as_nat px)) (fromDomain_ (felem_seq_as_nat py)) (fromDomain_ (felem_seq_as_nat pz)) s m x3 y3;
  lemma_zToSpecification (fromDomain_ (felem_seq_as_nat px)) (fromDomain_ (felem_seq_as_nat py)) (fromDomain_ (felem_seq_as_nat pz)) z3;
  r
 
