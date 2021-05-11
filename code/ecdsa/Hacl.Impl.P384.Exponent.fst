module Hacl.Impl.P384.Exponent

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer

open FStar.Mul

open Hacl.Spec.EC.Definition
open Spec.ECC
open Spec.ECC.Curves
open Hacl.Impl.EC.MontgomeryMultiplication
open Hacl.Impl.EC.LowLevel

open FStar.Math.Lemmas
open Hacl.EC.Lemmas

open FStar.Tactics 
open FStar.Tactics.Canon 

open Hacl.Spec.MontgomeryMultiplication


#set-options "--z3rlimit 100 --ifuel 0 --fuel 0"

let fromDomain__ = fromDomain_ #P384 #DH
let toDomain__ = toDomain_ #P384 #DH

let as_nat_ h1 result = as_nat P384 h1 result

val lemma_mod_mul_distr: a: nat -> b: nat -> prime: pos -> Lemma 
  ((a % prime * (b % prime)) % prime ==  a * b % prime)

let lemma_mod_mul_distr a b prime = 
  lemma_mod_mul_distr_l a (b % prime) prime;
  lemma_mod_mul_distr_r a b prime


val lemma_mod_mul_distr1: a: nat -> b: nat -> c: nat -> prime: pos -> Lemma
  ((pow a b % prime) * (pow a c % prime) % prime == pow a (b + c) % prime)

let lemma_mod_mul_distr1 a b c prime = 
  lemma_mod_mul_distr (pow a b) (pow a c) prime;
  pow_plus a b c

inline_for_extraction noextract
val exponent0: t: felem P384 -> t0: felem P384 -> t1: felem P384 -> t2: felem P384 -> t3: felem P384 ->  Stack unit 
  (requires fun h -> live h t /\ live h t0 /\ live h t1 /\ live h t2 /\ live h t3 /\
    LowStar.Monotonic.Buffer.all_disjoint [loc t; loc t0; loc t1; loc t2; loc t3] /\
    as_nat_ h t < prime384)
  (ensures fun h0 _ h1 -> modifies (loc t0 |+| loc t1 |+| loc t2 |+| loc t3) h0 h1 /\
    as_nat_ h1 t < prime384 /\ as_nat_ h1 t0 < prime384 /\ as_nat_ h1 t1 < prime384 /\ as_nat_ h1 t2 < prime384 /\ 
    as_nat_ h1 t3 < prime384 /\ (
    let tD = fromDomain__ (as_nat_ h0 t) in 
    as_nat_ h1 t0 = toDomain__ (pow tD 7 % prime384) /\
    as_nat_ h1 t1 = toDomain__ (pow tD 63 % prime384) /\
    as_nat_ h1 t2 = toDomain__ (pow tD (126 * pow2 5 + 63) % prime384) /\
    as_nat_ h1 t3 = toDomain__ (pow tD (63 * (pow2 7 + 2) *  pow2 11)  % prime384)))


let exponent0 t t0 t1 t2 t3 = 
  let h0 = ST.get() in 
(* _10     = sq(t) *)
(* t0 = _10  *)
  montgomery_square_buffer_dh #P384 t t0;
    let h1 = ST.get() in 

(* _11     = m(t, _10) *)
  montgomery_multiplication_buffer_dh #P384 t t0 t0;
    let h2 = ST.get() in 
(* t0 = _11*)

(* _110    = sq(_11) *)
  montgomery_square_buffer_dh #P384 t0 t0;
    let h3 = ST.get() in 
(* t0 = _110 *)  

(* _111    = m(t, _110) *)
  montgomery_multiplication_buffer_dh #P384 t t0 t0;
    let h4 = ST.get() in 
(* t0 = _111 *)  

(* _111000 (t1) = n_sq(_111, 3) *)
  montgomery_square_buffer_dh #P384 t0 t1;
    let h5 = ST.get() in 
    
  fsquarePowN_dh #P384 (size 2) t1;
    let h6 = ST.get() in 
(* t1 = sq _111 *)
(* t1 = n_sq _111 3  *)
(* t1 = _111000 *)

(* _111111 = m(_111,  _111000) *)
  montgomery_multiplication_buffer_dh #P384 t0 t1 t1;  
    let h7 = ST.get() in 
(* t1 = t0 * t1 *)
(* t1 = _111 * _111000 *)
(* t1 = _111111 *)

(* x12     = m(n_sq(_111111, 6), _111111) *)
  montgomery_square_buffer_dh #P384 t1 t2;
    let h8 = ST.get() in 

  fsquarePowN_dh #P384 (size 5) t2 ;
    let h9 = ST.get() in 
  montgomery_multiplication_buffer_dh #P384 t2 t1 t2;
    let h10 = ST.get() in 
(* t2 = x12 *)
  
  (* x24     = m(n_sq(x12 , 12), x12) *)
  montgomery_square_buffer_dh #P384 t2 t3;
    let h11 = ST.get() in 
    
  fsquarePowN_dh #P384 (size 11) t3 ;
    let h12 = ST.get() in 
    
(* t2 = x24*) 

  let tD = fromDomain__ (as_nat_ h0 t) in
  Hacl.EC.Lemmas.power_one_2 tD;
  
  assert(as_nat_ h1 t0 = toDomain__ (tD * tD % prime384));
  assert(as_nat_ h3 t0 = toDomain__ (fromDomain__ (as_nat_ h2 t0) * fromDomain__ (as_nat_ h2 t0) % prime384));
  assert(as_nat_ h4 t0 = toDomain__ (tD * fromDomain__ (as_nat_ h3 t0) % prime384));
  assert(as_nat_ h5 t1 = toDomain__ (fromDomain__ (as_nat_ h4 t0) * fromDomain__ (as_nat_ h4 t0) % prime384));
  assert(as_nat_ h6 t1 = toDomain__ (pow (fromDomain__ (as_nat_ h5 t1)) 4 % prime384));
  
  calc (==) {
    as_nat_ h2 t0;
    (==) {}
    toDomain__ (tD * (pow tD 1 * pow tD 1 % prime384) % prime384);
    (==) {pow_plus tD 1 1}
    toDomain__ (tD * (pow tD 2 % prime384) % prime384);
    (==) {lemma_mod_mul_distr_r tD (pow tD 2) prime384}
    toDomain__ (pow tD 1 * pow tD 2 % prime384);
    (==) {pow_plus tD 1 2}
    toDomain__ (pow tD 3 % prime384);};

  calc (==) {
    as_nat_ h3 t0;
    (==) {}
    toDomain__ ((pow tD 3 % prime384) * (pow tD 3 % prime384) % prime384); 
    (==) {lemma_mod_mul_distr_l (pow tD 3) (pow tD 3 % prime384) prime384; 
      lemma_mod_mul_distr_l (pow tD 3) (pow tD 3) prime384}
    toDomain__ (pow tD 3 * pow tD 3 % prime384);
    (==) {pow_plus tD 3 3}
    toDomain__ (pow tD 6 % prime384);};

  calc (==) {
    as_nat_ h4 t0;
    (==) {}
    toDomain__ (tD * (pow tD 6 % prime384) % prime384);
    (==) {lemma_mod_mul_distr_r tD (pow tD 6) prime384}
    toDomain__ (pow tD 1 * pow tD 6 % prime384);
    (==) {pow_plus tD 1 6}
    toDomain__ (pow tD 7 % prime384);};

  calc (==) {
    as_nat_ h5 t1;
    (==) {}
    toDomain__ (pow tD 7 % prime384 * (pow tD 7 % prime384) % prime384);
    (==) {lemma_mod_mul_distr (pow tD 7) (pow tD 7) prime384}
    toDomain__ (pow tD 7 * pow tD 7 % prime384);
    (==) {pow_plus tD 7 7}
    toDomain__ (pow tD 14 % prime384); };

  calc (==) {
    as_nat_ h6 t1;
    (==) {}
    toDomain__ (pow (pow tD 14 % prime384) 4 % prime384);
    (==) {power_distributivity (pow tD 14) 4 prime384}
    toDomain__ (pow (pow tD 14) 4 % prime384);
    (==) {power_mult tD 14 4}
    toDomain__ (pow tD 56 % prime384); };

  calc (==) {
    as_nat_ h7 t1;
    (==) {}
    toDomain__ ((pow tD 7 % prime384) * (pow tD 56 % prime384) % prime384);
    (==) {lemma_mod_mul_distr (pow tD 7) (pow tD 56) prime384}
    toDomain__ ((pow tD 7) * (pow tD 56) % prime384);
    (==) {pow_plus tD 7 56}
    toDomain__ (pow tD 63 % prime384);};

  calc (==) {
    as_nat_ h8 t2;
    (==) {}
    toDomain__ ((pow tD 63 % prime384) * (pow tD 63 % prime384) % prime384);
    (==) {lemma_mod_mul_distr1 tD 63 63 prime384}
    toDomain__ (pow tD 126 % prime384);};

  calc (==) {
    as_nat_ h9 t2;
    (==) {}
    toDomain__ (pow (pow tD 126 % prime384) (pow2 5) % prime384);
    (==) {power_distributivity (pow tD 126) (pow2 5) prime384}
    toDomain__ (pow (pow tD 126) (pow2 5) % prime384);
    (==) {power_mult tD 126 (pow2 5)}
    toDomain__ (pow tD (126 * pow2 5) % prime384);};  

  calc (==) {
    as_nat_ h10 t2;
    (==) {}
    toDomain__ (pow tD (126 * pow2 5) % prime384 * (pow tD 63 % prime384) % prime384);
    (==) {lemma_mod_mul_distr1 tD (126 * pow2 5) 63 prime384}
    toDomain__ (pow tD (126 * pow2 5 + 63) % prime384);};

  calc (==) {
    as_nat_ h11 t3;
    (==) {}
    toDomain__ (pow tD (126 * pow2 5 + 63) % prime384 * (pow tD (126 * pow2 5 + 63) % prime384) % prime384);
    (==) {lemma_mod_mul_distr1 tD (126 * pow2 5 + 63) (126 * pow2 5 + 63) prime384}
    toDomain__ (pow tD (4 * 63 * pow2 5 + 2 * 63) % prime384);
    (==) {assert_by_tactic (4 * 63 * pow2 5 == 63 * (4 * pow2 5)) canon}
    toDomain__ (pow tD (63 * (pow2 2 * pow2 5) + 2 * 63) % prime384);
    (==) {pow2_plus 2 5}
    toDomain__ (pow tD (63 * (pow2 7 + 2)) % prime384);};

  let pow2_11 = pow2 11 in 
  
  calc (==) {
    as_nat_ h12 t3;
    (==) {}
    toDomain__ (pow (pow tD (63 * (pow2 7 + 2)) % prime384) pow2_11  % prime384);
    (==) {power_distributivity (pow tD (63 * (pow2 7 + 2))) pow2_11 prime384}
    toDomain__ (pow (pow tD (63 * (pow2 7 + 2))) pow2_11  % prime384);
    (==) {power_mult tD (63 * (pow2 7 + 2)) pow2_11}
    toDomain__ (pow tD (63 * (pow2 7 + 2) *  pow2_11)  % prime384); }


val lemma_exp1_4_2: t1D: nat -> t2D : nat -> t3D: nat -> prime384: pos  -> Lemma (    
  toDomain__ ((pow t2D (pow2 6) * pow t3D (pow2 6) * t1D) % prime384 * ((pow t2D (pow2 6) * pow t3D (pow2 6) * t1D) % prime384) % prime384) == toDomain__ ((pow t2D (pow2 7) * pow t3D (pow2 7) * pow t1D 2) % prime384))
  
let lemma_exp1_4_2 t1D t2D t3D prime384 = 

  calc (==) {
    toDomain__ ((pow t2D (pow2 6) * pow t3D (pow2 6) * t1D) % prime384 * ((pow t2D (pow2 6) * pow t3D (pow2 6) * t1D) % prime384) % prime384);
     (==) {lemma_mod_mul_distr (pow t2D (pow2 6) * pow t3D (pow2 6) * t1D) (pow t2D (pow2 6) * pow t3D (pow2 6) * t1D) prime384}
     toDomain__ ((pow t2D (pow2 6) * pow t3D (pow2 6) * t1D) * (pow t2D (pow2 6) * pow t3D (pow2 6) * t1D) % prime384);
     (==) {assert_by_tactic ((pow t2D (pow2 6) * pow t3D (pow2 6) * t1D) * (pow t2D (pow2 6) * pow t3D (pow2 6) * t1D) == 
       (pow t2D (pow2 6) * pow t2D (pow2 6)) * (pow t3D (pow2 6) * pow t3D (pow2 6)) * (t1D * t1D)) canon}
     toDomain__ ((pow t2D (pow2 6) * pow t2D (pow2 6)) * (pow t3D (pow2 6) * pow t3D (pow2 6)) * (t1D * t1D) % prime384);
     (==) {pow_plus t2D (pow2 6) (pow2 6); pow_plus t3D (pow2 6) (pow2 6); power_one_2 t1D}
     toDomain__ (pow t2D (2 * pow2 6) * pow t3D (2 * pow2 6) * (pow t1D 1 * pow t1D 1) % prime384);
     (==) {pow2_double_sum 6; pow_plus t1D 1 1}
     toDomain__ ((pow t2D (pow2 7) * pow t3D (pow2 7) * pow t1D 2) % prime384);}


val lemma_exp1_5_2: tD: nat -> t1D: nat -> t2D : nat -> t3D: nat -> prime384: pos -> Lemma (
  toDomain__ ((pow t2D (pow2 7) * pow t3D (pow2 7) * pow t1D 2 * tD % prime384) * (pow t2D (pow2 7) * pow t3D (pow2 7) * pow t1D 2 * tD % prime384) % prime384) ==
    toDomain__ ((pow t2D (pow2 8) * pow t3D (pow2 8) * pow t1D (pow2 2) * pow tD 2) % prime384))


let lemma_exp1_5_2 tD t1D t2D t3D prime384 = 
  calc (==) {
    toDomain__ ((pow t2D (pow2 7) * pow t3D (pow2 7) * pow t1D 2 * tD % prime384) * (pow t2D (pow2 7) * pow t3D (pow2 7) * pow t1D 2 * tD % prime384) % prime384);
     (==) {lemma_mod_mul_distr (pow t2D (pow2 7) * pow t3D (pow2 7) * pow t1D 2 * tD) (pow t2D (pow2 7) * pow t3D (pow2 7) * pow t1D 2 * tD) prime384}
     toDomain__ ((pow t2D (pow2 7) * pow t3D (pow2 7) * pow t1D 2 * tD) * (pow t2D (pow2 7) * pow t3D (pow2 7) * pow t1D 2 * tD) % prime384);
     (==) {assert_by_tactic (((pow t2D (pow2 7) * pow t3D (pow2 7) * pow t1D 2 * tD) * (pow t2D (pow2 7) * pow t3D (pow2 7) * pow t1D 2 * tD)) == (pow t2D (pow2 7) * pow t2D (pow2 7)) * (pow t3D (pow2 7) * pow t3D (pow2 7)) * (pow t1D 2 * pow t1D 2) * (tD * tD)) canon}
     toDomain__ (((pow t2D (pow2 7) * pow t2D (pow2 7)) * (pow t3D (pow2 7) * pow t3D (pow2 7)) * (pow t1D 2 * pow t1D 2) * (tD * tD)) % prime384);
     (==) {pow_plus t2D (pow2 7) (pow2 7); pow_plus t3D (pow2 7) (pow2 7); pow_plus t1D 2 2; power_one_2 tD}
     toDomain__ (((pow t2D (2 * pow2 7)) * (pow t3D (2 * pow2 7)) * (pow t1D 4) * (pow tD 1 * pow tD 1)) % prime384);
     (==) {pow2_double_sum 7; pow_plus tD 1 1}
     toDomain__ (((pow t2D (pow2 8)) * (pow t3D (pow2 8)) * (pow t1D 4) * (pow tD 2)) % prime384);}


val lemma_exp1_8_2: tD: nat -> t1D: nat -> t2D : nat -> t3D: nat -> prime384: pos -> Lemma (
  toDomain__ (((pow t2D (pow2 8) * pow t3D (pow2 8) * pow t1D (pow2 2) * pow tD 3) % prime384) * ((pow t2D (pow2 8) * pow t3D (pow2 8) * pow t1D (pow2 2) * pow tD 3) % prime384) % prime384) == 
  toDomain__ ((pow t2D (pow2 9) * pow t3D (pow2 9) * pow t1D (pow2 3) * pow tD 6) % prime384))

let lemma_exp1_8_2 tD t1D t2D t3D prime384 = 
   calc (==) {
     toDomain__ (((pow t2D (pow2 8) * pow t3D (pow2 8) * pow t1D (pow2 2) * pow tD 3) % prime384) * ((pow t2D (pow2 8) * pow t3D (pow2 8) * pow t1D (pow2 2) * pow tD 3) % prime384) % prime384);
     (==) {lemma_mod_mul_distr (pow t2D (pow2 8) * pow t3D (pow2 8) * pow t1D (pow2 2) * pow tD 3) (pow t2D (pow2 8) * pow t3D (pow2 8) * pow t1D (pow2 2) * pow tD 3) prime384}
     toDomain__ (pow t2D (pow2 8) * pow t3D (pow2 8) * pow t1D (pow2 2) * pow tD 3 * ((pow t2D (pow2 8) * pow t3D (pow2 8) * pow t1D (pow2 2) * pow tD 3)) % prime384);
     (==) {assert_by_tactic ((pow t2D (pow2 8) * pow t3D (pow2 8) * pow t1D (pow2 2) * pow tD 3 * ((pow t2D (pow2 8) * pow t3D (pow2 8) * pow t1D (pow2 2) * pow tD 3))) == (pow t2D (pow2 8) * pow t2D (pow2 8)) * (pow t3D (pow2 8) * pow t3D (pow2 8)) * (pow t1D (pow2 2) * pow t1D (pow2 2)) * (pow tD 3 * pow tD 3)) canon}
     toDomain__ (((pow t2D (pow2 8) * pow t2D (pow2 8)) * (pow t3D (pow2 8) * pow t3D (pow2 8)) * (pow t1D (pow2 2) * pow t1D (pow2 2)) * (pow tD 3 * pow tD 3)) % prime384);
     (==) {pow_plus t2D (pow2 8) (pow2 8); pow_plus t3D (pow2 8) (pow2 8); pow_plus t1D (pow2 2) (pow2 2); pow_plus tD 3 3}
     toDomain__ ((pow t2D (2 * pow2 8) * pow t3D (2 * pow2 8) * pow t1D (2 * pow2 2) * pow tD 6) % prime384);
     (==) {pow2_double_sum 8; pow2_double_sum 2}
     toDomain__ ((pow t2D (pow2 9) * pow t3D (pow2 9) * pow t1D (pow2 3) * pow tD 6) % prime384);}

val lemma_exp1_9_2_: a: nat -> b: nat -> c: nat -> d: nat -> e: pos -> Lemma
   (pow (a * b * c * d) e = pow a e * pow b e * pow c e * pow d e)

let lemma_exp1_9_2_ a b c d  e = 
  power_distributivity_2 (a * b * c) d e;
  power_distributivity_2 (a * b) c e;
  power_distributivity_2 a b e
  


val lemma_exp1_9_2: tD: nat -> t1D: nat -> t2D : nat -> t3D: nat -> prime384: pos -> Lemma (
  toDomain__ (pow ((pow t2D (pow2 9) * pow t3D (pow2 9) * pow t1D (pow2 3) * pow tD 6) % prime384) (pow2 30) % prime384) == 
  toDomain__ (pow t2D (pow2 39) * pow t3D (pow2 39) * pow t1D (pow2 33) * pow tD (3 * pow2 31) % prime384))

let lemma_exp1_9_2 tD t1D t2D t3D prime384 = 
  let pow2_30 = pow2 30 in 
  let pow2_39 = pow2 39 in 
  let pow2_33 = pow2 33 in 
  let pow2_31 = pow2 31 in 
  let a = pow t2D (pow2 9) in 
  let a = pow t3D (pow2 9) in 
  let b = pow t1D (pow2 3) in 
  let c = pow tD 6 in 
  
   calc (==) {
     toDomain__ (pow ((pow t2D (pow2 9) * pow t3D (pow2 9) * pow t1D (pow2 3) * pow tD 6) % prime384) pow2_30 % prime384);
   (==) {power_distributivity (pow t2D (pow2 9) * pow t3D (pow2 9) * pow t1D (pow2 3) * pow tD 6) (pow2_30) prime384}
     toDomain__ (pow (pow t2D (pow2 9) * pow t3D (pow2 9) * pow t1D (pow2 3) * pow tD 6) pow2_30 % prime384);
   (==) {lemma_exp1_9_2_ (pow t2D (pow2 9)) (pow t3D (pow2 9)) (pow t1D (pow2 3)) (pow tD 6) pow2_30}
     toDomain__ (pow (pow t2D (pow2 9)) pow2_30 * pow (pow t3D (pow2 9)) pow2_30 * pow (pow t1D (pow2 3)) pow2_30 * pow (pow tD 6) pow2_30 % prime384);
   (==) {power_mult t2D (pow2 9) pow2_30; power_mult t3D (pow2 9) pow2_30; power_mult t1D (pow2 3) pow2_30; power_mult tD 6 (pow2 30)}
     toDomain__ (pow t2D (pow2 9 * pow2_30) * pow t3D (pow2 9 * pow2_30) * pow t1D (pow2 3 * pow2_30) * pow tD (6 * pow2_30) % prime384);
  (==) {pow2_plus 9 30; pow2_plus 3 30; pow2_plus 1 30}
    toDomain__ (pow t2D pow2_39 * pow t3D pow2_39 * pow t1D pow2_33 * pow tD (3 * pow2_31) % prime384);}


val lemma_exp1_10_2: tD: nat -> t1D: nat -> t2D : nat -> t3D: nat -> prime384: pos -> Lemma (
  toDomain__ ((pow t2D (pow2 39) * pow t3D (pow2 39) * pow t1D (pow2 33) * pow tD (3 * pow2 31) % prime384) * (pow t2D (pow2 7) * pow t3D (pow2 7) * pow t1D 2 * tD % prime384) % prime384) == 
  toDomain__ (pow t2D (pow2 39 + pow2 7) * pow t3D (pow2 39 + pow2 7) * pow t1D (pow2 33 + 2) * pow tD (3 * pow2 31 + 1) % prime384))
    

let lemma_exp1_10_2 tD t1D t2D t3D prime384 = 
  let pow2_31 = pow2 31 in 
  let pow2_33 = pow2 33 in 
  let pow2_39 = pow2 39 in 
  let pow2_46 = pow2 46 in 

  calc (==) {
    toDomain__ ((pow t2D pow2_39 * pow t3D pow2_39 * pow t1D pow2_33 * pow tD (3 * pow2_31) % prime384) * (pow t2D (pow2 7) * pow t3D (pow2 7) * pow t1D 2 * tD % prime384) % prime384);
  (==) {lemma_mod_mul_distr (pow t2D pow2_39 * pow t3D pow2_39 * pow t1D pow2_33 * pow tD (3 * pow2_31)) (pow t2D (pow2 7) * pow t3D (pow2 7) * pow t1D 2 * tD) prime384}
    toDomain__ (pow t2D pow2_39 * pow t3D pow2_39 * pow t1D pow2_33 * pow tD (3 * pow2_31) * (pow t2D (pow2 7) * pow t3D (pow2 7) * pow t1D 2 * tD) % prime384);
  (==) {assert_by_tactic (pow t2D pow2_39 * pow t3D pow2_39 * pow t1D pow2_33 * pow tD (3 * pow2_31) * (pow t2D (pow2 7) * pow t3D (pow2 7) * pow t1D 2 * tD) == 
    (pow t2D pow2_39 * pow t2D (pow2 7)) * (pow t3D pow2_39 * pow t3D (pow2 7)) * (pow t1D pow2_33 * pow t1D 2) * (pow tD (3 * pow2_31) * tD)) canon}
    toDomain__ ((pow t2D pow2_39 * pow t2D (pow2 7)) * (pow t3D pow2_39 * pow t3D (pow2 7)) * (pow t1D pow2_33 * pow t1D 2) * (pow tD (3 * pow2_31) * tD) % prime384);
  (==) {pow_plus t2D pow2_39 (pow2 7); pow_plus t3D pow2_39 (pow2 7); pow_plus t1D pow2_33 2; power_one_2 tD}
    toDomain__ (pow t2D (pow2_39 + pow2 7) * pow t3D (pow2_39 + pow2 7) * pow t1D (pow2_33 + 2) * (pow tD (3 * pow2_31) * pow tD 1) % prime384);
  (==) {pow_plus tD (3 * pow2_31) 1}
    toDomain__ (pow t2D (pow2_39 + pow2 7) * pow t3D (pow2_39 + pow2 7) * pow t1D (pow2_33 + 2) * pow tD (3 * pow2_31 + 1) % prime384);}
  


#set-options "--z3rlimit 300 --ifuel 0 --fuel 0"


inline_for_extraction noextract
val exponent1: t: felem P384 -> t1: felem P384 -> t2: felem P384 -> t3: felem P384 -> t4: felem P384 ->  Stack unit 
  (requires fun h -> live h t /\ live h t1 /\ live h t2 /\ live h t3 /\ live h t4 /\
    LowStar.Monotonic.Buffer.all_disjoint [loc t; loc t1; loc t2; loc t3; loc t4] /\
    as_nat_ h t < prime384 /\ as_nat_ h t1 < prime384 /\ as_nat_ h t2 < prime384 /\ as_nat_ h t3 < prime384)
  (ensures fun h0 _ h1 -> modifies (loc t1 |+| loc t2 |+| loc t3 |+| loc t4) h0 h1 /\ (
    let tD = fromDomain__ (as_nat_ h0 t) in 
    let t1D = fromDomain__ (as_nat_ h0 t1) in 
    let t2D = fromDomain__ (as_nat_ h0 t2) in 
    let t3D = fromDomain__ (as_nat_ h0 t3) in 
    as_nat_ h1 t1 ==  toDomain__ (pow t2D (pow2 6) * pow t3D (pow2 6) * t1D % prime384) /\
    as_nat_ h1 t3 == toDomain__ ((pow t2D (pow2 8) * pow t3D (pow2 8) * pow t1D (pow2 2) * pow tD 3) % prime384) /\
    as_nat_ h1 t4 == toDomain__ (pow t2D (pow2 39 + pow2 7) * pow t3D (pow2 39 + pow2 7) * pow t1D (pow2 33 + 2) * pow tD (3 * pow2 31 + 1) % prime384)
  ))

let exponent1 t t1 t2 t3 t4 = 
    let h0 = ST.get() in 
  montgomery_multiplication_buffer_dh #P384 t2 t3 t2;
    let h1 = ST.get() in 
(* x30     = m(n_sq(x24 , 6) , _111111) *)
  fsquarePowN_dh #P384 (size 6) t2 ;
    let h2 = ST.get() in 
  montgomery_multiplication_buffer_dh #P384 t2 t1 t1;  
    let h3 = ST.get() in 
(* t1 = x30 *)

(* x31     = m(sq(x30), t) *)
  montgomery_square_buffer_dh #P384 t1 t2;
    let h4 = ST.get() in 
  (* fsquarePowN_dh #P384 (size 29) t2 ; *)
  montgomery_multiplication_buffer_dh #P384 t2 t t2;
    let h5 = ST.get() in 
(* t2 = x31 *)

 (* x32     = m(sq(x31), t)  *)
  montgomery_square_buffer_dh #P384 t2 t3;
    let h6 = ST.get() in 
  (* fsquarePowN_dh #P384 (size 30) t3 ; *)
  montgomery_multiplication_buffer_dh #P384 t t3 t3;
    let h7 = ST.get() in 
(* t3 = x32*)

(* x63     = m(n_sq(x32, 31) , x31) *)
  montgomery_square_buffer_dh #P384 t3 t4;
    let h8 = ST.get() in 
  fsquarePowN_dh #P384 (size 30) t4;
    let h9 = ST.get() in   
  montgomery_multiplication_buffer_dh #P384 t4 t2 t4;
    let h10 = ST.get() in 
(* t4 = x63 *)

   let tD = fromDomain__ (as_nat_ h0 t) in 
   let t1D = fromDomain__ (as_nat_ h0 t1) in 
   let t2D = fromDomain__ (as_nat_ h0 t2) in 
   let t3D = fromDomain__ (as_nat_ h0 t3) in 

   assert(as_nat_ h1 t2 = toDomain__ (t2D * t3D % prime384));
   assert(as_nat_ h2 t2 = toDomain__ (pow (t2D * t3D % prime384) (pow2 6) % prime384));
   assert(as_nat_ h3 t1 = toDomain__ (pow (t2D * t3D % prime384) (pow2 6) % prime384 * t1D % prime384));

   calc(==) {
     as_nat_ h2 t2;
     (==) {}
     toDomain__ (pow (t2D * t3D % prime384) (pow2 6) % prime384);
     (==) {power_distributivity (t2D * t3D) (pow2 6) prime384}
     toDomain__ (pow (t2D * t3D) (pow2 6) % prime384);
     (==) {power_distributivity_2 t2D t3D (pow2 6)}
     toDomain__ (pow t2D (pow2 6) * pow t3D (pow2 6) % prime384); };

   calc (==) {
     as_nat_ h3 t1;
     (==) {}
     toDomain__ (pow t2D (pow2 6) * pow t3D (pow2 6) % prime384 * t1D % prime384);
     (==) {lemma_mod_mul_distr_l (pow t2D (pow2 6) * pow t3D (pow2 6)) t1D prime384}
     toDomain__ (pow t2D (pow2 6) * pow t3D (pow2 6) * t1D % prime384);};

   calc (==) {
     as_nat_ h4 t2;
     (==) {}
     toDomain__ ((pow t2D (pow2 6) * pow t3D (pow2 6) * t1D) % prime384 * ((pow t2D (pow2 6) * pow t3D (pow2 6) * t1D) % prime384) % prime384);
     (==) {lemma_exp1_4_2 t1D t2D t3D prime384}
     toDomain__ ((pow t2D (pow2 7) * pow t3D (pow2 7) * pow t1D 2) % prime384);};

   calc (==) {
     as_nat_ h5 t2;
     (==) {}
     toDomain__ (((pow t2D (pow2 7) * pow t3D (pow2 7) * pow t1D 2) % prime384) * tD % prime384);
     (==) {lemma_mod_mul_distr_l (pow t2D (pow2 7) * pow t3D (pow2 7) * pow t1D 2) tD prime384}
     toDomain__ (pow t2D (pow2 7) * pow t3D (pow2 7) * pow t1D 2 * tD % prime384);};

   calc (==) {
     as_nat_ h6 t3;
     (==) {}
     toDomain__ ((pow t2D (pow2 7) * pow t3D (pow2 7) * pow t1D 2 * tD % prime384) * (pow t2D (pow2 7) * pow t3D (pow2 7) * pow t1D 2 * tD % prime384) % prime384);
     (==) {lemma_exp1_5_2 tD t1D t2D t3D prime384}
     toDomain__ ((pow t2D (pow2 8) * pow t3D (pow2 8) * pow t1D (pow2 2) * pow tD 2) % prime384);};

   calc (==) {
     as_nat_ h7 t3;
     (==) {}
     toDomain__ (tD * ((pow t2D (pow2 8) * pow t3D (pow2 8) * pow t1D (pow2 2) * pow tD 2) % prime384) % prime384);
     (==) {lemma_mod_mul_distr_r tD ((pow t2D (pow2 8) * pow t3D (pow2 8) * pow t1D (pow2 2) * pow tD 2)) prime384}
     toDomain__ (tD * (pow t2D (pow2 8) * pow t3D (pow2 8) * pow t1D (pow2 2) * pow tD 2) % prime384);
     (==) {assert_by_tactic (tD * (pow t2D (pow2 8) * pow t3D (pow2 8) * pow t1D (pow2 2) * pow tD 2) == 
       (pow t2D (pow2 8) * pow t3D (pow2 8) * pow t1D (pow2 2) * (pow tD 2 * tD))) canon; power_one_2 tD}
     toDomain__ ((pow t2D (pow2 8) * pow t3D (pow2 8) * pow t1D (pow2 2) * (pow tD 2 * pow tD 1)) % prime384);
     (==) {pow_plus tD 2 1}
     toDomain__ ((pow t2D (pow2 8) * pow t3D (pow2 8) * pow t1D (pow2 2) * pow tD 3) % prime384);};

   calc (==) {
     as_nat_ h8 t4;
     (==) {}
     toDomain__ (((pow t2D (pow2 8) * pow t3D (pow2 8) * pow t1D (pow2 2) * pow tD 3) % prime384) * ((pow t2D (pow2 8) * pow t3D (pow2 8) * pow t1D (pow2 2) * pow tD 3) % prime384) % prime384);
     (==) {lemma_exp1_8_2 tD t1D t2D t3D prime384}
     toDomain__ ((pow t2D (pow2 9) * pow t3D (pow2 9) * pow t1D (pow2 3) * pow tD 6) % prime384); };

   let pow2_30 = pow2 30 in 
   let pow2_31 = pow2 31 in 
   let pow2_33 = pow2 33 in 
   let pow2_39 = pow2 39 in 

   calc (==) {
     as_nat_ h9 t4;
     (==) {}
     toDomain__ (pow ((pow t2D (pow2 9) * pow t3D (pow2 9) * pow t1D (pow2 3) * pow tD 6) % prime384) pow2_30 % prime384);
     (==) {lemma_exp1_9_2 tD t1D t2D t3D prime384}
     toDomain__ (pow t2D pow2_39 * pow t3D pow2_39 * pow t1D pow2_33 * pow tD (3 * pow2_31) % prime384);};

   calc (==) {
     as_nat_ h10 t4;
     (==) {}
     toDomain__ ((pow t2D pow2_39 * pow t3D pow2_39 * pow t1D pow2_33 * pow tD (3 * pow2_31) % prime384) * (pow t2D (pow2 7) * pow t3D (pow2 7) * pow t1D 2 * tD % prime384) % prime384);
     (==) {lemma_exp1_10_2 tD t1D t2D t3D prime384}
     toDomain__ (pow t2D (pow2_39 + pow2 7) * pow t3D (pow2_39 + pow2 7) * pow t1D (pow2_33 + 2) * pow tD (3 * pow2_31 + 1) % prime384);
     }


val lemma_exp2_9: t0D : nat -> t4D: nat -> Lemma (
  toDomain__ (pow (pow t4D (pow2 192 + pow2 129 + pow2 66 + pow2 3) * t0D % prime384) (pow2 33) % prime384) ==
  toDomain__ (pow t4D (pow2 225 + pow2 162 + pow2 99 + pow2 36) * pow t0D (pow2 33) % prime384))

let lemma_exp2_9 t0D t4D = 
  let pow2_33 = pow2 33 in 
  let pow2_192 = pow2 192 in 
  let pow2_129 = pow2 129 in 
  let pow2_66 = pow2 66 in 

  let pow2_225 = pow2 225 in 
  let pow2_162 = pow2 162 in 
  let pow2_99 = pow2 99 in 
  let pow2_36 = pow2 36 in 

  calc (==) {
    toDomain__ (pow (pow t4D (pow2_192 + pow2_129 + pow2_66 + pow2 3) * t0D % prime384) pow2_33 % prime384);
  (==) {power_distributivity (pow t4D (pow2_192 + pow2_129 + pow2_66 + pow2 3) * t0D) pow2_33 prime384}
    toDomain__ (pow (pow t4D (pow2_192 + pow2_129 + pow2_66 + pow2 3) * t0D) pow2_33 % prime384);
  (==) {power_distributivity_2 (pow t4D (pow2_192 + pow2_129 + pow2_66 + pow2 3)) t0D pow2_33; power_one_2 t0D}
    toDomain__ (pow (pow t4D (pow2_192 + pow2_129 + pow2_66 + pow2 3)) pow2_33 * pow (pow t0D 1) pow2_33 % prime384);
  (==) {power_mult t4D (pow2_192 + pow2_129 + pow2_66 + pow2 3) pow2_33; power_mult t0D 1 pow2_33}
    toDomain__ (pow t4D (pow2_192 * pow2_33 + pow2_129 * pow2_33 + pow2_66 * pow2_33 + pow2 3 * pow2_33) * pow t0D pow2_33 % prime384);
  (==) {pow2_plus 192 33; pow2_plus 129 33; pow2_plus 66 33; pow2_plus 3 33}
    toDomain__ (pow t4D (pow2_225 + pow2_162 + pow2_99 + pow2_36) * pow t0D pow2_33 % prime384);}

inline_for_extraction noextract
val exponent2: t0: felem P384 -> t3: felem P384 -> t4: felem P384 -> t5: felem P384 -> Stack unit 
  (requires fun h -> live h t0 /\ live h t3 /\ live h t4 /\ live h t5 /\
    LowStar.Monotonic.Buffer.all_disjoint [loc t0; loc t3; loc t4; loc t5] /\ 
    as_nat_ h t0 < prime384 /\ as_nat_ h t3 < prime384 /\ as_nat_ h t4 < prime384 /\ as_nat_ h t5 < prime384)
  (ensures fun h0 _ h1 -> True)


let exponent2 t0 t3 t4 t5  = 
  let h0 = ST.get() in 
(* x126    = m(n_sq(x63, 63) , x63) *)
  montgomery_square_buffer_dh #P384 t4 t5;
    let h1 = ST.get() in 
  fsquarePowN_dh #P384 (size 62) t5;
    let h2 = ST.get() in 
  montgomery_multiplication_buffer_dh #P384 t4 t5 t4;  
  (* t4 = x126*)
    let h3 = ST.get() in 

(* x252    = m(n_sq(x126, 126) , x126) *)
  montgomery_square_buffer_dh #P384 t4 t5;
    let h4 = ST.get() in 

  fsquarePowN_dh #P384 (size 125) t5 ;
    let h5 = ST.get() in 

  montgomery_multiplication_buffer_dh #P384 t4 t5 t4;
    let h6 = ST.get() in 
(* t4 = x252 *)
   
(* x255    = m(n_sq(x252, 3) , _111) *)
  fsquarePowN_dh #P384 (size 3) t4 ;
    let h7 = ST.get() in 
  montgomery_multiplication_buffer_dh #P384 t4 t0 t4;
    let h8 = ST.get() in 
(* t4 = x255 *)

(* i0 = m(n_sq(x255, 33), x32) *)
  fsquarePowN_dh #P384 (size 33) t4 ;
    let h9 = ST.get() in 
  montgomery_multiplication_buffer_dh #P384 t4 t3 t4;
    let h10 = ST.get() in 

  let t0D = fromDomain__ (as_nat_ h0 t0) in 
  let t3D = fromDomain__ (as_nat_ h0 t3) in 
  let t4D = fromDomain__ (as_nat_ h0 t4) in 
  let t5D = fromDomain__ (as_nat_ h0 t5) in 

  calc (==) {
    as_nat_ h1 t5;
  (==) {}
    toDomain__ (t4D * t4D % prime384);
  (==) {power_one_2 t4D}
    toDomain__ (pow t4D 1 * pow t4D 1 % prime384);
  (==) {pow_plus t4D 1 1}
    toDomain__ (pow t4D 2 % prime384);};

  let pow2_62 = pow2 62 in 
  let pow2_63 = pow2 63 in 

  calc (==) {
    as_nat_ h2 t5;
  (==) {}
    toDomain__ (pow (pow t4D 2 % prime384) pow2_62 % prime384);
  (==) {power_distributivity (pow t4D 2) pow2_62 prime384}
    toDomain__ (pow (pow t4D 2) pow2_62 % prime384);
  (==) {power_mult t4D 2 pow2_62}
    toDomain__ (pow t4D (pow2 1 * pow2_62) % prime384);
  (==) {pow2_plus 1 62}
     toDomain__ (pow t4D pow2_63 % prime384);};

  calc (==) {
    as_nat_ h3 t4;
  (==) {}
    toDomain__ (t4D * (pow t4D pow2_63 % prime384) % prime384);
  (==) {lemma_mod_mul_distr_r t4D (pow t4D pow2_63) prime384}
    toDomain__ (t4D * pow t4D pow2_63 % prime384);
  (==) {power_one_2 t4D}
    toDomain__ (pow t4D 1 * pow t4D pow2_63 % prime384);
  (==) {pow_plus t4D 1 pow2_63}
    toDomain__ (pow t4D (pow2_63 + 1) % prime384);};

  let pow2_64 = pow2 64 in 
  
  calc (==) {
    as_nat_ h4 t5;
  (==) {}
    toDomain__ (pow t4D (pow2_63 + 1) % prime384 * (pow t4D (pow2_63 + 1) % prime384) % prime384);
  (==) {lemma_mod_mul_distr (pow t4D (pow2_63 + 1)) (pow t4D (pow2_63 + 1)) prime384}
    toDomain__ (pow t4D (pow2_63 + 1) * pow t4D (pow2_63 + 1) % prime384);
  (==) {pow_plus t4D (pow2_63 + 1) (pow2_63 + 1)}
    toDomain__ (pow t4D (2 * pow2_63 + 2) % prime384);
  (==) {pow2_double_mult 63}
    toDomain__ (pow t4D (pow2_64 + 2) % prime384);};

  let pow2_125 = pow2 125 in 
  let pow2_126 = pow2 126 in 
  let pow2_189 = pow2 189 in 
  
  calc (==) {
    as_nat_ h5 t5;
  (==) {}
    toDomain__ (pow (pow t4D (pow2_64 + 2) % prime384) pow2_125 % prime384);
  (==) {power_distributivity (pow t4D (pow2_64 + 2)) pow2_125 prime384}
    toDomain__ (pow (pow t4D (pow2_64 + 2)) pow2_125 % prime384);
  (==) {power_mult t4D (pow2_64 + 2) pow2_125}
    toDomain__ (pow t4D (pow2_64 * pow2_125 + 2 * pow2_125) % prime384);  
  (==) {pow2_plus 64 125; pow2_double_mult 125}
    toDomain__ (pow t4D (pow2_189 + pow2_126) % prime384);};

  calc (==) {
    as_nat_ h6 t4;
  (==) {}
    toDomain__ (pow t4D (pow2_63 + 1) % prime384 * (pow t4D (pow2_189 + pow2_126) % prime384) % prime384);
  (==) {lemma_mod_mul_distr (pow t4D (pow2_63 + 1)) (pow t4D (pow2_189 + pow2_126)) prime384}
    toDomain__ (pow t4D (pow2_63 + 1) * pow t4D (pow2_189 + pow2_126) % prime384);
  (==) {pow_plus t4D (pow2_63 + 1) (pow2_189 + pow2_126)}  
    toDomain__ (pow t4D (pow2_189 + pow2_126 + pow2_63 + 1) % prime384);};

  let pow2_192 = pow2 192 in 
  let pow2_129 = pow2 129 in 
  let pow2_66 = pow2 66 in 

  calc (==) {
    as_nat_ h7 t4;
  (==) {}
    toDomain__ (pow (pow t4D (pow2_189 + pow2_126 + pow2_63 + 1) % prime384) (pow2 3) % prime384);
  (==) {power_distributivity (pow t4D (pow2_189 + pow2_126 + pow2_63 + 1)) (pow2 3) prime384}
    toDomain__ (pow (pow t4D (pow2_189 + pow2_126 + pow2_63 + 1)) (pow2 3) % prime384);
  (==) {power_mult t4D (pow2_189 + pow2_126 + pow2_63 + 1) (pow2 3)}
    toDomain__ (pow t4D (pow2_189 * pow2 3 + pow2_126 * pow2 3 + pow2_63 * pow2 3 + pow2 3) % prime384);
  (==) {pow2_plus 189 3; pow2_plus 126 3; pow2_plus 63 3}
    toDomain__ (pow t4D (pow2_192 + pow2_129 + pow2_66 + pow2 3) % prime384);};
    
  calc (==) {
    as_nat_ h8 t4;
  (==) {}
    toDomain__ (pow t4D (pow2_192 + pow2_129 + pow2_66 + pow2 3) % prime384 * t0D % prime384);
  (==) {lemma_mod_mul_distr_l (pow t4D (pow2_192 + pow2_129 + pow2_66 + pow2 3)) t0D prime384}
    toDomain__ (pow t4D (pow2_192 + pow2_129 + pow2_66 + pow2 3) * t0D % prime384);};

  let pow2_33 = pow2 33 in 

  let pow2_225 = pow2 225 in 
  let pow2_162 = pow2 162 in 
  let pow2_99 = pow2 99 in 
  let pow2_36 = pow2 36 in 
  
  calc (==) {
    as_nat_ h9 t4;
  (==) {lemma_exp2_9 t0D t4D}
    toDomain__ (pow t4D (pow2_225 + pow2_162 + pow2_99 + pow2_36) * pow t0D (pow2_33) % prime384);}




(*t4 = i0 *)

inline_for_extraction noextract
val exponent3: t: felem P384 -> t1: felem P384 -> t4: felem P384 -> result: felem P384 -> Stack unit 
  (requires fun h -> live h t /\ live h t1 /\ live h t4 /\ live h result /\
    LowStar.Monotonic.Buffer.all_disjoint [loc t; loc t1; loc t4] /\
    as_nat_ h t < prime384 /\ as_nat_ h t1 < prime384 /\ as_nat_ h t4 < prime384)
  (ensures fun h0 _ h1 -> modifies (loc t1 |+| loc t4 |+| loc result) h0 h1)


let exponent3 t t1 t4 result = 
(* i1 = m(n_sq(i0, 94), x30) *)
  fsquarePowN_dh #P384 (size 94) t4 ;
  montgomery_multiplication_buffer_dh #P384 t4 t1 t4;
(* t4 = i1 *)

(* i397    = n_sq(i1, 2) *)
  fsquarePowN_dh #P384  (size 2) t4;

(* r = m(t, i397) *)
  montgomery_multiplication_buffer_dh #P384 t4 t result



let exponent_p384 t result tempBuffer = 
  let h0 = ST.get () in 

  let t0 = sub tempBuffer (size 0) (size 6) in 

  let t1 = sub tempBuffer (size 6) (size 6) in 
  let t2 = sub tempBuffer (size 12) (size 6) in 
  let t3 = sub tempBuffer (size 18) (size 6) in 
  let t4 = sub tempBuffer (size 24) (size 6) in 
  let t5 = sub tempBuffer (size 30) (size 6) in 

  exponent0 t t0 t1 t2 t3;
  exponent1 t t1 t2 t3 t4;
  exponent2 t0 t3 t4 t5;
  exponent3 t t1 t4 result


