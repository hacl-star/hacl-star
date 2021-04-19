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
open Hacl.Lemmas.P256

open FStar.Tactics 
open FStar.Tactics.Canon 

open Hacl.Spec.MontgomeryMultiplication


#set-options "--z3rlimit 100 --ifuel 0 --fuel 0"

let fromDomain_ = fromDomain_ #P384 #DH
let toDomain_ = toDomain_ #P384 #DH

let as_nat h1 result = as_nat P384 h1 result

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


val exponent0: t: felem P384 -> t0: felem P384 -> t1: felem P384 -> t2: felem P384 -> t3: felem P384 ->  Stack unit 
  (requires fun h -> live h t /\ live h t0 /\ live h t1 /\ live h t2 /\ live h t3 /\
    LowStar.Monotonic.Buffer.all_disjoint [loc t; loc t0; loc t1; loc t2; loc t3] /\
    as_nat h t < prime384)
  (ensures fun h0 _ h1 -> modifies (loc t0 |+| loc t1 |+| loc t2 |+| loc t3) h0 h1 /\
    as_nat h1 t < prime384 /\ as_nat h1 t0 < prime384 /\ as_nat h1 t1 < prime384 /\ as_nat h1 t2 < prime384 /\ 
    as_nat h1 t3 < prime384 /\ (
    let tD = fromDomain_ (as_nat h0 t) in 
    as_nat h1 t0 = toDomain_ (pow tD 7 % prime384) /\
    as_nat h1 t1 = toDomain_ (pow tD 63 % prime384) /\
    as_nat h1 t2 = toDomain_ (pow tD (126 * pow2 5 + 63) % prime384) /\
    as_nat h1 t3 = toDomain_ (pow tD (63 * (pow2 7 + 2) *  pow2 11)  % prime384)))


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

  let tD = fromDomain_ (as_nat h0 t) in
  Hacl.Lemmas.P256.power_one_2 tD;
  
  assert(as_nat h1 t0 = toDomain_ (tD * tD % prime384));
  assert(as_nat h3 t0 = toDomain_ (fromDomain_ (as_nat h2 t0) * fromDomain_ (as_nat h2 t0) % prime384));
  assert(as_nat h4 t0 = toDomain_ (tD * fromDomain_ (as_nat h3 t0) % prime384));
  assert(as_nat h5 t1 = toDomain_ (fromDomain_ (as_nat h4 t0) * fromDomain_ (as_nat h4 t0) % prime384));
  assert(as_nat h6 t1 = toDomain_ (pow (fromDomain_ (as_nat h5 t1)) 4 % prime384));
  
  calc (==) {
    as_nat h2 t0;
    (==) {}
    toDomain_ (tD * (pow tD 1 * pow tD 1 % prime384) % prime384);
    (==) {pow_plus tD 1 1}
    toDomain_ (tD * (pow tD 2 % prime384) % prime384);
    (==) {lemma_mod_mul_distr_r tD (pow tD 2) prime384}
    toDomain_ (pow tD 1 * pow tD 2 % prime384);
    (==) {pow_plus tD 1 2}
    toDomain_ (pow tD 3 % prime384);};

  calc (==) {
    as_nat h3 t0;
    (==) {}
    toDomain_ ((pow tD 3 % prime384) * (pow tD 3 % prime384) % prime384); 
    (==) {lemma_mod_mul_distr_l (pow tD 3) (pow tD 3 % prime384) prime384; 
      lemma_mod_mul_distr_l (pow tD 3) (pow tD 3) prime384}
    toDomain_ (pow tD 3 * pow tD 3 % prime384);
    (==) {pow_plus tD 3 3}
    toDomain_ (pow tD 6 % prime384);};

  calc (==) {
    as_nat h4 t0;
    (==) {}
    toDomain_ (tD * (pow tD 6 % prime384) % prime384);
    (==) {lemma_mod_mul_distr_r tD (pow tD 6) prime384}
    toDomain_ (pow tD 1 * pow tD 6 % prime384);
    (==) {pow_plus tD 1 6}
    toDomain_ (pow tD 7 % prime384);};

  calc (==) {
    as_nat h5 t1;
    (==) {}
    toDomain_ (pow tD 7 % prime384 * (pow tD 7 % prime384) % prime384);
    (==) {lemma_mod_mul_distr (pow tD 7) (pow tD 7) prime384}
    toDomain_ (pow tD 7 * pow tD 7 % prime384);
    (==) {pow_plus tD 7 7}
    toDomain_ (pow tD 14 % prime384); };

  calc (==) {
    as_nat h6 t1;
    (==) {}
    toDomain_ (pow (pow tD 14 % prime384) 4 % prime384);
    (==) {power_distributivity (pow tD 14) 4 prime384}
    toDomain_ (pow (pow tD 14) 4 % prime384);
    (==) {power_mult tD 14 4}
    toDomain_ (pow tD 56 % prime384); };

  calc (==) {
    as_nat h7 t1;
    (==) {}
    toDomain_ ((pow tD 7 % prime384) * (pow tD 56 % prime384) % prime384);
    (==) {lemma_mod_mul_distr (pow tD 7) (pow tD 56) prime384}
    toDomain_ ((pow tD 7) * (pow tD 56) % prime384);
    (==) {pow_plus tD 7 56}
    toDomain_ (pow tD 63 % prime384);};

  calc (==) {
    as_nat h8 t2;
    (==) {}
    toDomain_ ((pow tD 63 % prime384) * (pow tD 63 % prime384) % prime384);
    (==) {lemma_mod_mul_distr1 tD 63 63 prime384}
    toDomain_ (pow tD 126 % prime384);};

  calc (==) {
    as_nat h9 t2;
    (==) {}
    toDomain_ (pow (pow tD 126 % prime384) (pow2 5) % prime384);
    (==) {power_distributivity (pow tD 126) (pow2 5) prime384}
    toDomain_ (pow (pow tD 126) (pow2 5) % prime384);
    (==) {power_mult tD 126 (pow2 5)}
    toDomain_ (pow tD (126 * pow2 5) % prime384);};  

  calc (==) {
    as_nat h10 t2;
    (==) {}
    toDomain_ (pow tD (126 * pow2 5) % prime384 * (pow tD 63 % prime384) % prime384);
    (==) {lemma_mod_mul_distr1 tD (126 * pow2 5) 63 prime384}
    toDomain_ (pow tD (126 * pow2 5 + 63) % prime384);};

  calc (==) {
    as_nat h11 t3;
    (==) {}
    toDomain_ (pow tD (126 * pow2 5 + 63) % prime384 * (pow tD (126 * pow2 5 + 63) % prime384) % prime384);
    (==) {lemma_mod_mul_distr1 tD (126 * pow2 5 + 63) (126 * pow2 5 + 63) prime384}
    toDomain_ (pow tD (4 * 63 * pow2 5 + 2 * 63) % prime384);
    (==) {assert_by_tactic (4 * 63 * pow2 5 == 63 * (4 * pow2 5)) canon}
    toDomain_ (pow tD (63 * (pow2 2 * pow2 5) + 2 * 63) % prime384);
    (==) {pow2_plus 2 5}
    toDomain_ (pow tD (63 * (pow2 7 + 2)) % prime384);};

  let pow2_11 = pow2 11 in 
  
  calc (==) {
    as_nat h12 t3;
    (==) {}
    toDomain_ (pow (pow tD (63 * (pow2 7 + 2)) % prime384) pow2_11  % prime384);
    (==) {power_distributivity (pow tD (63 * (pow2 7 + 2))) pow2_11 prime384}
    toDomain_ (pow (pow tD (63 * (pow2 7 + 2))) pow2_11  % prime384);
    (==) {power_mult tD (63 * (pow2 7 + 2)) pow2_11}
    toDomain_ (pow tD (63 * (pow2 7 + 2) *  pow2_11)  % prime384); }


val lemma_exp1_4_2: t1D: nat -> t2D : nat -> t3D: nat -> prime384: pos  -> Lemma (    
  toDomain_ ((pow t2D (pow2 6) * pow t3D (pow2 6) * t1D) % prime384 * ((pow t2D (pow2 6) * pow t3D (pow2 6) * t1D) % prime384) % prime384) == toDomain_ ((pow t2D (pow2 7) * pow t3D (pow2 7) * pow t1D 2) % prime384))
  
let lemma_exp1_4_2 t1D t2D t3D prime384 = 

  calc (==) {
    toDomain_ ((pow t2D (pow2 6) * pow t3D (pow2 6) * t1D) % prime384 * ((pow t2D (pow2 6) * pow t3D (pow2 6) * t1D) % prime384) % prime384);
     (==) {lemma_mod_mul_distr (pow t2D (pow2 6) * pow t3D (pow2 6) * t1D) (pow t2D (pow2 6) * pow t3D (pow2 6) * t1D) prime384}
     toDomain_ ((pow t2D (pow2 6) * pow t3D (pow2 6) * t1D) * (pow t2D (pow2 6) * pow t3D (pow2 6) * t1D) % prime384);
     (==) {assert_by_tactic ((pow t2D (pow2 6) * pow t3D (pow2 6) * t1D) * (pow t2D (pow2 6) * pow t3D (pow2 6) * t1D) == 
       (pow t2D (pow2 6) * pow t2D (pow2 6)) * (pow t3D (pow2 6) * pow t3D (pow2 6)) * (t1D * t1D)) canon}
     toDomain_ ((pow t2D (pow2 6) * pow t2D (pow2 6)) * (pow t3D (pow2 6) * pow t3D (pow2 6)) * (t1D * t1D) % prime384);
     (==) {pow_plus t2D (pow2 6) (pow2 6); pow_plus t3D (pow2 6) (pow2 6); power_one_2 t1D}
     toDomain_ (pow t2D (2 * pow2 6) * pow t3D (2 * pow2 6) * (pow t1D 1 * pow t1D 1) % prime384);
     (==) {pow2_double_sum 6; pow_plus t1D 1 1}
     toDomain_ ((pow t2D (pow2 7) * pow t3D (pow2 7) * pow t1D 2) % prime384);}


val lemma_exp1_5_2: tD: nat -> t1D: nat -> t2D : nat -> t3D: nat -> prime384: pos -> Lemma (
  toDomain_ ((pow t2D (pow2 7) * pow t3D (pow2 7) * pow t1D 2 * tD % prime384) * (pow t2D (pow2 7) * pow t3D (pow2 7) * pow t1D 2 * tD % prime384) % prime384) ==
    toDomain_ ((pow t2D (pow2 8) * pow t3D (pow2 8) * pow t1D (pow2 2) * pow tD 2) % prime384))


let lemma_exp1_5_2 tD t1D t2D t3D prime384 = 
  calc (==) {
    toDomain_ ((pow t2D (pow2 7) * pow t3D (pow2 7) * pow t1D 2 * tD % prime384) * (pow t2D (pow2 7) * pow t3D (pow2 7) * pow t1D 2 * tD % prime384) % prime384);
     (==) {lemma_mod_mul_distr (pow t2D (pow2 7) * pow t3D (pow2 7) * pow t1D 2 * tD) (pow t2D (pow2 7) * pow t3D (pow2 7) * pow t1D 2 * tD) prime384}
     toDomain_ ((pow t2D (pow2 7) * pow t3D (pow2 7) * pow t1D 2 * tD) * (pow t2D (pow2 7) * pow t3D (pow2 7) * pow t1D 2 * tD) % prime384);
     (==) {assert_by_tactic (((pow t2D (pow2 7) * pow t3D (pow2 7) * pow t1D 2 * tD) * (pow t2D (pow2 7) * pow t3D (pow2 7) * pow t1D 2 * tD)) == (pow t2D (pow2 7) * pow t2D (pow2 7)) * (pow t3D (pow2 7) * pow t3D (pow2 7)) * (pow t1D 2 * pow t1D 2) * (tD * tD)) canon}
     toDomain_ (((pow t2D (pow2 7) * pow t2D (pow2 7)) * (pow t3D (pow2 7) * pow t3D (pow2 7)) * (pow t1D 2 * pow t1D 2) * (tD * tD)) % prime384);
     (==) {pow_plus t2D (pow2 7) (pow2 7); pow_plus t3D (pow2 7) (pow2 7); pow_plus t1D 2 2; power_one_2 tD}
     toDomain_ (((pow t2D (2 * pow2 7)) * (pow t3D (2 * pow2 7)) * (pow t1D 4) * (pow tD 1 * pow tD 1)) % prime384);
     (==) {pow2_double_sum 7; pow_plus tD 1 1}
     toDomain_ (((pow t2D (pow2 8)) * (pow t3D (pow2 8)) * (pow t1D 4) * (pow tD 2)) % prime384);}


val lemma_exp1_8_2: tD: nat -> t1D: nat -> t2D : nat -> t3D: nat -> prime384: pos -> Lemma (
  toDomain_ (((pow t2D (pow2 8) * pow t3D (pow2 8) * pow t1D (pow2 2) * pow tD 3) % prime384) * ((pow t2D (pow2 8) * pow t3D (pow2 8) * pow t1D (pow2 2) * pow tD 3) % prime384) % prime384) == 
  toDomain_ ((pow t2D (pow2 9) * pow t3D (pow2 9) * pow t1D (pow2 3) * pow tD 6) % prime384))

let lemma_exp1_8_2 tD t1D t2D t3D prime384 = 
   calc (==) {
     toDomain_ (((pow t2D (pow2 8) * pow t3D (pow2 8) * pow t1D (pow2 2) * pow tD 3) % prime384) * ((pow t2D (pow2 8) * pow t3D (pow2 8) * pow t1D (pow2 2) * pow tD 3) % prime384) % prime384);
     (==) {lemma_mod_mul_distr (pow t2D (pow2 8) * pow t3D (pow2 8) * pow t1D (pow2 2) * pow tD 3) (pow t2D (pow2 8) * pow t3D (pow2 8) * pow t1D (pow2 2) * pow tD 3) prime384}
     toDomain_ (pow t2D (pow2 8) * pow t3D (pow2 8) * pow t1D (pow2 2) * pow tD 3 * ((pow t2D (pow2 8) * pow t3D (pow2 8) * pow t1D (pow2 2) * pow tD 3)) % prime384);
     (==) {assert_by_tactic ((pow t2D (pow2 8) * pow t3D (pow2 8) * pow t1D (pow2 2) * pow tD 3 * ((pow t2D (pow2 8) * pow t3D (pow2 8) * pow t1D (pow2 2) * pow tD 3))) == (pow t2D (pow2 8) * pow t2D (pow2 8)) * (pow t3D (pow2 8) * pow t3D (pow2 8)) * (pow t1D (pow2 2) * pow t1D (pow2 2)) * (pow tD 3 * pow tD 3)) canon}
     toDomain_ (((pow t2D (pow2 8) * pow t2D (pow2 8)) * (pow t3D (pow2 8) * pow t3D (pow2 8)) * (pow t1D (pow2 2) * pow t1D (pow2 2)) * (pow tD 3 * pow tD 3)) % prime384);
     (==) {pow_plus t2D (pow2 8) (pow2 8); pow_plus t3D (pow2 8) (pow2 8); pow_plus t1D (pow2 2) (pow2 2); pow_plus tD 3 3}
     toDomain_ ((pow t2D (2 * pow2 8) * pow t3D (2 * pow2 8) * pow t1D (2 * pow2 2) * pow tD 6) % prime384);
     (==) {pow2_double_sum 8; pow2_double_sum 2}
     toDomain_ ((pow t2D (pow2 9) * pow t3D (pow2 9) * pow t1D (pow2 3) * pow tD 6) % prime384);}

val lemma_exp1_9_2_: a: nat -> b: nat -> c: nat -> d: nat -> e: pos -> Lemma
   (pow (a * b * c * d) e = pow a e * pow b e * pow c e * pow d e)

let lemma_exp1_9_2_ a b c d  e = 
  Hacl.Lemmas.P256.power_distributivity_2 (a * b * c) d e;
  Hacl.Lemmas.P256.power_distributivity_2 (a * b) c e;
  Hacl.Lemmas.P256.power_distributivity_2 a b e
  


val lemma_exp1_9_2: tD: nat -> t1D: nat -> t2D : nat -> t3D: nat -> prime384: pos -> Lemma (True)

let lemma_exp1_9_2 tD t1D t2D t3D prime384 = 
  let pow2_30 = pow2 30 in 
   calc (==) {
     toDomain_ (pow ((pow t2D (pow2 9) * pow t3D (pow2 9) * pow t1D (pow2 3) * pow tD 6) % prime384) pow2_30 % prime384);
   (==) {power_distributivity (pow t2D (pow2 9) * pow t3D (pow2 9) * pow t1D (pow2 3) * pow tD 6) (pow2_30) prime384}
     toDomain_ (pow (pow t2D (pow2 9) * pow t3D (pow2 9) * pow t1D (pow2 3) * pow tD 6) pow2_30 % prime384);
  }


#set-options "--z3rlimit 300 --ifuel 0 --fuel 0"

val exponent1: t: felem P384 -> t1: felem P384 -> t2: felem P384 -> t3: felem P384 -> t4: felem P384 ->  Stack unit 
  (requires fun h -> live h t /\ live h t1 /\ live h t2 /\ live h t3 /\ live h t4 /\
    LowStar.Monotonic.Buffer.all_disjoint [loc t; loc t1; loc t2; loc t3; loc t4] /\
    as_nat h t < prime384 /\ as_nat h t1 < prime384 /\ as_nat h t2 < prime384 /\ as_nat h t3 < prime384)
  (ensures fun h0 _ h1 -> modifies (loc t1 |+| loc t2 |+| loc t3 |+| loc t4) h0 h1)


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
(* t4 = x63 *)

   let tD = fromDomain_ (as_nat h0 t) in 
   let t1D = fromDomain_ (as_nat h0 t1) in 
   let t2D = fromDomain_ (as_nat h0 t2) in 
   let t3D = fromDomain_ (as_nat h0 t3) in 

   assert(as_nat h1 t2 = toDomain_ (t2D * t3D % prime384));
   assert(as_nat h2 t2 = toDomain_ (pow (t2D * t3D % prime384) (pow2 6) % prime384));
   assert(as_nat h3 t1 = toDomain_ (pow (t2D * t3D % prime384) (pow2 6) % prime384 * t1D % prime384));

   calc(==) {
     as_nat h2 t2;
     (==) {}
     toDomain_ (pow (t2D * t3D % prime384) (pow2 6) % prime384);
     (==) {power_distributivity (t2D * t3D) (pow2 6) prime384}
     toDomain_ (pow (t2D * t3D) (pow2 6) % prime384);
     (==) {power_distributivity_2 t2D t3D (pow2 6)}
     toDomain_ (pow t2D (pow2 6) * pow t3D (pow2 6) % prime384); };

   calc (==) {
     as_nat h3 t1;
     (==) {}
     toDomain_ (pow t2D (pow2 6) * pow t3D (pow2 6) % prime384 * t1D % prime384);
     (==) {lemma_mod_mul_distr_l (pow t2D (pow2 6) * pow t3D (pow2 6)) t1D prime384}
     toDomain_ (pow t2D (pow2 6) * pow t3D (pow2 6) * t1D % prime384);};

   calc (==) {
     as_nat h4 t2;
     (==) {}
     toDomain_ ((pow t2D (pow2 6) * pow t3D (pow2 6) * t1D) % prime384 * ((pow t2D (pow2 6) * pow t3D (pow2 6) * t1D) % prime384) % prime384);
     (==) {lemma_exp1_4_2 t1D t2D t3D prime384}
     toDomain_ ((pow t2D (pow2 7) * pow t3D (pow2 7) * pow t1D 2) % prime384);};

   calc (==) {
     as_nat h5 t2;
     (==) {}
     toDomain_ (((pow t2D (pow2 7) * pow t3D (pow2 7) * pow t1D 2) % prime384) * tD % prime384);
     (==) {lemma_mod_mul_distr_l (pow t2D (pow2 7) * pow t3D (pow2 7) * pow t1D 2) tD prime384}
     toDomain_ (pow t2D (pow2 7) * pow t3D (pow2 7) * pow t1D 2 * tD % prime384);};

   calc (==) {
     as_nat h6 t3;
     (==) {}
     toDomain_ ((pow t2D (pow2 7) * pow t3D (pow2 7) * pow t1D 2 * tD % prime384) * (pow t2D (pow2 7) * pow t3D (pow2 7) * pow t1D 2 * tD % prime384) % prime384);
     (==) {lemma_exp1_5_2 tD t1D t2D t3D prime384}
     toDomain_ ((pow t2D (pow2 8) * pow t3D (pow2 8) * pow t1D (pow2 2) * pow tD 2) % prime384);};

   calc (==) {
     as_nat h7 t3;
     (==) {}
     toDomain_ (tD * ((pow t2D (pow2 8) * pow t3D (pow2 8) * pow t1D (pow2 2) * pow tD 2) % prime384) % prime384);
     (==) {lemma_mod_mul_distr_r tD ((pow t2D (pow2 8) * pow t3D (pow2 8) * pow t1D (pow2 2) * pow tD 2)) prime384}
     toDomain_ (tD * (pow t2D (pow2 8) * pow t3D (pow2 8) * pow t1D (pow2 2) * pow tD 2) % prime384);
     (==) {assert_by_tactic (tD * (pow t2D (pow2 8) * pow t3D (pow2 8) * pow t1D (pow2 2) * pow tD 2) == 
       (pow t2D (pow2 8) * pow t3D (pow2 8) * pow t1D (pow2 2) * (pow tD 2 * tD))) canon; power_one_2 tD}
     toDomain_ ((pow t2D (pow2 8) * pow t3D (pow2 8) * pow t1D (pow2 2) * (pow tD 2 * pow tD 1)) % prime384);
     (==) {pow_plus tD 2 1}
     toDomain_ ((pow t2D (pow2 8) * pow t3D (pow2 8) * pow t1D (pow2 2) * pow tD 3) % prime384);};

   calc (==) {
     as_nat h8 t4;
     (==) {}
     toDomain_ (((pow t2D (pow2 8) * pow t3D (pow2 8) * pow t1D (pow2 2) * pow tD 3) % prime384) * ((pow t2D (pow2 8) * pow t3D (pow2 8) * pow t1D (pow2 2) * pow tD 3) % prime384) % prime384);
     (==) {lemma_exp1_8_2 tD t1D t2D t3D prime384}
     toDomain_ ((pow t2D (pow2 9) * pow t3D (pow2 9) * pow t1D (pow2 3) * pow tD 6) % prime384); };

   let pow2_30 = pow2 30 in 

   calc (==) {
     as_nat h9 t4;
     (==) {}
     toDomain_ (pow ((pow t2D (pow2 9) * pow t3D (pow2 9) * pow t1D (pow2 3) * pow tD 6) % prime384) pow2_30 % prime384);
     }



val exponent2: t0: felem P384  -> t3: felem P384 -> t4: felem P384 -> t5: felem P384 -> Stack unit 
  (requires fun h ->  live h t3 /\ live h t4 /\
    LowStar.Monotonic.Buffer.all_disjoint [ loc t3; loc t4])
  (ensures fun h0 _ h1 -> True)


let exponent2 t0 t3 t4 t5  = 

(* x126    = m(n_sq(x63, 63) , x63) *)
  montgomery_square_buffer_dh #P384 t4 t5;
  fsquarePowN_dh #P384 (size 62) t5;

  montgomery_multiplication_buffer_dh #P384 t4 t5 t4;  
(* t4 = x126*)


(* x252    = m(n_sq(x126, 126) , x126) *)
  montgomery_square_buffer_dh #P384 t4 t5;
  fsquarePowN_dh #P384 (size 125) t5 ;
  montgomery_multiplication_buffer_dh #P384 t4 t5 t4;
(* t4 = x252 *)


(* x255    = m(n_sq(x252, 3) , _111) *)
  fsquarePowN_dh #P384 (size 3) t4 ;
  montgomery_multiplication_buffer_dh #P384 t4 t0 t4;
(* t4 = x255 *)


(* i0 = m(n_sq(x255, 33), x32) *)
  fsquarePowN_dh #P384 (size 33) t4 ;
  montgomery_multiplication_buffer_dh #P384 t4 t3 t4
(*t4 = i0 *)


val exponent3: t: felem P384 -> t1: felem P384 -> t4: felem P384 -> result: felem P384 -> Stack unit 
  (requires fun h -> live h t /\ live h t1 /\ live h t4 /\ live h result /\
    LowStar.Monotonic.Buffer.all_disjoint [loc t; loc t1; loc t4] /\
    as_nat h t < prime384 /\ as_nat h t1 < prime384 /\ as_nat h t4 < prime384)
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


val exponent_p384: a: felem P384 -> result: felem P384 -> 
  tempBuffer: lbuffer uint64 (getCoordinateLenU P384 *. 8ul) -> Stack unit
  (requires fun h -> live h a /\ live h tempBuffer /\ live h result /\ disjoint tempBuffer result /\ 
    disjoint a tempBuffer /\ as_nat  h a < getPrime P384)
  (ensures fun h0 _ h1 -> modifies (loc result |+| loc tempBuffer) h0 h1 /\ (
    let k = fromDomain #P384 (as_nat h0 a) in True ))(*
    as_nat P384 h1 result =  toDomain #P384 (pow k (prime384 - 2) % prime256) *) 


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


