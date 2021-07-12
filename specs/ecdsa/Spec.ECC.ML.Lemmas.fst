module Spec.ECC.ML.Lemmas

open Lib.IntTypes
open Lib.RawIntTypes
open Lib.LoopCombinators 

open Spec.ECC.Curves
open Spec.ECC

open FStar.Math
open FStar.Math.Lemmas
open FStar.Mul


#set-options "--fuel 0 --ifuel 0 --z3rlimit 100"

(* P + R == P + Q <==> R == Q --> P + P == P + Q <==> P == Q *)
assume val curve_point_equality: #c: curve -> p: point_nat_prime #c -> q: point_nat_prime #c -> Lemma 
  (pointEqual (pointAdd p q) (pointAdd p p) <==> pointEqual p q)

(* P + Q == Q + P *)
assume val curve_commutativity_lemma: #c: curve -> p: point_nat_prime #c -> q: point_nat_prime #c -> Lemma 
  (pointEqual (pointAdd p q) (pointAdd q p))

(* P == P' ==> P + Q == P' + Q *)
assume val curve_compatibility_with_translation_lemma: #c: curve -> p: point_nat_prime #c -> p1: point_nat_prime #c {pointEqual p p1}
  -> q: point_nat_prime #c -> 
  Lemma (pointEqual (pointAdd p q) (pointAdd p1 q))

(* order is the smallest number such that P * order == 0 *)
assume val curve_order_is_the_smallest: #c: curve -> p: point_nat_prime #c -> Lemma
  (forall (n: nat {repeat n (fun x -> pointAdd #c p x) p == pointAtInfinity}). n >= getOrder #c)

(* order * P == 0 *)
assume val curve_multiplication_by_order: #c: curve -> i: int {(i + 1) % getOrder #c = 0} -> p: point_nat_prime -> 
  Lemma (repeat (i % getOrder #c) (fun x -> pointAdd #c p x) p == pointAtInfinity)

(* P + 0 == P *)
assume val curve_point_at_infinity_property: #c: curve -> q: point_nat_prime #c -> Lemma (pointEqual (pointAdd pointAtInfinity q) q)

assume val curve_associativity: #c: curve -> p: point_nat_prime #c -> q: point_nat_prime #c -> r: point_nat_prime #c -> Lemma 
  (pointEqual (pointAdd (pointAdd p q) r) (pointAdd p (pointAdd q r)))



val point_mult_0: #c: curve -> p: point_nat_prime #c -> i: int {i % getOrder #c = 0} -> 
  Lemma (point_mult #c i p == pointAtInfinity)

let point_mult_0 #c p i = curve_multiplication_by_order #c (getOrder #c - 1) p


val point_mult_1: #c: curve ->p: point_nat_prime #c ->  Lemma (point_mult #c 1 p == p)

let point_mult_1 #c p = eq_repeat0 (fun x -> pointAdd #c p x) p 


#push-options "--fuel 1"

val point_mult_ext: #c: curve -> i: int -> p: point_nat_prime #c -> Lemma (
  let f = (fun x -> pointAdd #c p x) in  
  pointEqual (f (point_mult #c i p)) (point_mult #c (i + 1) p))

let point_mult_ext #c i p = 
  let f = (fun x -> pointAdd #c p x) in 
  if i % getOrder #c = 0 then 
    begin
      point_mult_0 #c p 0;
      curve_point_at_infinity_property p;  
      curve_commutativity_lemma pointAtInfinity p; 
      point_mult_1 #c p
    end
  else 
    begin
      unfold_repeat (getOrder #c) f p ((i - 1) % getOrder #c);
      lemma_mod_add_distr 1 (i - 1) (getOrder #c)
    end

#pop-options


val lemma_scalar_reduce: #c: curve -> p: point_nat_prime #c -> pk: int -> Lemma (point_mult pk p == point_mult #c (pk % getOrder #c) p)

let lemma_scalar_reduce #c p pk = 
  assert(point_mult pk p == repeat ((pk - 1) % getOrder #c) (fun x -> pointAdd #c p x) p);
  assert(point_mult #c (pk % getOrder #c) p == repeat ((pk - 1) % getOrder #c % getOrder #c) (fun x -> pointAdd #c p x) p);
  lemma_mod_twice (pk - 1) (getOrder #c)


val point_mult_def: #c: curve -> i: int -> p: point_nat_prime #c -> Lemma 
  (point_mult #c i p == repeat ((i - 1) % getOrder #c) (fun x -> pointAdd #c p x) p)

let point_mult_def #c i p = ()


val lemma_commutativity_extended: #c: curve -> p0: point_nat_prime #c  -> a: point_nat_prime #c -> b: point_nat_prime #c -> 
  Lemma (
    let f = (fun x -> pointAdd #c p0 x) in 
    pointEqual (pointAdd (f a) b) (pointAdd (f b) a))

let lemma_commutativity_extended #c p0 a b = 
  let f = (fun x -> pointAdd #c p0 x) in 
  curve_commutativity_lemma (f b) a;
  curve_commutativity_lemma (pointAdd a (pointAdd p0 b)) (pointAdd (pointAdd p0 b) a);
  curve_commutativity_lemma p0 a; 
  curve_compatibility_with_translation_lemma (pointAdd p0 a) (pointAdd a p0) b;
  curve_associativity a p0 b


val lemma_point_add_minus_plus_same_value: #c: curve -> p0: point_nat_prime #c -> pk: nat -> qk: nat -> i: nat -> Lemma ( 
  let p = pointAdd (point_mult pk p0) (point_mult qk p0) in 
  let p_i = pointAdd (point_mult (pk - i) p0) (point_mult (qk + i) p0) in 
  pointEqual p p_i)

let rec lemma_point_add_minus_plus_same_value #curve p0 pk qk i = 
   match i with 
  |0 -> ()
  | _ -> 
    let o = getOrder #curve in  
    let f = (fun x -> pointAdd #curve p0 x) in 
    lemma_point_add_minus_plus_same_value #curve p0 pk qk (i - 1);
    
    let p = pointAdd (point_mult pk p0) (point_mult qk p0) in 
  
    let a = (point_mult (pk - i + 1) p0) in 
    let b = (point_mult (qk + i - 1) p0) in 
    let c = (point_mult (pk - i) p0) in 
    let d = (point_mult (qk + i) p0) in 

    let p_i1 = pointAdd (point_mult (pk - i + 1) p0) (point_mult (qk + i - 1) p0) in 
    let p_i = pointAdd (point_mult (pk - i) p0) (point_mult (qk + i) p0) in  

    point_mult_def (pk - i + 1) p0;
    point_mult_def (pk - i) p0;
    unfold_repeat o f p0 ((pk - i - 1) % o);

    curve_point_at_infinity_property #curve p0;
    curve_commutativity_lemma pointAtInfinity p0;

    if ((pk - i - 1) % o + 1) < o then 
      begin
	small_mod (((pk - i - 1) % o + 1)) o;
	lemma_mod_add_distr 1 (pk - i - 1) o;
	assert(pointEqual a (f c))
      end 
    else begin
      curve_multiplication_by_order #curve ((pk - i - 1) % o) p0;
      lemma_mod_add_distr 1 (pk - i - 1) o;
      eq_repeat0 f p0;
      assert(pointEqual a (f c))
    end;

    point_mult_def (qk + i - 1) p0;
    point_mult_def (qk + i) p0;
    unfold_repeat o f p0 ((qk + i - 1 - 1) % o);

    if ((qk + i - 1 - 1) % o + 1) < o then 
      begin 
	small_mod (((qk + i - 1 - 1) % o) + 1) o;
	lemma_mod_add_distr 1 (qk + i - 2) o;
	assert (pointEqual d (f b))
      end
    else begin 
      curve_multiplication_by_order #curve ((qk + i - 1 - 1) % o) p0;
      lemma_mod_twice (qk + i - 1 - 1) o;
      point_mult_def (qk + i - 1) p0;
      

      lemma_mod_add_distr 1 (qk + i - 1) o;
      lemma_mod_add_distr 1 (qk + i - 2) o;
      eq_repeat0 f p0;

      point_mult_0 p0 (qk + i - 1);
      point_mult_ext (qk + i - 1) p0;

      assert (pointEqual ((point_mult (qk + i) p0)) p0)

    end;
    curve_compatibility_with_translation_lemma a (f c) b;
    curve_compatibility_with_translation_lemma d (f b) c;
    curve_commutativity_lemma #curve d c;

    lemma_commutativity_extended p0 c b;
    assert(pointEqual p_i1 p_i)


val lemmaApplPointDouble: #c: curve 
  -> p0: point_nat_prime #c 
  -> pk: int
  -> p: point_nat_prime #c {pointEqual p (point_mult pk p0)} ->
  Lemma (pointEqual (pointAdd p p) (point_mult (2 * pk) p0))

let lemmaApplPointDouble #c p0 pk p =  
  let o = getOrder #c in 

  let pk_p = point_mult pk p0 in 

  lemma_point_add_minus_plus_same_value #c p0 (pk % o) (pk % o) ((pk - 1) % o);
  lemma_scalar_reduce p0 pk;

  calc (==) {
    point_mult (pk % o - ((pk - 1) % o)) p0;
    (==) {lemma_scalar_reduce p0 (pk % o - ((pk - 1) % o))}
    point_mult ((pk % o - ((pk - 1) % o)) % o) p0;
    (==) {lemma_mod_add_distr (- ((pk - 1) % o)) pk o}
    point_mult ((pk - ((pk - 1) % o)) % o) p0;
    (==) {lemma_mod_sub_distr pk (pk - 1) o}
    point_mult ((pk - (pk - 1)) % o) p0;
    (==) {lemma_scalar_reduce p0 (pk - (pk - 1))}
    point_mult ((pk - (pk - 1))) p0;
  };

  calc (==) {
    point_mult (pk % o + ((pk - 1) % o)) p0;
    (==) {lemma_scalar_reduce p0 (pk % o + ((pk - 1) % o))}
    point_mult ((pk % o + ((pk - 1) % o)) % o) p0;
    (==) {lemma_mod_add_distr ((pk - 1) % o) pk o}
    point_mult ((pk + ((pk - 1) % o)) % o) p0;
    (==) {lemma_mod_add_distr pk (pk - 1) o}
    point_mult ((pk + pk - 1) % o) p0;
    (==) {lemma_scalar_reduce p0 (pk + pk - 1)}
    point_mult ((pk + pk - 1)) p0;
    
  };
    
  point_mult_1 p0;
  point_mult_ext (2 * pk - 1) p0;

  curve_compatibility_with_translation_lemma p pk_p pk_p


val lemmaApplPointAdd: #c: curve -> p0: point_nat_prime #c 
  -> pk: int
  -> p: point_nat_prime #c {pointEqual p (point_mult pk p0)} 
  -> qk: int
  -> q: point_nat_prime #c {pointEqual q (point_mult qk p0)} -> 
  Lemma (pointEqual (pointAdd p q) (point_mult (pk + qk) p0))

let lemmaApplPointAdd #c p0 pk p qk q = 
  let pk_p = point_mult pk p0 in 
  let qk_p = point_mult qk p0 in 
  
  let o = getOrder #c in 

  lemma_point_add_minus_plus_same_value #c p0 (qk % o) (pk % o) ((qk - 1) % o);
  lemma_scalar_reduce p0 qk;
  lemma_scalar_reduce p0 pk;

  assert(pointEqual (pointAdd (point_mult qk p0) (point_mult pk p0)) 
    (pointAdd (point_mult ((qk % o) - ((qk - 1) % o)) p0) (point_mult (pk % o + ((qk - 1) % o)) p0)));

  calc (==) {
    point_mult ((qk % o) - ((qk - 1) % o)) p0;
    (==) {lemma_scalar_reduce p0 ((qk % o) - ((qk - 1) % o))}
    point_mult (((qk % o) - ((qk - 1) % o)) % o) p0;
    (==) {lemma_mod_add_distr (- ((qk - 1) % o)) qk o}
    point_mult ((qk - ((qk - 1) % o)) % o) p0;
    (==) {lemma_mod_sub_distr qk (qk - 1) o}
    point_mult ((qk - qk + 1) % o) p0;
    (==) {lemma_scalar_reduce p0 1}
    point_mult 1 p0;
  };

  calc (==) {
    point_mult (pk % o + ((qk - 1) % o)) p0;
    (==) {lemma_scalar_reduce p0 (pk % o + ((qk - 1) % o))}
    point_mult ((pk % o + ((qk - 1) % o)) % o) p0;    
    (==) {lemma_mod_add_distr ((qk - 1) % o) pk o}
    point_mult ((pk + ((qk - 1) % o)) % o) p0;    
    (==) {lemma_mod_add_distr pk (qk - 1) o}
    point_mult ((pk + qk - 1) % o) p0;    
    (==) {lemma_scalar_reduce p0 (pk + qk - 1)}
    point_mult (pk + qk - 1) p0;  
  };

  point_mult_1 p0;
  
  point_mult_ext (pk + qk - 1) p0; 
  curve_compatibility_with_translation_lemma p pk_p qk_p;
  curve_compatibility_with_translation_lemma q qk_p p;
   
  curve_commutativity_lemma pk_p qk_p;
  curve_commutativity_lemma p qk_p;
  curve_commutativity_lemma q p



val point_mult_0_lemma: #c: curve -> p: point_nat_prime #c ->  Lemma (point_mult 1 p == p)

let point_mult_0_lemma #c p = 
  Lib.LoopCombinators.eq_repeat0 (fun x -> pointAdd #c p x) p 


val scalar_as_nat_: #c: curve -> scalar_bytes #c -> i: nat {i <= v (getScalarLen c)} -> nat

let rec scalar_as_nat_ #c s i = 
  if i = 0 then 0 else 
  let bit = ith_bit s (v (getScalarLen c) - i) in 
  scalar_as_nat_ #c s (i - 1) * 2 + uint_to_nat bit 

#push-options "--fuel 1 --ifuel 1 --z3rlimit 100"

val scalar_as_nat_zero: #c: curve -> s: scalar_bytes #c ->  Lemma (scalar_as_nat_ s 0 == 0)

let scalar_as_nat_zero #c s = ()




val scalar_as_nat_def: #c: curve -> s: scalar_bytes #c -> i: nat {i > 0 /\ i <= v (getScalarLen c)} -> Lemma (
  scalar_as_nat_ #c s i == 2 * scalar_as_nat_ #c s (i - 1) + uint_to_nat (ith_bit s (v (getScalarLen c) - i)))

let scalar_as_nat_def #c s i = ()


val scalar_as_nat: #c: curve -> scalar_bytes #c -> nat

let scalar_as_nat #c s = scalar_as_nat_ #c s (v (getScalarLen c))

