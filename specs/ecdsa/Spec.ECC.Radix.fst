module Spec.ECC.Radix

open FStar.Mul

open Lib.ByteSequence
open Lib.IntTypes
open Lib.Sequence
open Lib.RawIntTypes

open Lib.LoopCombinators 

open FStar.Math.Lemmas
open FStar.Math.Lib

open Spec.ECC.Curves

open Spec.ECC


#set-options "--fuel 0 --ifuel 0 --z3rlimit 100"

let radix = 4

val getPrecomputedPoint: #c: curve -> p: point_nat_prime #c -> i: nat -> 
  Tot (r: point_nat_prime #c {pointEqual r (point_mult i p)})

let getPrecomputedPoint #c p i = 
  point_mult i p


val repeatAsDoubling: #c: curve -> p: point_nat_prime #c -> i: nat -> Lemma (
  let r = repeat #(point_nat_prime #c) i (_point_double) p in 
  pointEqual r (point_mult (pow2 i) p))

let rec repeatAsDoubling #c p i = 
  match i with 
  |0 -> 
    point_mult_1 p;
    eq_repeat0 (_point_double) p
  | _ -> 
    repeatAsDoubling #c p (i - 1);
    
    let r = repeat #(point_nat_prime #c) (i - 1) (_point_double) p in 
    unfold_repeat i _point_double p (i - 1);     
    let ri = repeat #(point_nat_prime #c) i (_point_double) p in 

    let l = point_mult (pow2 (i - 1)) p in
    let li = point_mult (pow2 i) p in 
    
    lemmaApplPointDouble p (pow2 (i - 1)) l;
    pow2_double_mult (i - 1); 
    curve_compatibility_with_translation_lemma r l r


val getPointDoubleNTimes: #c: curve -> p: point_nat_prime #c -> i: nat -> 
  Tot (r: point_nat_prime #c {pointEqual r (point_mult (pow2 i) p)})

let getPointDoubleNTimes #c p i = 
  let r = repeat #(point_nat_prime #c) i (_point_double) p in 
  repeatAsDoubling #c p i;
  r


val _ml_step: #c: curve -> k: scalar_bytes #c 
  -> p0: point_nat_prime #c 
  -> i: nat{v (getScalarLen c)  >= (i + 2) * radix} 
  -> p: point_nat_prime #c
  -> point_nat_prime #c

let _ml_step #c k p0 i p =
  let scalar = scalar_as_nat k in 
  let l = v (getScalarLen c) in 
  let si = arithmetic_shift_right scalar (l - (i + 2) * radix) % (pow2 radix) in 
  let pointPrecomputed = getPrecomputedPoint p0 si in 

  let pRadixed = getPointDoubleNTimes p radix in 
  _point_add pointPrecomputed pRadixed


val lemmaIsPointAtInf: #c: curve ->  q: point_nat_prime #c  ->
  Lemma (requires  (let x, y, z = q in z == 0))
  (ensures isPointAtInfinity q)

let lemmaIsPointAtInf #c q = ()


#push-options "--fuel 1 --ifuel 1 --z3rlimit 100"

val pointAddDoubleWithTwoPointInfinity: #c: curve -> 
  q: point_nat_prime #c {isPointAtInfinity q} ->
  r: point_nat_prime #c {isPointAtInfinity r} -> 
  Lemma (pointEqual (_point_add q r) (pointAdd q r))

let pointAddDoubleWithTwoPointInfinity #c q r = 
   small_mod 0 (getPrime c)

#pop-options 


val pred0: #c: curve -> x: point_nat_prime #c 
  -> s: scalar_bytes #c {scalar_as_nat s < getOrder #c} 
  -> p0: point_nat_prime #c 
  -> i: nat {v (getScalarLen c) >= (i + 2) * radix}  ->
  Lemma (
    let l = v (getScalarLen c) in 
    let len =  (l / radix) - 1 in 
    let f = _ml_step #c s p0 in
    let pred (i: nat {v (getScalarLen c) >= (i + 1) * radix}) p = (
      let scalar = scalar_as_nat s in 
      let partialScalar = arithmetic_shift_right scalar (l - (i + 1) * radix) in  
      pointEqual p (point_mult #c partialScalar p0)) in
    pred i x ==> pred (i + 1) (f i x))

val curve_distributivity: #c: curve -> p0: point_nat_prime #c 
  -> a: nat  
  -> q: point_nat_prime #c {pointEqual q (point_mult a p0)}
  -> Lemma (pointEqual q (point_mult (a % getOrder #c) p0))

let curve_distributivity #c p0 a q = lemma_scalar_reduce p0 a


val pointAddNotEqual:  #c: curve -> 
  p0: point_nat_prime #c ->
  a: nat -> 
  q: point_nat_prime #c {pointEqual q (point_mult a p0)} ->
  b: nat -> 
  r: point_nat_prime #c {pointEqual r (point_mult b p0)} -> 
  Lemma 
  (requires ((a < b \/ isPointAtInfinity r) /\ a < getOrder #c))
  (ensures (if isPointAtInfinity q && isPointAtInfinity r then pointEqual (_point_add q r) (pointAdd q r) else ~ (pointEqual q r)))
  

let pointAddNotEqual #c p0 a q b r = 
  if isPointAtInfinity q && isPointAtInfinity r then 
    pointAddDoubleWithTwoPointInfinity q r
  else if isPointAtInfinity q then ()
  else if isPointAtInfinity r then () 
  else begin
    let order = getOrder #c in 
    let aPrime = getOrder #c - a in 
    let qPrime = point_mult aPrime p0 in 
    let aQprime = pointAdd q qPrime in 
    lemmaApplPointAdd p0 a q aPrime qPrime;

    point_mult_0 p0 (a + aPrime);
    
  if (aPrime + b < order) then 
    begin
      curve_order_is_the_smallest #c p0;
      assert(~ (isPointAtInfinity (point_mult (aPrime + b) p0)));
      assert(~ (pointEqual q r))
    end
  else 
    begin
      curve_distributivity p0 (aPrime + b) (point_mult (aPrime + b) p0);
      curve_order_is_the_smallest #c p0

    end
  
  end


val curve_multiplication_distributivity: 
  #c: curve ->
  p0: point_nat_prime #c ->
  a: nat -> 
  q: point_nat_prime #c {pointEqual q (point_mult a p0)} ->
  b: nat -> 
  r: point_nat_prime #c {pointEqual r (point_mult b q)} -> 
  Lemma (pointEqual r (point_mult (a * b) p0))


let rec curve_multiplication_distributivity #c p0 a q b r = 
  match b with 
  |0 -> 
    point_mult_0 q 0; 
    point_mult_0 p0 0
  |_ -> 
    let r1 = (point_mult (b - 1) q) in 
    curve_multiplication_distributivity #c p0 a q (b - 1) r1;
    let a_1 = point_mult (a * (b - 1)) p0 in 
    let a0 = point_mult (a * b) p0 in 

    curve_compatibility_with_translation_lemma q (point_mult a p0) a_1;
    assert(pointEqual (pointAdd q a_1) (pointAdd (point_mult a p0) a_1));
    lemmaApplPointAdd p0 a (point_mult a p0) (a * (b - 1)) a_1;

    let open FStar.Tactics in 
    let open FStar.Tactics.Canon in 
    assert_by_tactic (a + (a * (b - 1)) == a * b) canon;
    assert(pointEqual (pointAdd (point_mult a p0) a_1) a0);
    curve_commutativity_lemma q a_1;
    point_mult_1 q; 
    lemmaApplPointAdd q (b - 1) r1 1 q;

    curve_compatibility_with_translation_lemma r1 (point_mult (a * (b - 1)) p0) q
 

let pred0 #c x s p0 i =
  let scalar = scalar_as_nat s in 
  let l = v (getScalarLen c) in 
  let len =  (l / radix) - 1 in 
  let partialScalar = arithmetic_shift_right scalar (l - (i + 1) * radix) in 

  let pred (i: nat {v (getScalarLen c) >= (i + 1) * radix}) p = (
    let partialScalar = arithmetic_shift_right scalar (l - (i + 1) * radix) in  
    pointEqual p (point_mult #c partialScalar p0)) in 

  if pointEqual x (point_mult #c partialScalar p0) then begin
    let p = _ml_step #c s p0 i x in 
    let si = arithmetic_shift_right scalar (l - (i + 2) * radix) % (pow2 radix) in 

    let pointPrecomputed = getPrecomputedPoint p0 si in 
    let pRadixed = getPointDoubleNTimes x radix in 

    curve_multiplication_distributivity #c p0 partialScalar x (pow2 radix) pRadixed;

    let b : nat = pow2 radix * partialScalar in 
    let order = getOrder #c in 
    let q = pointPrecomputed in 


    if si > 0 && partialScalar > 0 then 
      assert(si < b)
    else
      begin
	assert(si = 0 || partialScalar = 0);
	  if si = 0 then 
	    if partialScalar = 0 then 
	      begin
		point_mult_0 p0 0;
		assert(isPointAtInfinity pointPrecomputed /\ isPointAtInfinity pRadixed)
	      end
	    else 
	      begin
		assert(si < b)
	      end
	  else
	    begin
	    point_mult_0 p0 0
	    end end;

    pointAddNotEqual p0 si pointPrecomputed b pRadixed;
    lemmaApplPointAdd p0 si pointPrecomputed (pow2 radix * partialScalar) pRadixed;

    let a = scalar / (pow2 (l - (i + 2) * radix)) in 
    lemma_div_mod (div scalar (pow2 (l - (i + 2) * radix))) (pow2 radix);
    division_multiplication_lemma scalar (pow2 (l - (i + 2) * radix)) (pow2 radix);
    pow2_plus (l - (i + 2) * radix) radix
    end


val lemma_predicate0: #c: curve -> s: scalar_bytes #c  {scalar_as_nat s < getOrder #c}  -> p0: point_nat_prime #c -> 
  Lemma (
    let l = v (getScalarLen c) in 
    let len =  (l / radix) - 1 in 
    
    let f = _ml_step #c s p0 in
    
    let pred (i: nat {v (getScalarLen c) >= (i + 1) * radix}) p : Type0 = (
      let scalar = scalar_as_nat s in 
      let partialScalar = arithmetic_shift_right scalar (l - (i + 1) * radix) in  
      pointEqual p (point_mult #c partialScalar p0)) in 
  
  forall (i: nat {i < len}) (x: point_nat_prime #c). pred i x ==> pred (i + 1) (f i x))

let lemma_predicate0 #c s p0 = 
  let pred = pred0 #c in
  Classical.forall_intro_4 pred


val radix_spec: #c: curve -> s: scalar_bytes #c {v (getScalarLen c) % radix == 0 /\ scalar_as_nat s < getOrder #c}
  -> i: point_nat_prime #c
  -> r: point_nat_prime #c {
    let pointStart = getPrecomputedPoint i (scalar_as_nat s % pow2 radix) in 
    pointEqual r (point_mult (scalar_as_nat #c s) i)}


let radix_spec #c s p0 = 
  let scalarNat = scalar_as_nat s in 
  let l = v (getScalarLen c) in 
  let pointToStart = getPrecomputedPoint p0 (arithmetic_shift_right scalarNat (l - radix)) in  
  
  let len =  (l / radix) - 1 in 
  
  let pred (i: nat {v (getScalarLen c) >= (i + 1) * radix}) p : Type0 = (
    let scalar = scalar_as_nat s in 
    let partialScalar = arithmetic_shift_right scalar (l - (i + 1) * radix) in  
    pointEqual p (point_mult #c partialScalar p0)) in 

  let f = _ml_step #c s p0 in 
  
  lemma_predicate0 s p0; 
  let r = repeati_inductive' #(point_nat_prime #c) len pred f pointToStart in 

  assert(
    let scalar = scalar_as_nat s in 
    pointEqual r (point_mult #c scalar p0));


  r
