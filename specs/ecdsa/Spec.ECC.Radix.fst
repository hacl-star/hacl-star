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

val getPrecomputedPoint_Affine: #c: curve -> p: point_nat_prime #c -> i: nat {i < 16} -> 
  Tot (r: point_nat_prime #c {
    isPointAtInfinity #Jacobian r == false /\ (
    if i = 0 then isPointAtInfinity #Affine r 
    else pointEqual r (point_mult #c i p) /\ isPointAtInfinity #Affine r == false)})

let getPrecomputedPoint_Affine #c p i = 
  curve_order_is_the_smallest #c p;
  if i = 0 then (0, 0, 1) else begin
    let r = point_mult #c i p in 
    curve_order_is_the_smallest p;
    (* if a point p belongs to curve, then the result point r belongs to the same curve *)
    (* the point p belongs to the curve, so, the result r belongs to the curve *)
    (* the point (0, 0) does not belong to the curve *)
    assume (isPointAtInfinity #Affine r == false);
    r
  end


val getPrecomputedPoint_Jacobian: #c: curve -> p: point_nat_prime #c -> i: nat -> 
  Tot (r: point_nat_prime #c {pointEqual r (point_mult #c i p)})

let getPrecomputedPoint_Jacobian #c p i = 
  point_mult #c i p
 

val getPrecomputedPoint: #c: curve -> #t: coordSyst -> p: point_nat_prime #c -> i: nat {i < 16} -> 
  Tot (r: point_nat_prime #c {
    match t with 
    |Affine -> 
      if i = 0 then isPointAtInfinity #Affine r 
      else pointEqual r (point_mult #c i p) /\ isPointAtInfinity #Jacobian r == false /\ isPointAtInfinity #Affine r == false
    |Jacobian -> 
      pointEqual r (point_mult #c i p)})

let getPrecomputedPoint #c #t p i = 
  match t with 
  |Affine -> getPrecomputedPoint_Affine #c p i
  |Jacobian -> getPrecomputedPoint_Jacobian #c p i


val repeatAsDoubling: #c: curve -> p: point_nat_prime #c -> i: nat -> Lemma (
  let r = repeat #(point_nat_prime #c) i (_point_double) p in 
  pointEqual r (point_mult #c  (pow2 i) p))

let rec repeatAsDoubling #c p i = 
  match i with 
  |0 -> 
    point_mult_1 #c p;
    eq_repeat0 (_point_double) p
  | _ -> 
    repeatAsDoubling #c p (i - 1);
    
    let r = repeat #(point_nat_prime #c) (i - 1) (_point_double) p in 
    unfold_repeat i _point_double p (i - 1);     
    let ri = repeat #(point_nat_prime #c) i (_point_double) p in 

    let l = point_mult  #c  (pow2 (i - 1)) p in
    let li = point_mult  #c  (pow2 i) p in
    
    lemmaApplPointDouble  #c  p (pow2 (i - 1)) l;
    pow2_double_mult (i - 1); 
    curve_compatibility_with_translation_lemma  #c  r l r


val getPointDoubleNTimes: #c: curve -> p: point_nat_prime #c -> i: nat -> 
  Tot (r: point_nat_prime #c {pointEqual r (point_mult #c (pow2 i) p)})

let getPointDoubleNTimes #c p i = 
  let r = repeat #(point_nat_prime #c) i (_point_double) p in 
  repeatAsDoubling #c p i;
  r


val _ml_step: #c: curve -> #t: coordSyst -> k: scalar_bytes #c 
  -> p0: point_nat_prime #c 
  -> i: nat {v (getScalarLen c) >= (i + 2) * radix} 
  -> p: point_nat_prime #c
  -> point_nat_prime #c

let _ml_step #c #t k p0 i p =
  let scalar = scalar_as_nat k in 
  let l = v (getScalarLen c) in 
  let si = arithmetic_shift_right scalar (l - (i + 2) * radix) % (pow2 radix) in 
  let pRadixed = getPointDoubleNTimes p radix in 
  match t with 
  |Affine -> let pointPrecomputed = getPrecomputedPoint_Affine #c p0 si in _point_add_mixed pRadixed pointPrecomputed
  |Jacobian -> let pointPrecomputed = getPrecomputedPoint_Jacobian #c p0 si in _point_add pRadixed pointPrecomputed


val point_addition_as_point_add_mixed_lemma: #c: curve -> p: point_nat_prime #c -> q: point_nat_prime #c {
  isPointAtInfinity #Affine q  \/ (~ (isPointAtInfinity #Affine q) /\ ~ (isPointAtInfinity #Jacobian q))}  ->
  Lemma (if isPointAtInfinity #Affine q then _point_add_mixed p q == p else _point_add_mixed p q == _point_add p q)

let point_addition_as_point_add_mixed_lemma p q = ()


val lemmaIsPointAtInf: #c: curve ->  q: point_nat_prime #c  ->
  Lemma (requires  (let x, y, z = q in z == 0))
  (ensures isPointAtInfinity #Jacobian q)

let lemmaIsPointAtInf #c q = ()


#push-options " --ifuel 1"

val pointAddDoubleWithTwoPointInfinity: #c: curve -> 
  q: point_nat_prime #c {isPointAtInfinity #Jacobian q} ->
  r: point_nat_prime #c {isPointAtInfinity #Jacobian r} -> 
  Lemma (pointEqual (_point_add #c q r) (pointAdd #c  q r))

let pointAddDoubleWithTwoPointInfinity #c q r = 
   small_mod 0 (getPrime c)

#pop-options 


val curve_distributivity: #c: curve -> p0: point_nat_prime #c 
  -> a: nat  
  -> q: point_nat_prime #c {pointEqual q (point_mult #c  a p0)}
  -> Lemma (pointEqual q (point_mult #c (a % getOrder #c) p0))

let curve_distributivity #c p0 a q = lemma_scalar_reduce #c p0 a

val pointAddNotEqual:  #c: curve ->
  p0: point_nat_prime #c ->
  b: nat -> 
  r: point_nat_prime #c {pointEqual r (point_mult #c b p0)} ->
  a: nat -> 
  q: point_nat_prime #c {pointEqual q (point_mult #c a p0)} -> 
  Lemma 
  (requires ((a < b \/ isPointAtInfinity #Jacobian r) /\ a < getOrder #c))
  (ensures (
    if isPointAtInfinity #Jacobian q && isPointAtInfinity #Jacobian  r then 
      pointEqual (_point_add #c q r) (pointAdd #c  q r) 
    else 
      ~ (pointEqual q r) /\ ~ (pointEqual r q)) )
  

let pointAddNotEqual #c p0 b r a q = 
  if isPointAtInfinity #Jacobian q && isPointAtInfinity #Jacobian r then 
    pointAddDoubleWithTwoPointInfinity q r
  else if isPointAtInfinity #Jacobian q then ()
  else if isPointAtInfinity #Jacobian r then () 
  else begin
    let order = getOrder #c in 
    let aPrime = getOrder #c - a in 
    let qPrime = point_mult #c  aPrime p0 in 
    let aQprime = pointAdd #c  q qPrime in 
    lemmaApplPointAdd #c p0 a q aPrime qPrime;
    point_mult_0 #c  p0 (a + aPrime);

  if (aPrime + b < order) then 
    begin
      curve_order_is_the_smallest #c  p0;
      assert(~ (isPointAtInfinity  #Jacobian (point_mult #c (aPrime + b) p0)));
      assert(~ (pointEqual q r))
    end
  else 
    begin
      assert(aPrime + b >= order);
      assert(a < b);
      curve_distributivity p0 (aPrime + b) (point_mult #c (aPrime + b) p0);
      assert(pointEqual (point_mult #c  (aPrime + b) p0) (point_mult #c  ((aPrime + b) % order) p0));
      curve_order_is_the_smallest #c  p0
    end
  end


val curve_multiplication_distributivity: 
  #c: curve ->
  p0: point_nat_prime #c ->
  a: nat -> 
  q: point_nat_prime #c {pointEqual q (point_mult #c a p0)} ->
  b: nat -> 
  r: point_nat_prime #c {pointEqual r (point_mult #c  b q)} -> 
  Lemma (pointEqual r (point_mult #c  (a * b) p0))


let rec curve_multiplication_distributivity #c p0 a q b r = 
  match b with 
  |0 -> 
    point_mult_0 #c  q 0; 
    point_mult_0 #c  p0 0
  |_ -> 
    let r1 = point_mult #c  (b - 1) q in 
    curve_multiplication_distributivity #c p0 a q (b - 1) r1;
    let a_1 = point_mult #c  (a * (b - 1)) p0 in 
    let a0 = point_mult #c  (a * b) p0 in 

    curve_compatibility_with_translation_lemma #c  q (point_mult #c  a p0) a_1;
    assert(pointEqual (pointAdd #c  q a_1) (pointAdd #c  (point_mult #c  a p0) a_1));
    lemmaApplPointAdd #c  p0 a (point_mult #c  a p0) (a * (b - 1)) a_1;

    let open FStar.Tactics in 
    let open FStar.Tactics.Canon in 
    assert_by_tactic (a + (a * (b - 1)) == a * b) canon;
    assert(pointEqual (pointAdd #c  (point_mult #c  a p0) a_1) a0);
    curve_commutativity_lemma #c  q a_1;
    point_mult_1 #c  q; 
    lemmaApplPointAdd #c  q (b - 1) r1 1 q;
    curve_compatibility_with_translation_lemma #c  r1 (point_mult #c  (a * (b - 1)) p0) q


val pred0: #c: curve -> #t: coordSyst -> x: point_nat_prime #c 
  -> s: scalar_bytes #c {scalar_as_nat s < getOrder #c} 
  -> p0: point_nat_prime #c 
  -> i: nat {v (getScalarLen c) >= (i + 2) * radix}  ->
  Lemma (
    let l = v (getScalarLen c) in 
    let len =  (l / radix) - 1 in 
    let f = _ml_step #c #t s p0 in
    let pred (i: nat {v (getScalarLen c) >= (i + 1) * radix}) p = (
      let scalar = scalar_as_nat s in 
      let partialScalar = arithmetic_shift_right scalar (l - (i + 1) * radix) in  
      pointEqual p (point_mult #c  partialScalar p0)) in
    pred i x ==> pred (i + 1) (f i x))


let pred0 #c #t x s p0 i =
  let scalar = scalar_as_nat s in 
  let order = getOrder #c in 
  let l = v (getScalarLen c) in 
  let partialScalar = arithmetic_shift_right scalar (l - (i + 1) * radix) in 

  if pointEqual x (point_mult  #c  partialScalar p0) then begin
    let si = arithmetic_shift_right scalar (l - (i + 2) * radix) % (pow2 radix) in 
    let pointPrecomputed = getPrecomputedPoint #c #t p0 si in 
    let pRadixed = getPointDoubleNTimes x radix in 
    let p = (
      match t with 
      |Affine -> _point_add_mixed #c pRadixed pointPrecomputed 
      |Jacobian -> _point_add pRadixed pointPrecomputed) in 

    curve_multiplication_distributivity #c p0 partialScalar x (pow2 radix) pRadixed;

    let b = pow2 radix * partialScalar in 
    
    if si > 0 && partialScalar > 0 then 
      assert(si < pow2 radix * partialScalar)
    else begin assert(si = 0 || partialScalar = 0);
      if si = 0 then 
	if partialScalar = 0 then begin
	  point_mult_0 #c  p0 0;
	  assert(isPointAtInfinity #t pointPrecomputed /\ isPointAtInfinity #Jacobian pRadixed) end
	else 
	  assert(si < b)
      else
	begin
	  assert(partialScalar = 0);
	  point_mult_0 #c p0 0;
	  assert(isPointAtInfinity #Jacobian pRadixed)
	end 
    end;

    assert(match t with 
      |Affine ->
	point_addition_as_point_add_mixed_lemma pRadixed pointPrecomputed;
	if si = 0 then begin
	  pointEqual p (point_mult (si + partialScalar * pow2 radix) p0)
	  end
	else begin
	  pointAddNotEqual p0 b pRadixed si pointPrecomputed;
	  lemmaApplPointAdd #c p0 (pow2 radix * partialScalar) pRadixed si pointPrecomputed;
	  pointEqual p (point_mult (si + partialScalar * pow2 radix) p0)
	  end
      |Jacobian ->
	pointAddNotEqual p0 b pRadixed si pointPrecomputed;
	lemmaApplPointAdd #c p0 (pow2 radix * partialScalar) pRadixed si pointPrecomputed;
	curve_commutativity_lemma pRadixed pointPrecomputed;
	pointEqual p (point_mult (si + pow2 radix * partialScalar) p0));


    let a = scalar / (pow2 (l - (i + 2) * radix)) in 
    lemma_div_mod (div scalar (pow2 (l - (i + 2) * radix))) (pow2 radix);
    division_multiplication_lemma scalar (pow2 (l - (i + 2) * radix)) (pow2 radix);
    pow2_plus (l - (i + 2) * radix) radix
      
    end


val lemma_predicate0: #c: curve -> #t: coordSyst 
  -> s: scalar_bytes #c  {scalar_as_nat s < getOrder #c} -> p0: point_nat_prime #c -> 
  Lemma (
    let l = v (getScalarLen c) in 
    let len =  (l / radix) - 1 in 
    let f = _ml_step #c #t s p0 in
    let pred (i: nat {v (getScalarLen c) >= (i + 1) * radix}) p : Type0 = (
      let scalar = scalar_as_nat s in 
      let partialScalar = arithmetic_shift_right scalar (l - (i + 1) * radix) in  
      pointEqual p (point_mult #c  partialScalar p0)) in 
  
  forall (i: nat {i < len}) (x: point_nat_prime #c). pred i x ==> pred (i + 1) (f i x))

let lemma_predicate0 #c #t s p0 = 
  let pred = pred0 #c #t in
  Classical.forall_intro_4 pred


val radix_spec: #c: curve -> #t: coordSyst -> 
  s: scalar_bytes #c {v (getScalarLen c) % radix == 0 /\ scalar_as_nat s < getOrder #c}
  -> i: point_nat_prime #c
  -> r: point_nat_prime #c {
    pointEqual r (point_mult #c  (scalar_as_nat #c s) i)}


let radix_spec #c #t s p0 = 
  let scalarNat = scalar_as_nat s in 
  let l = v (getScalarLen c) in  
    scalar_as_nat_upperbound s l;
    lemma_div_lt_nat scalarNat l radix;
  let pointToStart = getPrecomputedPoint #c #t p0 (arithmetic_shift_right scalarNat (l - radix)) in  
  
  let len = (l / radix) - 1 in 
  let pred (i: nat {v (getScalarLen c) >= (i + 1) * radix}) p : Type0 = (
    let scalar = scalar_as_nat s in 
    let partialScalar = arithmetic_shift_right scalar (l - (i + 1) * radix) in  
    pointEqual p (point_mult #c  partialScalar p0)) in 
  
  let f = _ml_step #c #t s p0 in 
  lemma_predicate0 #c #t s p0; 

  assert(
    match t with 
    |Jacobian -> pred 0 pointToStart 
    |Affine -> 
      let si = (arithmetic_shift_right scalarNat (l - radix)) in 
      if si = 0 then 
	begin
	  point_mult_0 p0 0;
	  pred 0 pointToStart
	end
	else 
      pointEqual pointToStart (point_mult #c si p0));

  let r = repeati_inductive' #(point_nat_prime #c) len pred f pointToStart in 
  
  assert(
    let scalar = scalar_as_nat s in 
    pointEqual r (point_mult #c  scalar p0));
  r
