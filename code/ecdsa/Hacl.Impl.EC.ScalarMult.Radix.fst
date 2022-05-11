module Hacl.Impl.EC.ScalarMult.Radix

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer
open Lib.Loops

open Spec.ECC
open Spec.ECC.Curves
open Hacl.Impl.EC.Masking

open Hacl.Spec.EC.Definition

open Hacl.Impl.EC.PointAdd
open Hacl.Impl.EC.PointDouble

open Hacl.Spec.MontgomeryMultiplication

open Hacl.Impl.EC.Masking.ScalarAccess
open Hacl.Impl.EC.Precomputed

open FStar.Mul

open Lib.LoopCombinators
open Hacl.Spec.EC.ScalarMult.Radix


#set-options "--z3rlimit 200 --max_ifuel 0 --max_fuel 0 "

inline_for_extraction noextract
val getPointDoubleNTimes: #c: curve 
  -> p: point c 
  -> tempBuffer: lbuffer uint64 (size 17 *! getCoordinateLenU64 c) ->
  Stack unit
  (requires fun h -> live h p /\ live h tempBuffer /\ disjoint p tempBuffer /\ point_eval c h p)
  (ensures fun h0 _ h1 -> modifies (loc p |+| loc tempBuffer) h0 h1 /\ point_eval c h1 p /\
    fromDomainPoint #c #DH (point_as_nat c h1 p) == Spec.ECC.Radix.getPointDoubleNTimes #c
      (fromDomainPoint #c #DH (point_as_nat c h0 p)) 4)

let getPointDoubleNTimes #c p tempBuffer = 
  let h0 = ST.get() in 
  let inv h (k: nat) = live h p /\ live h tempBuffer /\ disjoint p tempBuffer /\ point_eval c h p /\ 
    modifies (loc p |+| loc tempBuffer) h0 h /\
    fromDomainPoint #c #DH (point_as_nat c h p) ==
      Lib.LoopCombinators.repeat k (_point_double #c) (fromDomainPoint #c #DH (point_as_nat c h0 p)) in 
  Lib.LoopCombinators.eq_repeat0 (_point_double #c) (fromDomainPoint #c #DH (point_as_nat c h0 p));  
  for 0ul 4ul inv (fun i -> 
    point_double p p tempBuffer; 
    unfold_repeat 4 (_point_double #c) (fromDomainPoint #c #DH (point_as_nat c h0 p)) (v i))


val curve_compatibility_with_translation_lemma_1: #c: curve 
  -> p: Spec.ECC.point #c #Jacobian 
  -> p1: Spec.ECC.point #c #Jacobian
  -> q: Spec.ECC.point #c #Jacobian -> 
  Lemma (pointEqual p p1 <==> pointEqual (pointAdd #c q p) (pointAdd #c q p1))

let curve_compatibility_with_translation_lemma_1 #c p p1 q = 
  curve_compatibility_with_translation_lemma p p1 q;
  curve_commutativity_lemma p q;
  curve_commutativity_lemma p1 q


val lemma_point_mult_addition_of_coefficients: #c: curve 
  -> a: nat 
  -> k: nat
  -> p: Spec.ECC.point #c #Jacobian ->
  Lemma (pointEqual (pointAdd (point_mult a p) (point_mult k p)) (point_mult (k + a) p))

let rec lemma_point_mult_addition_of_coefficients #c a k p = 
  match a with
  | 0 -> 
    point_mult_0 p 0;
    curve_point_at_infinity_property (point_mult k p)
  | _ -> 
    lemma_point_mult_addition_of_coefficients #c (a - 1) k p;
    let pa = point_mult a p in  
    let pa1 = point_mult (a - 1) p in  
    let kp = point_mult k p in 
    
    curve_compatibility_with_translation_lemma_1 (pointAdd pa1 kp)  (point_mult (k + a - 1) p) p;
    point_mult_ext (k + a - 1) p;

    curve_associativity p pa1 kp;
    point_mult_ext (a - 1) p;

    curve_compatibility_with_translation_lemma (pointAdd #c p pa1) pa kp


val lemma_nat_distribitivity: a: nat -> b: nat -> Lemma (a * (b - 1) + a == a * b)

let lemma_nat_distribitivity a b = ()


val lemma_point_mult_associativity: #c: curve 
  -> a: nat 
  -> b: nat 
  -> p: Spec.ECC.point #c #Jacobian -> 
  Lemma (pointEqual (point_mult b (point_mult a p)) (point_mult (a * b) p))

let rec lemma_point_mult_associativity #c a b p = 
  match b with 
  |0 -> 
    point_mult_0 p 0;
    point_mult_0 (point_mult a p) 0
  |_ ->
    lemma_point_mult_associativity #c a (b - 1) p;
    assert(pointEqual (point_mult (b - 1) (point_mult a p)) (point_mult (a * (b - 1)) p));

    let pa = point_mult a p in 
    point_mult_def a p;
    point_mult_def (b - 1) pa;
    point_mult_def (a * (b - 1)) p;

    point_mult_ext #c (b - 1) pa; 

    lemma_point_mult_addition_of_coefficients a (a * (b - 1)) p;
    lemma_nat_distribitivity a b;
    assert(pointEqual (pointAdd (point_mult a p) (point_mult (a * (b - 1)) p)) (point_mult (a * b) p));

    curve_compatibility_with_translation_lemma_1 (point_mult (b - 1) pa) (point_mult (a * (b - 1)) p) pa;
    curve_compatibility_with_translation_lemma (pointAdd #c pa (point_mult (b - 1) pa)) (point_mult b pa) (pointAdd pa (point_mult (a * (b - 1)) p));
    curve_compatibility_with_translation_lemma (pointAdd #c pa (point_mult (a * (b - 1)) p)) (point_mult (a * b) p) (point_mult b pa)


val lemma_point_mult_equal_points: #c: curve 
  -> p0: Spec.ECC.point #c 
  -> p1: Spec.ECC.point #c {pointEqual p0 p1} 
  -> i: nat -> 
  Lemma (pointEqual (point_mult i p0) (point_mult i p1))

let rec lemma_point_mult_equal_points #c p0 p1 i = 
  match i with 
  |0 -> point_mult_0 p0 0; point_mult_0 p1 0
  |_ -> 
    lemma_point_mult_equal_points #c p0 p1 (i - 1);
    point_mult_ext (i - 1) p0;
    point_mult_ext (i - 1) p1; 
    curve_compatibility_with_translation_lemma p0 p1 (point_mult (i - 1) p0);
    curve_compatibility_with_translation_lemma_1  (point_mult (i - 1) p0) (point_mult (i - 1) p1) p1


val lemma_point_mult_of_point_infinity: #c: curve 
  -> p: Spec.ECC.point #c {isPointAtInfinity #c p} 
  -> a: nat ->
  Lemma (isPointAtInfinity (point_mult a p))

let rec lemma_point_mult_of_point_infinity #c p a = 
  match a with 
  |0 -> point_mult_0 p 0 
  |_ -> 
    lemma_point_mult_of_point_infinity #c p (a - 1);
    curve_point_at_infinity_property (point_mult (a - 1) p);
    point_mult_ext (a - 1) p


val not_equal_precomputed1: #c: curve 
  -> a: nat {a <= 16} 
  -> b: nat {b < getOrder #c}
  -> p0: Spec.ECC.point #c #Jacobian -> 
  Lemma (
    let pa = point_mult #c a p0 in 
    let pb = point_mult #c b p0 in 
    ~ (pointEqual pa pb) \/ (isPointAtInfinity #c #Jacobian pa /\ isPointAtInfinity #c #Jacobian pb))

let not_equal_precomputed1 #c a b p0 = 
  let pa = point_mult #c a p0 in 
  let pb = point_mult #c b p0 in  

  if (isPointAtInfinity #c p0) then begin
     lemma_point_mult_of_point_infinity p0 a;
     lemma_point_mult_of_point_infinity p0 b
    end
  else 
    if a = 0 || b = 0 then 
       point_mult_0 #c p0 0
    else
      if pointEqual pa pb then 
      begin
	let inv_pb = point_mult #c (getOrder #c - b) p0 in 
	curve_compatibility_with_translation_lemma pa pb inv_pb;
	
	lemma_point_mult_addition_of_coefficients #c b (getOrder #c - b) p0;
	point_mult_0 p0 (getOrder #c); 
	assert(isPointAtInfinity (pointAdd pb inv_pb));

	lemma_point_mult_addition_of_coefficients #c a (getOrder #c - b) p0;
	assert(pointEqual (pointAdd pa inv_pb) (point_mult (a - b + getOrder #c) p0));

	curve_order_is_the_smallest p0;  
	assert(~ (isPointAtInfinity (point_mult (a - b + getOrder #c) p0)));

	assert(False)
      end


val not_equal_precomputed: #c: curve 
  -> z: nat
  -> p: Spec.ECC.point #c #Jacobian
  -> p0: Spec.ECC.point #c #Jacobian 
  -> si: nat {si <= 16} -> 
  Lemma
  (requires ((z <= getOrder #c / 16) /\ pointEqual p (point_mult #c z p0)))
  (ensures (
    let p_16 = Spec.ECC.Radix.getPointDoubleNTimes #c p 4 in 
    ~ (pointEqual #c p_16 (point_mult #c si p0)) \/ (
    isPointAtInfinity #c #Jacobian p_16 /\ isPointAtInfinity #c #Jacobian (point_mult #c si p0))))

let not_equal_precomputed #c z p p0 si = 
  lemma_point_mult_associativity #c z 16 p0;
  lemma_point_mult_equal_points (point_mult z p0) p 16;
  not_equal_precomputed1 #c si (16 * z) p0


val get_exists_: #c: curve
  -> p0: Spec.ECC.point #c #Jacobian 
  -> p: Spec.ECC.point #c #Jacobian 
    {exists (z: nat). ((z <= getOrder #c / 16) /\ pointEqual p (point_mult #c z p0))}
  -> z_test: nat {forall (z: nat {z < z_test}).
    ~  ((z <= getOrder #c / 16) /\ pointEqual p (point_mult #c z p0))}
  -> Tot (z: nat { (z <= getOrder #c / 16) /\ pointEqual p (point_mult #c z p0)})
  (decreases (getOrder #c - z_test))

let rec get_exists_ #c p0 p z = 
  if (z <= getOrder #c / 16) && pointEqual p (point_mult #c z p0) 
  then z
  else get_exists_ #c p0 p (z + 1)


val get_exists: #c: curve
  -> p0: Spec.ECC.point #c #Jacobian 
  -> p: Spec.ECC.point #c #Jacobian 
    {exists (z: nat). ((z <= getOrder #c / 16) /\ pointEqual p (point_mult #c z p0))}
  -> Tot (z: nat { ((z <= getOrder #c / 16) /\ pointEqual p (point_mult #c z p0))})

let get_exists #c p0 p = get_exists_ #c p0 p 0


val not_equal_precomputed2: #c: curve 
  -> p0: Spec.ECC.point #c #Jacobian
  -> p: Spec.ECC.point #c #Jacobian
       { exists (z: nat {z <= getOrder #c / 16}). pointEqual p (point_mult #c z p0)}
  -> si: nat {si <= 16} -> 
  Lemma (
    let p_16 = Spec.ECC.Radix.getPointDoubleNTimes #c p 4 in 
    ~ (pointEqual #c p_16 (point_mult #c si p0)) \/ (
    isPointAtInfinity #c #Jacobian p_16 /\ isPointAtInfinity #c #Jacobian (point_mult #c si p0)))

let not_equal_precomputed2 #c p0 p si = 
  let z = get_exists #c p0 p in 
  not_equal_precomputed #c z p p0 si
  
  
val lemma_point_at_infinity_after_point_double: #c: curve 
  -> p: Spec.ECC.point #c #Jacobian {isPointAtInfinity #c p} -> 
  Lemma (isPointAtInfinity #c (_point_double p))

let lemma_point_at_infinity_after_point_double #c p = 
  let pd = _point_double p in 
  
  let prime = getPrime c in 
  let x, y, _ = toJacobianCoordinates p in

  let gamma = y * y in 
  let beta = x * gamma in 
  let alpha = 3 * x * x in 
  let x3 = (alpha * alpha - 8 * beta) % prime in 
  let y3 = (alpha * (4 * beta - x3) - 8 * gamma * gamma) % prime in 
  let z3 = (y * y  - gamma) % prime in 

  FStar.Math.Lemmas.small_mod 0 prime;  
  assert (z3 == 0);
  assert (isPointAtInfinity #c (x3, y3, z3))


inline_for_extraction noextract  
val radix_step_precomputed: #c: curve -> #buf_type: buftype 
  -> p: point c
  -> tempBuffer: lbuffer uint64 (size 17 *! getCoordinateLenU64 c) 
  -> scalar: scalar_t #buf_type #c
  -> i: size_t{v i >= 1 /\ v i < v (getScalarLenBytes c) * 2} -> 
  Stack unit
  (requires fun h -> 
    live h p /\ live h tempBuffer /\ live h scalar /\ point_eval c h p /\ (
    let fromDomainP = fromDomainPoint #c #DH (point_as_nat c h p) in 
    exists (z: nat {z <= getOrder #c / 16}). 
      pointEqual fromDomainP (point_mult #c z (basePoint #c)) /\
    LowStar.Monotonic.Buffer.all_disjoint [loc p; loc tempBuffer; loc scalar]))
  (ensures fun h0 _ h1 -> modifies (loc p |+| loc tempBuffer) h0 h1 /\ point_eval c h1 p /\ (
    let fromDomainP_h0 = fromDomainPoint #c #DH (point_as_nat c h0 p) in 
    let fromDomainP_h1 = fromDomainPoint #c #DH (point_as_nat c h1 p) in 
    pointEqual fromDomainP_h1
      (Spec.ECC.Radix.radix_step #c #Affine (as_seq h0 scalar) (basePoint #c) (v i - 1) fromDomainP_h0)))

let radix_step_precomputed #c p tempBuffer scalar i = 
    let h0 = ST.get() in 
    push_frame(); 
  let pointToAdd = create (size 2 *! getCoordinateLenU64 c) (u64 0) in 
  getPointPrecomputedMixed #c scalar i pointToAdd; 
    let h1 = ST.get() in
    Hacl.Impl.P.PointAdd.Aux.lemma_coord_eval c h0 h1 p; 
  getPointDoubleNTimes #c p tempBuffer;
    let h2 = ST.get() in
  Hacl.Impl.EC.PointAddMixed.point_add_mixed #c p pointToAdd p tempBuffer;
    let h3 = ST.get() in
    pop_frame();


    let scalar = scalar_as_nat (as_seq h0 scalar) in 
    let si = Math.Lib.arithmetic_shift_right scalar (v (getScalarLen c) - ((v i - 1) + 2) * 4) % pow2 4 in  
    let pRadixed = Spec.ECC.Radix.getPointDoubleNTimes #c (fromDomainPoint #c #DH (point_as_nat c h0 p)) 4 in
    let pointPrecomputed = Spec.ECC.Radix.getPrecomputedPoint #c #Affine (basePoint #c) si in 

    curve_compatibility_with_translation_lemma_1  (fromDomainPoint #c #DH (toJacobianCoordinates #c (point_affine_as_nat c h1 pointToAdd))) (point_mult #c si (basePoint #c)) pRadixed;

    not_equal_precomputed2 #c (basePoint #c) (fromDomainPoint #c #DH (point_as_nat c h0 p)) si;

    if (isPointAtInfinity #c #Jacobian pRadixed && isPointAtInfinity #c #Jacobian pointPrecomputed) then 
	lemma_point_at_infinity_after_point_double #c pRadixed
    else
      begin 
	curve_compatibility_with_translation_lemma_1 (fromDomainPoint #c #DH (toJacobianCoordinates #c (point_affine_as_nat c h1 pointToAdd))) pointPrecomputed pRadixed;
	curve_compatibility_with_translation_lemma_1  (pointAdd pRadixed (fromDomainPoint #c #DH (toJacobianCoordinates #c (point_affine_as_nat c h1 pointToAdd)))) (pointAdd pRadixed pointPrecomputed) (fromDomainPoint #c #DH (point_as_nat c h3 p))
      end


inline_for_extraction noextract
val radix_precomputed_upload_point: #c: curve -> #buf_type: buftype 
  -> p: point c
  -> scalar: lbuffer_t buf_type uint8 (getScalarLenBytes c) ->  
  Stack unit 
  (requires fun h -> live h p /\ live h scalar)
  (ensures fun h0 _ h1 -> modifies (loc p) h0 h1 /\ point_eval c h1 p /\ 
    pointEqual (fromDomainPoint #c #DH (point_as_nat c h1 p)) 
    (point_mult #c (Math.Lib.arithmetic_shift_right (scalar_as_nat (as_seq h0 scalar)) (v (getScalarLen c) - 4) % pow2 4) (basePoint #c)))

let radix_precomputed_upload_point #c p scalar =  
    let h0 = ST.get() in 
  let pXpY = sub p (size 0) (size 2 *! getCoordinateLenU64 c) in 
  getPointPrecomputedMixed scalar (size 0) pXpY; 
    let h1 = ST.get() in 
  let pZ = sub p (size 2 *! getCoordinateLenU64 c) (getCoordinateLenU64 c) in 
  Hacl.Impl.EC.LowLevel.uploadOneImpl pZ;
    let h2 = ST.get() in 
    
  let pX, pY = point_affine_as_nat c h1 pXpY in 
  if isPointAtInfinity #c #Affine (pX, pY) then 
    begin
      Hacl.Spec.MontgomeryMultiplication.lemma_pointAtInfInDomain #c 0 0 0;
      let f = (Math.Lib.arithmetic_shift_right (scalar_as_nat (as_seq h0 scalar)) (v (getScalarLen c) - 4) % pow2 4) in 
      curve_order_is_the_smallest #c (basePoint #c);
      point_mult_def #c f (basePoint #c);
      assert(False)
    end
  else 
    assert(pointEqual (fromDomainPoint #c #DH (point_as_nat c h2 p)) 
    (point_mult #c (Math.Lib.arithmetic_shift_right (scalar_as_nat (as_seq h0 scalar)) (v (getScalarLen c) - 4) % pow2 4) (basePoint #c)))


val lemma_scalar_less_than_order_: #c: curve 
  -> scalar: nat {scalar < getOrder #c} 
  -> i: nat {i > 0 /\ i < v ((size 2 *! getScalarLenBytes c))} -> 
  Lemma (scalar / pow2 4 <= (getOrder #c) / pow2 4)

let lemma_scalar_less_than_order_ #c scalar i = 
  let o = getOrder #c in 
  assert(scalar <= o - 1);
  Math.Lemmas.lemma_div_le scalar (o - 1) (pow2 4);
  assert(scalar / (pow2 4) <= (o - 1) / (pow2 4));
  assert(o - 1 < o);
  Math.Lemmas.lemma_div_le (o - 1) o (pow2 4);
  assert((o - 1) / pow2 4 <= o / pow2 4);
  assert(scalar / pow2 4 <= o / pow2 4)


val lemma_scalar_less_than_order: #c: curve 
  -> scalar: nat {scalar < getOrder #c} 
  -> i: nat {i > 0 /\ i < v ((size 2 *! getScalarLenBytes c))} -> 
  Lemma (scalar / pow2 ((v (getScalarLen c) - i * 4)) <= (getOrder #c) / pow2 4)

let lemma_scalar_less_than_order #c scalar i = 
  lemma_scalar_less_than_order_ #c scalar i;
  assert(v (getScalarLen c) - 4 * i >= 4);
  Math.Lemmas.pow2_le_compat (v (getScalarLen c) - 4 * i) 4;
  assert(pow2 (v (getScalarLen c) - 4 * i) >= pow2 4);
  assert(1 / (pow2 (v (getScalarLen c) - 4 * i)) <= 1 / pow2 4);
  Math.Lemmas.lemma_mult_le_left scalar (1 / (pow2 (v (getScalarLen c) - 4 * i))) (1 / pow2 4);
  assert(scalar * (1 / (pow2 (v (getScalarLen c) - 4 * i))) <= scalar / pow2 4)


inline_for_extraction noextract
val secret_to_public_radix: #c: curve -> #buf_type: buftype 
  -> p: point c  
  -> scalar: lbuffer_t buf_type uint8 (getScalarLenBytes c) 
  -> tempBuffer: lbuffer uint64 (size 17 *! getCoordinateLenU64 c)  -> 
  Stack unit
  (requires fun h -> live h p /\ live h scalar /\ live h tempBuffer /\ 
    point_eval c h p /\ LowStar.Monotonic.Buffer.all_disjoint [loc p; loc tempBuffer; loc scalar] /\ 
    scalar_as_nat (as_seq h scalar) < getOrder #c)
  (ensures fun h0 _ h1 -> modifies (loc p |+| loc tempBuffer) h0 h1 /\ point_eval c h1 p /\ (
    let p_n = fromDomainPoint #c #DH (point_as_nat c h1 p) in 
    pointEqual p_n (point_mult #c (scalar_as_nat (as_seq h0 scalar)) (basePoint #c))))


let secret_to_public_radix #c #a p scalar tempBuffer =  
  let h0 = ST.get() in 
  radix_precomputed_upload_point p scalar;
  let h1 = ST.get() in 
  let inv h (i: nat {i <= 2 * v (getScalarLenBytes c)}) = 
    live h p /\ live h tempBuffer /\ live h scalar /\ point_eval c h p /\
    modifies (loc p |+| loc tempBuffer) h0 h /\ (
    let p_n = fromDomainPoint #c #DH (point_as_nat c h p) in 
    let scalar = scalar_as_nat (as_seq h0 scalar) in
    let partialScalar = Math.Lib.arithmetic_shift_right scalar (v (getScalarLen c) - i * 4) in
    pointEqual p_n (point_mult #c partialScalar (basePoint #c))) in 

  scalar_as_nat_upperbound (as_seq h0 scalar) (v (getScalarLen c)); 
  Math.Lemmas.lemma_div_lt_nat (scalar_as_nat (as_seq h0 scalar)) (v (getScalarLen c)) (v (getScalarLen c) - 4); 
  Math.Lemmas.small_mod (scalar_as_nat (as_seq h0 scalar) / pow2 (v (getScalarLen c) - 4)) (pow2 4);

  for (size 1) (size 2 *! getScalarLenBytes c) inv 
    (fun i -> 
      let h0_ = ST.get() in
	lemma_scalar_less_than_order #c (scalar_as_nat (as_seq h0 scalar)) (v i);
      radix_step_precomputed p tempBuffer scalar i;
	Spec.ECC.Radix.pred0 #c #Affine (fromDomainPoint #c #DH (point_as_nat c h0_ p)) (as_seq h0_ scalar) (basePoint #c) (v i - 1))


let getPointTable (c: curve) (precomputedTable: lbuffer uint64 (getPointLenU64 c *! 16ul)) (i: nat {i < 16}) : GTot (point c) = 
  gsub precomputedTable (size i *! getPointLenU64 c) (getPointLenU64 c)

let tableInvariant (c: curve) (h: mem) (precomputedTable: lbuffer uint64 (getPointLenU64 c *! 16ul)) = 
  forall (i: nat {i < 16}). 
    let pi = getPointTable c precomputedTable i in
    let p1 = getPointTable c precomputedTable 1 in 
    point_eval c h pi /\ point_eval c h p1 /\ (
    let pi = fromDomainPoint #c #DH (point_as_nat c h pi) in 
    let p1 = fromDomainPoint #c #DH (point_as_nat c h p1) in 
    ~ (isPointAtInfinity #c p1) /\ pointEqual pi (point_mult #c i p1))


val getPointTableLemma: #c: curve 
  -> table: lbuffer uint64 (getPointLenU64 c *! 16ul) 
  -> i: size_t {v i < 16} -> 
  Lemma (getPointTable c table (v i) == gsub table (i *! getPointLenU64 c) (getPointLenU64 c))

let getPointTableLemma #c table i = 
  assert(getPointTable c table (v i) == gsub table (i *! getPointLenU64 c) (getPointLenU64 c))


val getPointPrecomputedTable_: #c: curve -> k: size_t {v k < 16}
  -> precomputedTable: lbuffer uint64 (getPointLenU64 c *! 16ul)
  -> bits: uint64
  -> r: point c ->
  Stack unit 
  (requires fun h -> live h precomputedTable /\ live h r /\ disjoint r precomputedTable /\
    point_eval c h r /\ (
    forall (i: nat {i < 16}). 
      let pi = getPointTable c precomputedTable i in
      let p1 = getPointTable c precomputedTable 1 in 
      point_eval c h pi /\ point_eval c h p1 /\ (
      let pi = fromDomainPoint #c #DH (point_as_nat c h pi) in 
      let p0 = fromDomainPoint #c #DH (point_as_nat c h p1) in 
      pointEqual pi (point_mult #c i p0))))
  (ensures fun h0 _ h1 -> modifies (loc r) h0 h1 /\ point_eval c h1 r /\ (
    let p1 = getPointTable c precomputedTable 1 in 
    let p1 = fromDomainPoint #c #DH (point_as_nat c h0 p1) in 
    let pi = fromDomainPoint #c #DH (point_as_nat c h1 r) in 
    if v bits = v k then 
      pointEqual pi (point_mult #c (v k) p1)
    else 
      point_as_nat c h1 r == point_as_nat c h0 r))

let getPointPrecomputedTable_ #c k precomputedTable bits r = 
  let h0 = ST.get() in
  let mask = eq_mask bits (to_u64 k) in 
    eq_mask_lemma bits (to_u64 k);

  let pointLen = k *! getPointLenU64 c in 
  let coordLen = getCoordinateLenU64 c in 
  let lut_cmb = sub precomputedTable pointLen (getPointLenU64 c)  in 

  let lut_cmb_x = sub lut_cmb (size 0) coordLen in 
  let lut_cmb_y = sub lut_cmb coordLen coordLen in
  let lut_cmb_z = sub lut_cmb (size 2 *! coordLen) coordLen in 

  let rX = sub r (size 0) coordLen in 
  let rY = sub r coordLen coordLen in 
  let rZ = sub r (size 2 *! coordLen) coordLen in 

  let h1 = ST.get() in 
  
  copy_conditional #c rX lut_cmb_x mask; 
  copy_conditional #c rY lut_cmb_y mask;
  copy_conditional #c rZ lut_cmb_z mask;

  let h2 = ST.get() in 

  getPointTableLemma precomputedTable k;

  let p1 = getPointTable c precomputedTable 1 in 
  let p1 = fromDomainPoint #c #DH (point_as_nat c h0 p1) in 

  assert(if v mask = 0 
    then 
      point_as_nat c h2 r == point_as_nat c h1 r
    else 
      pointEqual #c (fromDomainPoint #c #DH (point_as_nat c h2 r)) (fromDomainPoint #c #DH (point_as_nat c h1 lut_cmb)))


val getPointTableLemma_1: #c: curve -> table: lbuffer uint64 (getPointLenU64 c *! 16ul) -> Lemma
    (getPointTable c table 1 == gsub table (getPointLenU64 c) (getPointLenU64 c))

let getPointTableLemma_1 #c table = ()


val lemma_preserves_precomputed_table0: #c: curve 
  -> p: point c 
  -> modified: LowStar.Monotonic.Buffer.loc 
  -> h0: mem 
  -> h1: mem {live h0 p /\ modifies modified h0 h1 /\ LowStar.Buffer.loc_disjoint (loc p) modified /\ point_eval c h0 p} -> 
  Lemma (point_eval c h1 p /\ point_as_nat c h0 p == point_as_nat c h1 p /\ 
    fromDomainPoint #c #DH (point_as_nat c h0 p) == fromDomainPoint #c #DH (point_as_nat c h1 p))

let lemma_preserves_precomputed_table0 #c p r h0 h1 = 
  assert(as_nat c h0 (gsub p (size 0) (getCoordinateLenU64 c)) == as_nat c h1 (gsub p (size 0) (getCoordinateLenU64 c)));
  assert(as_nat c h0 (gsub p (getCoordinateLenU64 c) (getCoordinateLenU64 c)) == as_nat c h1 (gsub p (getCoordinateLenU64 c) (getCoordinateLenU64 c)));
  assert(as_nat c h0 (gsub p (2ul *! getCoordinateLenU64 c) (getCoordinateLenU64 c)) == as_nat c h1 (gsub p (2ul *! getCoordinateLenU64 c) (getCoordinateLenU64 c)))


val lemma_preserves_precomputed_table1: #c: curve 
  -> precomputedTable: lbuffer uint64 (getPointLenU64 c *! 16ul) 
  -> h0: mem 
  -> h1: mem 
  -> i: nat {i < 16} 
  -> modified: LowStar.Monotonic.Buffer.loc -> 
  Lemma
  (requires (live h0 precomputedTable /\ LowStar.Buffer.loc_disjoint modified (loc precomputedTable) /\ 
    modifies modified h0 h1 /\ (
    let pi = getPointTable c precomputedTable i in point_eval c h0 pi)))
  (ensures (
    let pi = getPointTable c precomputedTable i in 
    point_eval c h1 pi /\ point_as_nat c h0 pi == point_as_nat c h1 pi /\
    fromDomainPoint #c #DH (point_as_nat c h0 pi) == fromDomainPoint #c #DH (point_as_nat c h1 pi)))

let lemma_preserves_precomputed_table1 #c precomputedTable h0 h1 i modified = 
  let p = getPointTable c precomputedTable i in 
  getPointTableLemma #c precomputedTable (size i);
  assert (p == gsub precomputedTable (size i *! getPointLenU64 c) (getPointLenU64 c));
  assert (LowStar.Buffer.loc_disjoint modified (loc precomputedTable));
  assert (LowStar.Buffer.loc_disjoint modified (loc p));
  lemma_preserves_precomputed_table0 #c p modified h0 h1


val lemma_preserves_precomputed_table2: #c: curve 
  -> precomputedTable: lbuffer uint64 (getPointLenU64 c *! 16ul) 
  -> h0: mem 
  -> h1: mem 
  -> modified: LowStar.Monotonic.Buffer.loc 
  -> i: nat {i < 16} -> 
  Lemma
  (requires (live h0 precomputedTable /\ modifies modified h0 h1 /\ 
    LowStar.Buffer.loc_disjoint modified (loc precomputedTable) /\ (
    let pi = getPointTable c precomputedTable i in
    let p0 = getPointTable c precomputedTable 1 in 
    point_eval c h0 pi /\ point_eval c h0 p0 /\ 
    pointEqual (fromDomainPoint #c #DH (point_as_nat c h0 pi)) (point_mult #c i (fromDomainPoint #c #DH (point_as_nat c h0 p0))))))
  (ensures (
    let pi = getPointTable c precomputedTable i in 
    let p0 = getPointTable c precomputedTable 1 in 
    point_eval c h1 pi /\ point_eval c h1 p0 /\ 
    pointEqual (fromDomainPoint #c #DH (point_as_nat c h1 pi)) (point_mult #c i (fromDomainPoint #c #DH (point_as_nat c h1 p0)))))

let lemma_preserves_precomputed_table2 #c precomputedTable h0 h1 r i = 
  lemma_preserves_precomputed_table1 #c precomputedTable h0 h1 i r;
  lemma_preserves_precomputed_table1 #c precomputedTable h0 h1 1 r


val lemma_preserves_precomputed_table_: #c: curve 
  -> precomputedTable: lbuffer uint64 (getPointLenU64 c *! 16ul) 
  -> h0: mem 
  -> h1: mem 
  -> modified: LowStar.Monotonic.Buffer.loc -> 
  Lemma
  (requires (live h0 precomputedTable /\ LowStar.Buffer.loc_disjoint modified (loc precomputedTable) /\ 
    modifies modified h0 h1 /\ (
    forall (i: nat {i < 16}). ( 
      let pi = getPointTable c precomputedTable i in 
      let p1 = getPointTable c precomputedTable 1 in
      point_eval c h0 pi /\ point_eval c h0 p1 /\ (
      let pi = fromDomainPoint #c #DH (point_as_nat c h0 pi) in
      let p0 = fromDomainPoint #c #DH (point_as_nat c h0 p1) in 
      pointEqual pi (point_mult #c i p0))))))
  (ensures (
    forall (i: nat {i < 16}). 
      let pi = getPointTable c precomputedTable i in 
      let p1 = getPointTable c precomputedTable 1 in point_eval c h1 pi /\ point_eval c h1 p1 /\ (
      let pi = fromDomainPoint #c #DH (point_as_nat c h1 (getPointTable c precomputedTable i)) in 
      let p0 = fromDomainPoint #c #DH (point_as_nat c h1 (getPointTable c precomputedTable 1)) in 
      pointEqual pi (point_mult #c i p0))))

let lemma_preserves_precomputed_table_ #c precomputedTable h0 h1 r = 
  let a : Type = (a: nat {a < 16}) in 
  let p : (a -> GTot Type) = 
    fun i -> 
      let pi = getPointTable c precomputedTable i in 
      let p1 = getPointTable c precomputedTable 1 in 
      point_eval c h1 pi /\ point_eval c h1 p1 /\ 
      pointEqual (fromDomainPoint #c #DH (point_as_nat c h1 pi)) (point_mult #c i (fromDomainPoint #c #DH (point_as_nat c h1 p1))) in 
  let pred: (x : a -> Lemma (p x)) = lemma_preserves_precomputed_table2 #c precomputedTable h0 h1 r in 
  Classical.forall_intro #a #_ pred


val getPointPrecomputedTable_1: #c: curve 
  -> precomputedTable: lbuffer uint64 (getPointLenU64 c *! 16ul)
  -> bits: uint64 {v bits < 16}
  -> r: point c ->
  Stack unit 
  (requires fun h -> live h precomputedTable /\ live h r /\ disjoint r precomputedTable /\ point_eval c h r /\ (
    forall (i: nat {i < 16}). 
      let p1 = getPointTable c precomputedTable 1 in
      let pi = getPointTable c precomputedTable i in point_eval c h pi /\ point_eval c h p1 /\ (
      let pi = fromDomainPoint #c #DH (point_as_nat c h pi) in 
      let p1 = fromDomainPoint #c #DH (point_as_nat c h p1) in 
      pointEqual pi (point_mult #c i p1))))
  (ensures fun h0 _ h1 -> modifies (loc r) h0 h1 /\ point_eval c h1 r /\ (
    let p1 = getPointTable c precomputedTable 1 in 
    let p1 = fromDomainPoint #c #DH (point_as_nat c h0 p1) in 
    let rD = fromDomainPoint #c #DH (point_as_nat c h1 r) in 
    pointEqual rD (point_mult #c (v bits) p1)))

let getPointPrecomputedTable_1 #c precomputedTable bits r = 
  let h0 = ST.get() in 
  let inv (h: mem) (k: nat {0 <= k /\ k <= 16}) : Type0 = modifies (loc r) h0 h /\ point_eval c h r /\ 
    disjoint r precomputedTable /\ (
    let p0 = getPointTable c precomputedTable 1 in 
    (forall (i: nat {i < 16}). let pi = getPointTable c precomputedTable i in point_eval c h pi) /\
    (forall (i: nat {i < 16}). 
      let pi = fromDomainPoint #c #DH (point_as_nat c h (getPointTable c precomputedTable i)) in 
      let p0 = fromDomainPoint #c #DH (point_as_nat c h p0) in 
      pointEqual pi (point_mult #c i p0)) /\ (
    if v bits < k then 
      pointEqual (fromDomainPoint #c #DH (point_as_nat c h r)) (point_mult #c (v bits)
	(fromDomainPoint #c #DH (point_as_nat c h0 p0)))
    else
      point_as_nat c h r == point_as_nat c h0 r)) in 
  let f = fun (k: size_t {0 <= v k /\ v k < 16})  ->
    let h0_ = ST.get() in 
    getPointPrecomputedTable_ k precomputedTable bits r; 
    let h1 = ST.get() in
    lemma_preserves_precomputed_table_ #c precomputedTable h0 h1 (loc r);
    assert (modifies (loc r) h0 h0_);
    lemma_preserves_precomputed_table0 (getPointTable c precomputedTable 1) (loc r) h0 h0_ in 
  Lib.Loops.for (size 0) (size 16) inv f


val getPointPrecomputedTable: #c: curve -> #buf_type: buftype
  -> scalar: scalar_t #buf_type #c
  -> precomputedTable: lbuffer uint64 (getPointLenU64 c *! 16ul)
  -> i: size_t {v i < v (getScalarLenBytes c) * 2}
  -> r: point c ->
  Stack unit 
  (requires fun h -> live h precomputedTable /\ live h r /\ live h scalar /\ disjoint r precomputedTable /\ point_eval c h r /\ (
    forall (i: nat {i < 16}).
      let pi = getPointTable c precomputedTable i in 
      let p1 = getPointTable c precomputedTable 1 in point_eval c h pi /\ point_eval c h p1 /\ (
      let pi = fromDomainPoint #c #DH (point_as_nat c h pi) in 
      let p1 = fromDomainPoint #c #DH (point_as_nat c h p1) in 
      pointEqual pi (point_mult #c i p1))))
  (ensures fun h0 _ h1 -> modifies (loc r) h0 h1 /\ point_eval c h1 r /\ (
    let p1 = getPointTable c precomputedTable 1 in 
    let p1 = fromDomainPoint #c #DH (point_as_nat c h0 p1) in 
    let bits = Math.Lib.arithmetic_shift_right (scalar_as_nat #c (as_seq h0 scalar)) (v (getScalarLen c) - (v i + 1) * 4) % pow2 4 in 
    pointEqual (fromDomainPoint #c #DH (point_as_nat c h1 r)) (point_mult #c bits p1) /\
    pointEqual (fromDomainPoint #c #DH (point_as_nat c h1 r)) (Spec.ECC.Radix.getPrecomputedPoint #c #Jacobian p1 bits)))


let getPointPrecomputedTable #c #buf_type scalar precomputedTable i pointToAdd = 
    let h0 = ST.get() in 
  let bits = getScalar_4_byBit #c scalar i in 
    let h1 = ST.get() in 
    Hacl.Impl.P.PointAdd.Aux.lemma_coord_eval c h0 h1 pointToAdd; 
    lemma_preserves_precomputed_table_ #c precomputedTable h0 h1 (loc pointToAdd);
  getPointPrecomputedTable_1 precomputedTable bits pointToAdd;
    lemma_preserves_precomputed_table0 (getPointTable c precomputedTable 1) (loc pointToAdd) h0 h1

 
inline_for_extraction noextract
val montgomery_ladder_step_radix_0: #c: curve -> #buf_type: buftype
  -> p: point c 
  -> scalar: scalar_t #buf_type #c
  -> precomputedTable: lbuffer uint64 (getPointLenU64 c *! 16ul)
  -> i: size_t {v i < v (getScalarLenBytes c) * 2}
  -> tempBuffer: lbuffer uint64 (size 17 *! getCoordinateLenU64 c) 
  -> r: point c ->
  Stack unit 
  (requires fun h -> live h precomputedTable /\ live h r /\ live h tempBuffer /\  live h scalar /\ live h p /\
    disjoint r precomputedTable /\ disjoint p r /\ disjoint r tempBuffer /\
    point_eval c h r /\ disjoint p tempBuffer /\ point_eval c h p  /\ (
    forall (i: nat {i < 16}). 
      let p1 = getPointTable c precomputedTable 1 in 
      let pi = getPointTable c precomputedTable i in point_eval c h pi /\ point_eval c h p1 /\ (
      let pi = fromDomainPoint #c #DH (point_as_nat c h pi) in 
      let p1 = fromDomainPoint #c #DH (point_as_nat c h p1) in 
      pointEqual pi (point_mult #c i p1))))
  (ensures fun h0 _ h1 -> modifies (loc r |+| loc tempBuffer |+| loc p) h0 h1 /\ 
    point_eval c h1 p /\ point_eval c h1 r /\ (
    let p1 = fromDomainPoint #c #DH (point_as_nat c h0 (getPointTable c precomputedTable 1)) in 
    let bits = Math.Lib.arithmetic_shift_right (scalar_as_nat #c (as_seq h0 scalar)) (v (getScalarLen c) - (v i + 1) * 4) % pow2 4 in 
    pointEqual (fromDomainPoint #c #DH (point_as_nat c h1 r)) (Spec.ECC.Radix.getPrecomputedPoint #c #Jacobian p1 bits) /\   
    fromDomainPoint #c #DH (point_as_nat c h1 p) == Spec.ECC.Radix.getPointDoubleNTimes #c (fromDomainPoint #c #DH (point_as_nat c h0 p)) 4))

let montgomery_ladder_step_radix_0 #c #b p scalar precomputedTable i tempBuffer r = 
    let h0 = ST.get() in 
  getPointPrecomputedTable #c scalar precomputedTable i r;
    let h1 = ST.get() in 
    Hacl.Impl.P.PointAdd.Aux.lemma_coord_eval c h0 h1 p; 
  getPointDoubleNTimes #c p tempBuffer; 
    let h2 = ST.get() in 

  Hacl.Impl.P.PointAdd.Aux.lemma_coord_eval c h0 h1 p;
  Hacl.Impl.P.PointAdd.Aux.lemma_coord_eval c h1 h2 r


val montgomery_ladder_step_radix_1_lemma: #c: curve -> scalar: scalar_bytes #c
  -> p0: point_nat_prime #c {~ (isPointAtInfinity #c p0)} 
  -> p: point_nat_prime #c {exists (z: nat {z <= getOrder #c / 16}). pointEqual p (point_mult #c z p0)} 
  -> pi: point_nat_prime #c -> r: point_nat_prime #c 
  -> i: nat {i >= 1 /\ i < v (getScalarLenBytes c) * 2} -> 
  Lemma 
  (requires (  
    let scalar = scalar_as_nat scalar in 
    let si = Math.Lib.arithmetic_shift_right scalar (v (getScalarLen c) - (i + 1) * 4) % pow2 4 in 
    let pointRadixed =  Spec.ECC.Radix.getPointDoubleNTimes #c p 4 in 
    pointEqual pi (Spec.ECC.Radix.getPrecomputedPoint #c #Jacobian p0 si) /\ r == _point_add #c pi pointRadixed))
   (ensures (pointEqual #c r (Spec.ECC.Radix.radix_step #c #Jacobian scalar p0 (i - 1) p)))

let montgomery_ladder_step_radix_1_lemma #c k p0 p pi r i = 
  let scalar = scalar_as_nat k in 
  let l = v (getScalarLen c) in 
  let si = Math.Lib.arithmetic_shift_right scalar (l - ((i - 1) + 2) * 4) % pow2 4 in 
  let pointRadixed = Spec.ECC.Radix.getPointDoubleNTimes #c p 4 in 
  let pointPrecomputed = Spec.ECC.Radix.getPrecomputedPoint #c #Jacobian p0 si in 

  not_equal_precomputed2 #c p0 p si;
  curve_order_is_the_smallest #c p0;
  curve_compatibility_with_translation_lemma pi pointPrecomputed pointRadixed; 
  curve_commutativity_lemma pointPrecomputed pointRadixed


inline_for_extraction noextract
val montgomery_ladder_step_radix: #c: curve -> #buf_type: buftype
  -> p: point c 
  -> scalar: scalar_t #buf_type #c
  -> precomputedTable: lbuffer uint64 (getPointLenU64 c *! 16ul)
  -> i: size_t {v i >= 1 /\ v i < v (getScalarLenBytes c) * 2}
  -> tempBuffer: lbuffer uint64 (size 17 *! getCoordinateLenU64 c) 
  -> r: point c ->
  Stack unit 
  (requires fun h -> live h precomputedTable /\ live h r /\ live h tempBuffer /\  live h scalar /\ live h p /\
    disjoint r precomputedTable /\ disjoint p r /\ disjoint r tempBuffer /\
    point_eval c h r /\ disjoint p tempBuffer /\ point_eval c h p /\ tableInvariant c h precomputedTable /\ (
    let p1 = fromDomainPoint #c #DH (point_as_nat c h (getPointTable c precomputedTable 1)) in 
    let p  = fromDomainPoint #c #DH (point_as_nat c h p) in
    (exists (z: nat {z <= getOrder #c / 16}). pointEqual p (point_mult #c z p1))))
  (ensures fun h0 _ h1 -> modifies (loc r |+| loc tempBuffer |+| loc p) h0 h1 /\ 
    point_eval c h1 p /\ point_eval c h1 r /\ (
    let p1 = fromDomainPoint #c #DH (point_as_nat c h0 (getPointTable c precomputedTable 1)) in 
    let r =  fromDomainPoint #c #DH (point_as_nat c h1 p) in 
    let p = (fromDomainPoint #c #DH (point_as_nat c h0 p)) in 
    pointEqual #c r (Spec.ECC.Radix.radix_step #c #Jacobian (as_seq h0 scalar) p1 (v i - 1) p)))

let montgomery_ladder_step_radix #c #b p scalar table i tempBuffer r = 
  let h0 = ST.get() in 
  montgomery_ladder_step_radix_0 p scalar table i tempBuffer r;
  let h1 = ST.get() in 
  point_add r p p tempBuffer;
  let h2 = ST.get() in 
  Hacl.Impl.P.PointAdd.Aux.lemma_coord_eval c h1 h2 r;
  
  let p1 = fromDomainPoint #c #DH (point_as_nat c h0 (getPointTable c table 1)) in 
  let pi = fromDomainPoint #c #DH (point_as_nat c h1 r) in 
  let r =  fromDomainPoint #c #DH (point_as_nat c h2 p) in 
  let p =  fromDomainPoint #c #DH (point_as_nat c h0 p) in 

  montgomery_ladder_step_radix_1_lemma #c (as_seq h0 scalar) p1 p pi r (v i)


val lemma_pointAtInfInDomain1: #c: curve -> p: Spec.ECC.point #c -> Lemma 
  (isPointAtInfinity #c #Jacobian p == isPointAtInfinity #c #Jacobian (fromDomainPoint #c #DH p))

let lemma_pointAtInfInDomain1 #c p = 
  let (x, y, z) = p in 
  lemma_pointAtInfInDomain #c x y z


val lemma_modifies_not_first_element_of_precomputed_table: #c: curve 
  -> modified: LowStar.Monotonic.Buffer.loc 
  -> h0: mem 
  -> h1: mem 
  -> table: lbuffer uint64 (getPointLenU64 c *! 16ul) -> 
  Lemma 
  (requires (modifies modified h0 h1 /\ LowStar.Buffer.loc_disjoint modified (loc table) /\ live h0 table /\
    point_eval c h0 (getPointTable c table 1)))
  (ensures (
    let p1 = getPointTable c table 1 in 
    point_eval c h1 (getPointTable c table 1) /\
    point_as_nat c h0 p1 == point_as_nat c h1 p1))

let lemma_modifies_not_first_element_of_precomputed_table #c modified h0 h1 table = 
  let p1 = getPointTable c table 1 in 
  getPointTableLemma_1 table;
  
  assert(as_nat c h0 (gsub p1 (size 0) (getCoordinateLenU64 c)) == as_nat c h1 (gsub p1 (size 0) (getCoordinateLenU64 c)));
  assert(as_nat c h0 (gsub p1 (getCoordinateLenU64 c) (getCoordinateLenU64 c)) == as_nat c h1 (gsub p1 (getCoordinateLenU64 c) (getCoordinateLenU64 c)));
  assert(as_nat c h0 (gsub p1 (2ul *! getCoordinateLenU64 c) (getCoordinateLenU64 c)) == as_nat c h1 (gsub p1 (2ul *! getCoordinateLenU64 c) (getCoordinateLenU64 c)))


inline_for_extraction noextract
val generatePrecomputedTable_0: #c: curve 
  -> precomputedTable: lbuffer uint64 (getPointLenU64 c *! 16ul) 
  -> publicKey: point c -> 
  Stack unit
  (requires fun h -> live h precomputedTable /\ live h publicKey /\ point_eval c h publicKey /\ 
    disjoint publicKey precomputedTable /\ 
    ~ (isPointAtInfinity #c (fromDomainPoint #c #DH (point_as_nat c h publicKey))))
  (ensures fun h0 _ h1 -> modifies (loc precomputedTable) h0 h1 /\ (
    forall (i: nat {i < 2}). 
      let p1 = getPointTable c precomputedTable 1 in
      let pi = getPointTable c precomputedTable i in point_eval c h1 pi /\ point_eval c h1 p1 /\ (
      let pi = fromDomainPoint #c #DH (point_as_nat c h1 pi) in 
      let p1 = fromDomainPoint #c #DH (point_as_nat c h1 p1) in 
      let p  = fromDomainPoint #c #DH (point_as_nat c h0 publicKey) in
      pointEqual #c p p1 /\
      ~ (isPointAtInfinity #c p1) /\ (exists (z: nat {z <= getOrder #c / 16}). pointEqual p (point_mult #c z p1)) /\ 
	pointEqual pi (point_mult #c i p1))))

let generatePrecomputedTable_0 #c table publicKey = 
  let pointLen = getPointLenU64 c in 
  let point0 = sub table (size 0) pointLen in 
  let point1 = sub table pointLen pointLen in 

  let h0 = ST.get() in 
  Hacl.Impl.EC.LowLevel.uploadZeroPoint #c point0;
  let h1 = ST.get() in 
  Hacl.Impl.EC.LowLevel.copy_point #c publicKey point1;
  let h2 = ST.get() in 

  getPointTableLemma table (size 0);
  getPointTableLemma_1 table;

  assert (getPointTable c table 0 == gsub table (size 0 *! pointLen) pointLen);
  assert (getPointTable c table 1 == gsub table (size 1 *! pointLen) pointLen);

  let p1 = fromDomainPoint #c #DH (point_as_nat c h2 (getPointTable c table 1)) in 
  let p  = fromDomainPoint #c #DH (point_as_nat c h0 publicKey) in

  point_mult_0 #c p1 0; 
  lemma_pointAtInfInDomain1 #c (point_as_nat c h1 (getPointTable c table 0));
  point_mult_1 #c p1


val lemma_disjoint_and_eval_points_upload_table: #c: curve
  -> i: size_t {v i >= 1 /\ v i <= 7} 
  -> h: mem
  -> table: lbuffer uint64 (getPointLenU64 c *! 16ul) -> 
  Lemma
  (requires (live h table /\ (forall (j: nat {j < 2 * v i}). let pi = getPointTable c table j in point_eval c h pi)))
  (ensures (
    let point1 = getPointTable c table 1 in 
    let point_n = getPointTable c table (v i) in 
    let point_2n = getPointTable c table (2 * v i) in 
    let point_2n_1 = getPointTable c table (2 * v i + 1) in 
    disjoint point_n point_2n /\ point_eval c h point_n /\ point_eval c h point1))
    
let lemma_disjoint_and_eval_points_upload_table #c i h table = 
  let pointLen = getPointLenU64 c in 
  
  let point1 = gsub table pointLen pointLen in 
  let point_n = gsub table (i *! pointLen) pointLen in 
  let point_2n = gsub table (2ul *! i *! pointLen) pointLen in 
  let point_2n_1 = gsub table ((2ul *! i +! 1ul) *! pointLen) pointLen in 
    
  getPointTableLemma #c table i;
  getPointTableLemma_1 #c table;
  assert (disjoint point_n point_2n)


val lemma_disjoint_and_eval_points_upload_table1: #c: curve 
  -> i: size_t {v i >= 1 /\ v i <= 7} 
  -> h0: mem 
  -> h1: mem 
  -> table: lbuffer uint64 (getPointLenU64 c *! 16ul) 
  -> tempBuffer: lbuffer uint64 (size 17 *! getCoordinateLenU64 c) ->
  Lemma
  (requires (
    let point_2n = getPointTable c table (2 * v i) in 
    modifies (loc point_2n |+| loc tempBuffer) h0 h1 /\ disjoint table tempBuffer /\ live h0 table /\ (
    forall (j: nat {j < 2 * v i}). let pi = getPointTable c table j in point_eval c h0 pi)))
  (ensures (
    let point1 = getPointTable c table 1 in 
    let point_n = getPointTable c table (v i) in 
    let point_2n = getPointTable c table (2 * v i) in 
    let point_2n_1 = getPointTable c table (2 * v i + 1) in 
    eq_or_disjoint point1 point_2n_1 /\ disjoint point_2n point1 /\ disjoint point_2n point_2n_1 /\ 
    point_eval c h1 point1 /\ 
    point_as_nat c h0 point1 == point_as_nat c h1 point1))

let lemma_disjoint_and_eval_points_upload_table1 #c i h0 h1 table tempBuffer = 
  let pointLen = getPointLenU64 c in
  
  let point1 = gsub table pointLen pointLen in 
  let point_n = gsub table (i *! pointLen) pointLen in 
  let point_2n = gsub table (2ul *! i *! pointLen) pointLen in 
  let point_2n_1 = gsub table ((2ul *! i +! 1ul) *! pointLen) pointLen in 
  
  getPointTableLemma_1 table; 
  assert(as_seq h0 point1 == as_seq h1 point1);
  Hacl.Impl.P.PointAdd.Aux.lemma_coord_eval c h0 h1 point1


val lemma_not_modifies_all_points_before_index: #c: curve 
  -> i: size_t {v i >= 1 /\ v i <= 7} 
  -> h0: mem 
  -> h1: mem 
  -> table: lbuffer uint64 (getPointLenU64 c *! 16ul) 
  -> tempBuffer: LowStar.Monotonic.Buffer.loc ->
  Lemma 
  (requires (live h0 table /\ LowStar.Buffer.loc_disjoint (loc table) tempBuffer /\ ( 
    let point_2n = getPointTable c table (2 * v i) in 
    let point_2n_1 = getPointTable c table (2 * v i + 1) in 
    modifies (loc point_2n |+| loc point_2n_1 |+| tempBuffer) h0 h1)))
  (ensures (
    let pointLen = getPointLenU64 c in 
    let allPointsBefore = gsub table (size 0) (2ul *! i *! pointLen) in 
    as_seq h0 allPointsBefore == as_seq h1 allPointsBefore))

let lemma_not_modifies_all_points_before_index #c i h0 h1 table tempBuffer =
  let pointLen = getPointLenU64 c in 
  let allPointsBefore = gsub table (size 0) (2ul *! i *! pointLen) in 

  let point_2n = getPointTable c table (2 * v i) in 
  let point_2n_1 = getPointTable c table (2 * v i + 1) in 

  getPointTableLemma table (size (2 * v i)); 
  getPointTableLemma table (size (2 * v i + 1)); 

  assert(point_2n == gsub table (size (2 * v i) *! getPointLenU64 c) (getPointLenU64 c));
  assert(point_2n_1 == gsub table (size (2 * v i + 1) *! getPointLenU64 c) (getPointLenU64 c));

  assert(as_seq h0 allPointsBefore == as_seq h1 allPointsBefore)


val lemma_not_modifies_point_k: #c: curve 
  -> i: size_t {v i >= 1 /\ v i <= 7} 
  -> h0: mem 
  -> h1: mem 
  -> table: lbuffer uint64 (getPointLenU64 c *! 16ul) 
  -> k: nat {k < 2 * v i} ->
  Lemma 
  (requires (
    let pointLen = getPointLenU64 c in 
    let allPointsBefore = gsub table (size 0) (2ul *! i *! pointLen) in 
    as_seq h0 allPointsBefore == as_seq h1 allPointsBefore /\ 
    point_eval c h0 (getPointTable c table k)))
  (ensures (
    let pk = getPointTable c table k in 
    point_eval c h1 pk /\ point_as_nat c h1 pk == point_as_nat c h0 pk))

let lemma_not_modifies_point_k #c i h0 h1 table k = 
  let pointLen = getPointLenU64 c in 
  let allPointsBefore = gsub table (size 0) (2ul *! i *! pointLen) in 
  let pk = getPointTable c table k in 
  
  assert(gsub table (size k *! getPointLenU64 c) (getPointLenU64 c) == gsub allPointsBefore (size k *! getPointLenU64 c) (getPointLenU64 c));
  assert (getZ pk == gsub pk (size 2 *! (getCoordinateLenU64 c)) (getCoordinateLenU64 c))


val lemma_getZ: #c: curve -> p: point c -> 
  Lemma (getZ p == gsub p (size 2 *! (getCoordinateLenU64 c)) (getCoordinateLenU64 c))

let lemma_getZ #c p = ()


val lemma_point_eval_if_point_did_not_change_: #c: curve -> i: size_t {v i >= 1 /\ v i <= 7} -> h0: mem -> h1: mem 
  -> table: lbuffer uint64 (getPointLenU64 c *! 16ul) -> j: nat {j < 2 * v i} ->
  Lemma (requires (live h0 table /\ (
    let pointLen = getPointLenU64 c in 
    let allPointsBefore = gsub table (size 0) (2ul *! i *! pointLen) in 
    as_seq h0 allPointsBefore == as_seq h1 allPointsBefore /\ (
    let pi = getPointTable c table j in 
    let p1 = getPointTable c table 1 in 
    point_eval c h0 pi /\ point_eval c h0 p1 /\ (
    let pi = fromDomainPoint #c #DH (point_as_nat c h0 pi) in 
    let p1 = fromDomainPoint #c #DH (point_as_nat c h0 p1) in 
    pointEqual pi (point_mult #c j p1))))))
  (ensures (
    let pi = getPointTable c table j in
    let p1 = getPointTable c table 1 in 
    point_eval c h1 pi /\ point_eval c h1 p1 /\ (
    let pi = fromDomainPoint #c #DH (point_as_nat c h1 pi) in 
    let p1 = fromDomainPoint #c #DH (point_as_nat c h1 p1) in 
    pointEqual pi (point_mult #c j p1))))

let lemma_point_eval_if_point_did_not_change_ #c i h0 h1 table j = 
    let pointLen = getPointLenU64 c in 
  lemma_not_modifies_point_k i h0 h1 table j;
  lemma_not_modifies_point_k i h0 h1 table 1;
  
  let allPointsBefore = gsub table (size 0) (2ul *! i *! pointLen) in 
  
  getPointTableLemma_1 table;
  lemma_getZ #c (getPointTable c table 1); 

  getPointTableLemma table (size j);
  lemma_getZ #c (getPointTable c table j)


val lemma_point_eval_if_point_did_not_change: #c: curve 
  -> i: size_t {v i >= 1 /\ v i <= 7} 
  -> h0: mem 
  -> h1: mem 
  -> table: lbuffer uint64 (getPointLenU64 c *! 16ul) ->
  Lemma (requires (live h0 table /\ (
    let pointLen = getPointLenU64 c in 
    let allPointsBefore = gsub table (size 0) (2ul *! i *! pointLen) in 
    as_seq h0 allPointsBefore == as_seq h1 allPointsBefore /\ (
    forall (j: nat {j < 2 * v i}). let pi = getPointTable c table j in point_eval c h0 pi) /\ (
    forall (j: nat {j < 2 * v i}).
      let pi = fromDomainPoint #c #DH (point_as_nat c h0 (getPointTable c table j)) in 
      let p1 = fromDomainPoint #c #DH (point_as_nat c h0 (getPointTable c table 1)) in 
      pointEqual pi (point_mult #c j p1)))))
  (ensures (
      forall (j: nat {j < 2 * v i}). let pi = getPointTable c table j in point_eval c h1 pi) /\ (
      forall (j: nat {j < 2 * v i}). 
      let pi = fromDomainPoint #c #DH (point_as_nat c h1 (getPointTable c table j)) in 
      let p1 = fromDomainPoint #c #DH (point_as_nat c h1 (getPointTable c table 1)) in 
      pointEqual pi (point_mult #c j p1)))

let lemma_point_eval_if_point_did_not_change #c i h0 h1 table = 
  let a: Type = a: nat {a < 2 * v i} in 
  let p : (a -> GTot Type) = 
    fun i -> 
      let pi = getPointTable c table i in
      point_eval c h1 (getPointTable c table i) /\ 
      point_eval c h1 (getPointTable c table 1) /\ (
      let pi = fromDomainPoint #c #DH (point_as_nat c h1 (getPointTable c table i)) in 
      let p1 = fromDomainPoint #c #DH (point_as_nat c h1 (getPointTable c table 1)) in 
      pointEqual pi (point_mult #c i p1)) in 
  let pred : (x : a -> Lemma (p x)) = lemma_point_eval_if_point_did_not_change_ #c i h0 h1 table in 
  Classical.forall_intro #a #p pred


val lemma_preserves_precomputed_table: #c: curve -> i: size_t {v i >= 1 /\ v i <= 7} -> h0: mem -> h1: mem 
  -> table: lbuffer uint64 (getPointLenU64 c *! 16ul) 
  -> tempBuffer: lbuffer uint64 (size 17 *! getCoordinateLenU64 c) ->
  Lemma
  (requires (live h0 table /\ live h0 tempBuffer /\ disjoint table tempBuffer /\ (
    let point_2n = getPointTable c table (2 * v i) in 
    let point_2n_1 = getPointTable c table (2 * v i + 1) in 
    modifies (loc point_2n |+| loc point_2n_1 |+| loc tempBuffer) h0 h1 /\ 
    point_eval c h1 point_2n /\ point_eval c h1 point_2n_1 /\ (
    forall (j: nat {j < 2 * v i}). 
      let p1 = getPointTable c table 1 in 
      let pi = getPointTable c table j in point_eval c h0 pi /\ point_eval c h0 p1 /\ (
      let p1 = fromDomainPoint #c #DH (point_as_nat c h0 p1) in  
      let pi = fromDomainPoint #c #DH (point_as_nat c h0 pi) in 
      ~ (isPointAtInfinity #c p1) /\ 
      pointEqual pi (point_mult #c j p1) /\
      pointEqual (fromDomainPoint #c #DH (point_as_nat c h1 point_2n)) (point_mult #c (2 * v i) p1) /\ 
      pointEqual (fromDomainPoint #c #DH (point_as_nat c h1 point_2n_1)) (point_mult #c (2 * v i + 1) p1))))))
  (ensures (
    forall (j: nat {j <= 2 * v i + 1}). 
      let p1 = getPointTable c table 1 in 
      let pi = getPointTable c table j in point_eval c h1 pi /\ point_eval c h1 p1 /\ 
      point_as_nat c h0 p1 == point_as_nat c h1 p1 /\ (
      let p1 = fromDomainPoint #c #DH (point_as_nat c h1 p1) in 
      let pi = fromDomainPoint #c #DH (point_as_nat c h1 pi) in 
      ~ (isPointAtInfinity #c p1) /\ (pointEqual pi (point_mult #c j p1)))))

let lemma_preserves_precomputed_table #c i h0 h1 table tempBuffer = 
  lemma_not_modifies_all_points_before_index i h0 h1 table (loc tempBuffer);
  lemma_point_eval_if_point_did_not_change #c i h0 h1 table;
  lemma_not_modifies_point_k i h0 h1 table 1


val getPointTable_buffer: #c: curve -> precomputedTable: lbuffer uint64 (getPointLenU64 c *! 16ul) 
  -> i: size_t {v i < 16} 
  -> tempBuffer: lbuffer uint64 (size 17 *! getCoordinateLenU64 c) ->
  Stack (point c)
  (requires (fun h -> live h precomputedTable /\ disjoint precomputedTable tempBuffer))
  (ensures fun h0 r h1 -> h0 == h1 /\ live h1 r /\ r == getPointTable c precomputedTable (v i) /\ 
    disjoint r tempBuffer /\ modifies0 h0 h1 /\ (
    let pointLen = getPointLenU64 c in 
    r == gsub precomputedTable (i *! pointLen) pointLen))

let getPointTable_buffer #c table i tempBuffer = 
  let pointLen = getPointLenU64 c in 
  sub table (i *! pointLen) pointLen


val generatePrecomputedTable_step_lemma_disjoint: #c: curve -> p: point c 
  -> tempBuffer: lbuffer uint64 (size 17 *! getCoordinateLenU64 c) 
  -> table: lbuffer uint64 (getPointLenU64 c *! 16ul) 
  -> a: size_t {v a < 16} -> h0: mem -> h1: mem ->
  Lemma 
  (requires (p == getPointTable c table (v a) /\ modifies (loc p |+| loc tempBuffer) h0 h1))
  (ensures (modifies (loc table |+| loc tempBuffer) h0 h1))

let generatePrecomputedTable_step_lemma_disjoint #c p temp table a h0 h1 = 
  let pointLen = getPointLenU64 c in 
  getPointTableLemma table a;
  assert(getPointTable c table (v a) == gsub table (pointLen *! a) pointLen)
  

val lemma_two_points_different_coeff_not_equal: #c: curve 
  -> p0: Spec.ECC.point #c #Jacobian {~ (isPointAtInfinity p0)}
  -> pk: nat
  -> p: Spec.ECC.point #c #Jacobian {pointEqual p (point_mult #c  pk p0)} 
  -> qk: nat
  -> q: Spec.ECC.point #c #Jacobian {pointEqual q (point_mult #c  qk p0)} -> 
  Lemma 
  (requires (pk <> qk /\ pk < getOrder #c /\ qk < getOrder #c))
  (ensures (~ (pointEqual p q)))

let lemma_two_points_different_coeff_not_equal #c p0 pk p qk q =
  if pointEqual p q then 
    begin
      let inverseP = point_mult #c (- pk) p0 in 
      lemmaApplPointAdd #c p0 pk p (- pk) inverseP;
      
      point_mult_0 #c p0 0;
      assert(pointEqual (pointAdd p inverseP) (point_mult #c 0 p0));
      assert(isPointAtInfinity (pointAdd p inverseP));

      lemmaApplPointAdd #c p0 qk q (- pk) inverseP;
      assert(pointEqual (pointAdd q inverseP) (point_mult #c (qk - pk) p0));
      assert(qk - pk <> 0);

      lemma_scalar_reduce p0 (qk - pk); 

      assert(point_mult #c (qk - pk) p0 == point_mult #c ((qk - pk) % getOrder #c) p0);
      curve_order_is_the_smallest #c p0;
      assert(~ (isPointAtInfinity (pointAdd q inverseP)));
        
      curve_compatibility_with_translation_lemma #c p q (inverseP);
      assert(False)
    end


val generatePrecomputedResultOfPointAddAndDouble: #c: curve 
  -> table: lbuffer uint64 (getPointLenU64 c *! 16ul) 
  -> i: nat {2 * i < 16}
  -> h0: mem -> h1: mem -> h2: mem ->
  Lemma
  (requires (
    let p_1 = getPointTable c table 1 in 
    let p_n = getPointTable c table i in 
    let p_2n = getPointTable c table (2 * i) in 
    let p_2n_1 =  getPointTable c table (2 * i + 1) in 
    point_eval c h1 p_1 /\ point_eval c h0 p_n /\ point_eval c h2 p_2n /\ point_eval c h2 p_2n_1 /\ (
    let p1 = fromDomainPoint #c #DH (point_as_nat c h1 p_1) in 
    pointEqual (fromDomainPoint #c #DH (point_as_nat c h0 p_n)) (point_mult #c i p1) /\ ~ (isPointAtInfinity #c p1) /\
    fromDomainPoint #c #DH (point_as_nat c h2 p_2n) == _point_double #c (fromDomainPoint #c #DH (point_as_nat c h0 p_n)) /\
    fromDomainPoint #c #DH (point_as_nat c h2 p_2n_1) == _point_add #c (fromDomainPoint #c #DH (point_as_nat c h2 p_2n)) (fromDomainPoint #c #DH (point_as_nat c h1 p_1)))))
  (ensures (
    let point_2n = getPointTable c table (2 * i) in 
    let point_2n_1 = getPointTable c table (2 * i + 1) in 
    let p1 = getPointTable c table 1 in 
    let p1 = fromDomainPoint #c #DH (point_as_nat c h1 p1) in 
    pointEqual (fromDomainPoint #c #DH (point_as_nat c h2 point_2n)) (point_mult #c (2 * i) p1) /\ 
    pointEqual (fromDomainPoint #c #DH (point_as_nat c h2 point_2n_1)) (point_mult #c (2 * i + 1) p1)))

let generatePrecomputedResultOfPointAddAndDouble #c table i h0 h1 h2 = 
  let p_n = fromDomainPoint #c #DH (point_as_nat c h0 (getPointTable c table i)) in 
  let p_2n = fromDomainPoint #c #DH (point_as_nat c h2 (getPointTable c table (2 * i))) in 
  let p_2n_1 =  getPointTable c table (2 * i + 1) in 
  let p1 = fromDomainPoint #c #DH (point_as_nat c h1 (getPointTable c table 1)) in 

  lemmaApplPointAdd #c p1 i p_n i p_n; 

  point_mult_1 #c p1;
  lemma_two_points_different_coeff_not_equal #c p1 (2 * i) p_2n 1 p1; 
  lemmaApplPointAdd #c p1 (2 * i) p_2n 1 p1


val generatePrecomputedTable_step: #c: curve -> precomputedTable: lbuffer uint64 (getPointLenU64 c *! 16ul) 
  -> i: size_t {v i >= 1 /\ v i <= 7}
  -> tempBuffer: lbuffer uint64 (size 17 *! getCoordinateLenU64 c) ->
  Stack unit  
  (requires fun h -> live h precomputedTable /\ live h tempBuffer /\ disjoint precomputedTable tempBuffer /\ (
    forall (j: nat {j < 2 * v i}). let pi = getPointTable c precomputedTable j in point_eval c h pi) /\ (
    forall (j: nat {j < 2 * v i}). 
      let pi = fromDomainPoint #c #DH (point_as_nat c h (getPointTable c precomputedTable j)) in 
      let p1 = fromDomainPoint #c #DH (point_as_nat c h (getPointTable c precomputedTable 1)) in 
      ~ (isPointAtInfinity #c p1) /\ pointEqual pi (point_mult #c j p1)))
  (ensures fun h0 _ h1 -> modifies (loc precomputedTable |+| loc tempBuffer) h0 h1 /\ (
    forall (j: nat {j <= 2 * v i + 1}). 
      let p1 = getPointTable c precomputedTable 1 in
      let pi = getPointTable c precomputedTable j in point_eval c h1 pi /\ point_eval c h1 p1 /\
	point_as_nat c h0 p1 == point_as_nat c h1 p1 /\ (
      let pi = fromDomainPoint #c #DH (point_as_nat c h1 pi) in 
      let p1 = fromDomainPoint #c #DH (point_as_nat c h1 p1) in 
      ~ (isPointAtInfinity #c p1) /\ pointEqual pi (point_mult #c j p1))))

let generatePrecomputedTable_step #c table i tempBuffer =
  let pointLen = getPointLenU64 c in 

  let h0 = ST.get() in
  
  let point1 = getPointTable_buffer #c table (size 1) tempBuffer in 
  let point_n = getPointTable_buffer #c table i tempBuffer in 
  let point_2n = getPointTable_buffer #c table (size 2 *! i) tempBuffer in 
  let point_2n_1 =  getPointTable_buffer #c table (size 2 *! i +! size 1) tempBuffer in 

  lemma_disjoint_and_eval_points_upload_table #c i h0 table;
  point_double #c point_n point_2n tempBuffer;
  
  let h1 = ST.get() in 
  lemma_disjoint_and_eval_points_upload_table1 i h0 h1 table tempBuffer;
  point_add point_2n point1 point_2n_1 tempBuffer;
  let h2 = ST.get() in 

  Hacl.Impl.P.PointAdd.Aux.lemma_coord_eval c h1 h2 point_2n;

  generatePrecomputedTable_step_lemma_disjoint point_2n tempBuffer table (size 2 *! i) h0 h1;
  generatePrecomputedTable_step_lemma_disjoint point_2n_1 tempBuffer table (size 2 *! i +! size 1) h1 h2;

  generatePrecomputedResultOfPointAddAndDouble #c table (v i) h0 h1 h2;
  lemma_preserves_precomputed_table i h0 h2 table tempBuffer


val generatePrecomputedTable_loop: #c: curve -> precomputedTable: lbuffer uint64 (getPointLenU64 c *! 16ul) 
  -> tempBuffer: lbuffer uint64 (size 17 *! getCoordinateLenU64 c) ->
  Stack unit  
  (requires fun h -> (live h precomputedTable /\ live h tempBuffer /\ disjoint precomputedTable tempBuffer /\ (
    forall (i: nat {i < 2}). let pi = getPointTable c precomputedTable i in point_eval c h pi) /\ (
    forall (i: nat {i < 2}). 
      let pi = fromDomainPoint #c #DH (point_as_nat c h (getPointTable c precomputedTable i)) in 
      let p1 = fromDomainPoint #c #DH (point_as_nat c h (getPointTable c precomputedTable 1)) in 
      ~ (isPointAtInfinity #c p1) /\ pointEqual pi (point_mult #c i p1))))
  (ensures fun h0 _ h1 -> modifies (loc precomputedTable |+| loc tempBuffer) h0 h1 /\ tableInvariant c h1 precomputedTable /\ (
    let p1 = getPointTable c precomputedTable 1 in
    point_as_nat c h0 p1 == point_as_nat c h1 p1))

let generatePrecomputedTable_loop #c table tempBuffer = 
  let h0 = ST.get() in 
  [@inline_let]
  let inv (h : mem) (i: nat {i <= 8}) = modifies (loc table |+| loc tempBuffer) h0 h /\ 
    point_eval c h0 (getPointTable c table 1) /\ (
    forall (j: nat {j < 2 * i}). let pi = getPointTable c table j in point_eval c h pi)  /\ (
    forall (j: nat {j < 2 * i}). 
      let pi = fromDomainPoint #c #DH (point_as_nat c h (getPointTable c table j)) in 
      let p1 = fromDomainPoint #c #DH (point_as_nat c h (getPointTable c table 1)) in 
      ~ (isPointAtInfinity #c p1) /\ pointEqual pi (point_mult #c j p1) /\
	point_as_nat c h0 (getPointTable c table 1) == point_as_nat c h (getPointTable c table 1)) in
  for 1ul 8ul inv (fun i -> generatePrecomputedTable_step #c table i tempBuffer)


[@ CInline]
val generatePrecomputedTable: #c: curve 
  -> precomputedTable: lbuffer uint64 (getPointLenU64 c *! 16ul) 
  -> publicKey: point c 
  -> tempBuffer: lbuffer uint64 (size 17 *! getCoordinateLenU64 c) -> Stack unit  
  (requires fun h -> 
    live h precomputedTable /\ live h publicKey /\ live h tempBuffer /\ 
    point_eval c h publicKey /\ 
    disjoint publicKey precomputedTable /\ disjoint precomputedTable tempBuffer /\
    ~ (isPointAtInfinity #c (fromDomainPoint #c #DH (point_as_nat c h publicKey))))
  (ensures fun h0 _ h1 ->
    modifies (loc precomputedTable |+| loc tempBuffer) h0 h1 /\ tableInvariant c h1 precomputedTable /\ (
    let p1 = getPointTable c precomputedTable 1 in
    let p1 = fromDomainPoint #c #DH (point_as_nat c h1 p1) in 
    let p  = fromDomainPoint #c #DH (point_as_nat c h0 publicKey) in
    pointEqual #c p p1))

let generatePrecomputedTable #c table publicKey tempBuffer = 
  generatePrecomputedTable_0 table publicKey;
  generatePrecomputedTable_loop #c table tempBuffer


val lemma_modifies_not_tb_invariant_holds: #c: curve 
  -> modified: LowStar.Monotonic.Buffer.loc
  -> h0: mem 
  -> h1: mem 
  -> table: lbuffer uint64 (getPointLenU64 c *! 16ul) -> 
  Lemma 
  (requires (tableInvariant c h0 table /\ modifies modified h0 h1 /\ 
    LowStar.Buffer.loc_disjoint modified (loc table) /\ live h0 table))
  (ensures (tableInvariant c h1 table))

let lemma_modifies_not_tb_invariant_holds #c modified h0 h1 table = 
  lemma_preserves_precomputed_table_ #c table h0 h1 modified;
  lemma_modifies_not_first_element_of_precomputed_table modified h0 h1 table


inline_for_extraction noextract
val scalar_mult_radix__: #c: curve -> #buf_type: buftype 
  -> p: point c
  -> scalar: scalar_t #buf_type #c 
  -> tempBuffer: lbuffer uint64 (size 17 *! getCoordinateLenU64 c) 
  -> r: point c 
  -> precomputedTable: lbuffer uint64 (getPointLenU64 c *! 16ul) ->
  Stack unit
  (requires fun h -> 
    live h precomputedTable /\ live h r /\ live h tempBuffer /\ live h scalar /\ live h p /\
    LowStar.Monotonic.Buffer.all_disjoint [loc p; loc scalar; loc tempBuffer; loc r; loc precomputedTable] /\ 
    scalar_as_nat (as_seq h scalar) < getOrder #c /\
    point_eval c h p /\ point_eval c h r /\ tableInvariant c h precomputedTable /\ (
    let p1 = fromDomainPoint #c #DH (point_as_nat c h (getPointTable c precomputedTable 1)) in 
    let p  = fromDomainPoint #c #DH (point_as_nat c h p) in 
    let scalar = scalar_as_nat (as_seq h scalar) in
    let partialScalar = Math.Lib.arithmetic_shift_right scalar (v (getScalarLen c) - 1 * 4)  in
    pointEqual p (point_mult #c partialScalar p1)))
  (ensures fun h0 _ h1 -> modifies (loc r |+| loc p |+| loc tempBuffer) h0 h1 /\ point_eval c h1 p /\ (
    let p1 = getPointTable c precomputedTable 1 in 
    let p1 = fromDomainPoint #c #DH (point_as_nat c h0 p1) in 
    let p_n = fromDomainPoint #c #DH (point_as_nat c h1 p) in 
    pointEqual p_n (point_mult #c (scalar_as_nat (as_seq h0 scalar)) p1)))

let scalar_mult_radix__ #c p scalar tempBuffer r precomputedTable =  
  let h0 = ST.get() in 
  let inv h (i: nat {i <= 2 * v (getScalarLenBytes c)}) =
    live h precomputedTable /\ live h r /\ live h tempBuffer /\ live h scalar /\ live h p /\
    point_eval c h r /\ point_eval c h p /\
    modifies (loc r |+| loc p |+| loc tempBuffer) h0 h /\
    tableInvariant c h precomputedTable /\ (
    let p1 = getPointTable c precomputedTable 1 in 
    let p1 = fromDomainPoint #c #DH (point_as_nat c h p1) in 
    let p  = fromDomainPoint #c #DH (point_as_nat c h p) in 
      
    let scalar = scalar_as_nat (as_seq h0 scalar) in
    let partialScalar = Math.Lib.arithmetic_shift_right scalar (v (getScalarLen c) - i * 4) in
    pointEqual p (point_mult #c partialScalar p1)) in 

  for 1ul (size 2 *! getScalarLenBytes c) inv 
  (fun j -> 
    let h0_ = ST.get() in
    
    lemma_scalar_less_than_order #c (scalar_as_nat (as_seq h0 scalar)) (v j);
    montgomery_ladder_step_radix #c p scalar precomputedTable j tempBuffer r;
    let h1_ = ST.get() in 
   
    assert(LowStar.Buffer.loc_disjoint (loc r |+| loc p |+| loc tempBuffer) (loc precomputedTable));
    lemma_modifies_not_tb_invariant_holds #c (loc r |+| loc p |+| loc tempBuffer) h0_ h1_ precomputedTable;

    let p1_ = getPointTable c precomputedTable 1 in 
    lemma_modifies_not_first_element_of_precomputed_table (loc r |+| loc p |+| loc tempBuffer) h0_ h1_ precomputedTable;
    
    let x = fromDomainPoint #c #DH (point_as_nat c h0_ p) in 
    let p1 = fromDomainPoint #c #DH (point_as_nat c h0_ p1_) in 
    let s = as_seq h0_ scalar in 
    Spec.ECC.Radix.pred0 #c #Jacobian x s p1 (v j - 1));

  let h1 = ST.get() in 

  lemma_modifies_not_first_element_of_precomputed_table (loc r |+| loc p |+| loc tempBuffer) h0 h1 precomputedTable


inline_for_extraction noextract
val scalar_mult_radix_: #c: curve -> #buf_type: buftype 
  -> p: point c
  -> scalar: scalar_t #buf_type #c 
  -> tempBuffer: lbuffer uint64 (size 17 *! getCoordinateLenU64 c) 
  -> r: point c 
  -> precomputedTable: lbuffer uint64 (getPointLenU64 c *! 16ul) ->
  Stack unit
  (requires fun h -> 
    live h precomputedTable /\ live h r /\ live h tempBuffer /\ live h scalar /\ live h p /\
    LowStar.Monotonic.Buffer.all_disjoint [loc p; loc scalar; loc tempBuffer; loc r; loc precomputedTable] /\ 
    scalar_as_nat (as_seq h scalar) < getOrder #c /\
    point_eval c h p /\ point_eval c h r /\ tableInvariant c h precomputedTable)
  (ensures fun h0 _ h1 -> modifies (loc r |+| loc p |+| loc tempBuffer) h0 h1 /\ point_eval c h1 p /\ (
    let p1 = getPointTable c precomputedTable 1 in 
    let p1 = fromDomainPoint #c #DH (point_as_nat c h0 p1) in 
    let p_n = fromDomainPoint #c #DH (point_as_nat c h1 p) in 
    pointEqual p_n (point_mult #c (scalar_as_nat (as_seq h0 scalar)) p1)))

let scalar_mult_radix_ #c p scalar tempBuffer r precomputedTable = 
  let h0 = ST.get() in 
  getPointPrecomputedTable #c scalar precomputedTable (size 0) p;

  let h1 = ST.get() in 
  lemma_modifies_not_tb_invariant_holds #c (loc p) h0 h1 precomputedTable;
  Hacl.Impl.P.PointAdd.Aux.lemma_coord_eval c h0 h1 r;

  scalar_as_nat_upperbound (as_seq h0 scalar) (v (getScalarLen c)); 
  Math.Lemmas.lemma_div_lt_nat (scalar_as_nat (as_seq h0 scalar)) (v (getScalarLen c)) (v (getScalarLen c) - 4); 
  Math.Lemmas.small_mod (scalar_as_nat (as_seq h0 scalar) / pow2 (v (getScalarLen c) - 4)) (pow2 4);

  lemma_modifies_not_first_element_of_precomputed_table (loc p) h0 h1 precomputedTable;
  scalar_mult_radix__ p scalar tempBuffer r precomputedTable


(* the same as in DH *)
val lemma_zero_point_zero_coordinates: c: curve -> h: mem -> p: point c -> 
  Lemma (requires lseq_as_nat (as_seq h p) == 0)
  (ensures (as_nat c h (getX p) == 0) /\ (as_nat c h (getY p) == 0) /\ (as_nat c h (getZ p) == 0) /\ point_eval c h p)

let lemma_zero_point_zero_coordinates c h p = 
  let yz = gsub p (getCoordinateLenU64 c) (size 2 *! getCoordinateLenU64 c) in 
  lemma_test (as_seq h p) (v (getCoordinateLenU64 c));
  lemma_test (as_seq h yz) (v (getCoordinateLenU64 c));
  Hacl.Impl.P.PointAdd.Aux.lemma_point_eval_if_zero c p h


inline_for_extraction noextract
val scalar_mult_radix: #c: curve -> #t:buftype
  -> publicKey: point c 
  -> scalar: scalar_t #t #c 
  -> tempBuffer: lbuffer uint64 (size 20 *! getCoordinateLenU64 c) ->
  Stack unit 
  (requires fun h -> live h publicKey /\ live h scalar /\ live h tempBuffer /\
    LowStar.Monotonic.Buffer.all_disjoint [loc publicKey; loc tempBuffer; loc scalar] /\ 
    point_eval c h publicKey /\
    scalar_as_nat (as_seq h scalar) < getOrder #c /\
    ~ (isPointAtInfinity #c (fromDomainPoint #c #DH (point_as_nat c h publicKey))))
  (ensures fun h0 _ h1 -> modifies (loc publicKey |+| loc tempBuffer) h0 h1 /\ 
    point_eval c h1 publicKey /\ (
    let result = fromDomainPoint #c #DH (point_as_nat c h1 publicKey) in 
    let p  = fromDomainPoint #c #DH (point_as_nat c h0 publicKey) in
    pointEqual result (point_mult #c (scalar_as_nat (as_seq h0 scalar)) p)))

let scalar_mult_radix #c publicKey scalar tempBuffer = 
  let h0 = ST.get() in 
  push_frame(); 
    let precomputedTable = create (size 16 *! getPointLenU64 c) (u64 0) in 
    let tempPoint = create (getPointLenU64 c) (u64 0) in 
    let tempBuffer = sub tempBuffer (size 0) (size 17 *! getCoordinateLenU64 c) in 
  let h1 = ST.get() in 
  Hacl.Impl.P.PointAdd.Aux.lemma_coord_eval c h0 h1 publicKey;
  generatePrecomputedTable precomputedTable publicKey tempBuffer;

  let h2 = ST.get() in

  lemma_create_zero_buffer #U64 (v (getPointLenU64 c)) c;
  lemma_zero_point_zero_coordinates c h1 tempPoint; 

  Hacl.Impl.P.PointAdd.Aux.lemma_coord_eval c h1 h2 tempPoint;
  Hacl.Impl.P.PointAdd.Aux.lemma_coord_eval c h1 h2 publicKey;
    
  scalar_mult_radix_ publicKey scalar tempBuffer tempPoint precomputedTable;
  
  let h3 = ST.get() in 

  lemma_point_mult_equal_points #c (fromDomainPoint #c #DH (point_as_nat c h1 publicKey)) (fromDomainPoint #c #DH (point_as_nat c h2 (getPointTable c precomputedTable 1))) (scalar_as_nat (as_seq h2 scalar));

  pop_frame();
  let h4 = ST.get() in 
  Hacl.Impl.P.PointAdd.Aux.lemma_coord_eval c h3 h4 publicKey
