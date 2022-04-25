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
val getPointDoubleNTimes: #c: curve -> p: point c -> tempBuffer: lbuffer uint64 (size 17 *! getCoordinateLenU64 c) ->
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


val curve_compatibility_with_translation_lemma_1: #c: curve -> p: Spec.ECC.point #c #Jacobian 
  -> p1: Spec.ECC.point #c #Jacobian
  -> q: Spec.ECC.point #c #Jacobian -> 
  Lemma (pointEqual p p1 <==> pointEqual (pointAdd #c q p) (pointAdd #c q p1))

let curve_compatibility_with_translation_lemma_1 #c p p1 q = 
  curve_compatibility_with_translation_lemma p p1 q;
  curve_commutativity_lemma p q;
  curve_commutativity_lemma p1 q


val point_mult_mult0: #c: curve -> a: nat -> k: nat
  -> p: Spec.ECC.point #c #Jacobian ->
  Lemma (pointEqual (pointAdd (point_mult a p) (point_mult k p)) (point_mult (k + a) p))

let rec point_mult_mult0 #c a k p = 
  match a with
  | 0 -> 
    point_mult_0 p 0;
    curve_point_at_infinity_property (point_mult k p)
  | _ -> 
    point_mult_mult0 #c (a - 1) k p;
    let pa = point_mult a p in  
    let pa1 = point_mult (a - 1) p in  
    let kp = point_mult k p in 
    
    curve_compatibility_with_translation_lemma_1 (pointAdd pa1 kp)  (point_mult (k + a - 1) p) p;
    point_mult_ext (k + a - 1) p;

    curve_associativity p pa1 kp;
    point_mult_ext (a - 1) p;

    curve_compatibility_with_translation_lemma (pointAdd #c p pa1) pa kp


val point_mult_mult1: a: nat -> b: nat -> Lemma (a * (b - 1) + a == a * b)

let point_mult_mult1 a b = ()


val point_mult_mult: #c: curve -> a: nat -> b: nat 
  -> p: Spec.ECC.point #c #Jacobian -> Lemma (
  pointEqual (point_mult b (point_mult a p)) (point_mult (a * b) p))

let rec point_mult_mult #c a b p = 
  match b with 
  |0 -> 
    point_mult_0 p 0;
    point_mult_0 (point_mult a p) 0
  |_ ->
    point_mult_mult #c a (b - 1) p;
    assert(pointEqual (point_mult (b - 1) (point_mult a p)) (point_mult (a * (b - 1)) p));

    let pa = point_mult a p in 
    point_mult_def a p;
    point_mult_def (b - 1) pa;
    point_mult_def (a * (b - 1)) p;

    point_mult_ext #c (b - 1) pa; 

    point_mult_mult0 a (a * (b - 1)) p;
    point_mult_mult1 a b;
    assert(pointEqual (pointAdd (point_mult a p) (point_mult (a * (b - 1)) p)) (point_mult (a * b) p));


    curve_compatibility_with_translation_lemma_1 (point_mult (b - 1) pa) (point_mult (a * (b - 1)) p) pa;
    curve_compatibility_with_translation_lemma (pointAdd #c pa (point_mult (b - 1) pa)) (point_mult b pa) (pointAdd pa (point_mult (a * (b - 1)) p));
    curve_compatibility_with_translation_lemma (pointAdd #c pa (point_mult (a * (b - 1)) p)) (point_mult (a * b) p) (point_mult b pa)


val not_equal_precomputed0: #c: curve 
    -> a: nat
    -> p0: Spec.ECC.point #c #Jacobian 
    -> p1: Spec.ECC.point #c #Jacobian {pointEqual p0 p1} -> 
    Lemma (pointEqual (point_mult a p0) (point_mult a p1))

let rec not_equal_precomputed0 #c a p0 p1 = 
  match a with 
  |0 ->
    point_mult_0 #c p0 0; 
    point_mult_0 #c p1 0
  |_ -> 
    not_equal_precomputed0 #c (a - 1) p0 p1;
    point_mult_ext (a - 1) p0;
    point_mult_ext (a - 1) p1;

    assert(pointEqual (point_mult (a - 1) p0) (point_mult (a - 1) p1));
    assert(pointEqual (pointAdd p0 (point_mult (a - 1) p0)) (point_mult a p0));
    assert(pointEqual (pointAdd p1 (point_mult (a - 1) p1)) (point_mult a p1));

    curve_compatibility_with_translation_lemma_1 (point_mult (a - 1) p0) (point_mult (a - 1) p1) p0;
    curve_compatibility_with_translation_lemma_1 (pointAdd p0 (point_mult (a - 1) p0)) (point_mult a p0) (pointAdd p0 (point_mult (a - 1) p1));
    curve_compatibility_with_translation_lemma p0 p1 (point_mult (a - 1) p1);
    curve_compatibility_with_translation_lemma_1 (pointAdd p1 (point_mult (a - 1) p1)) (point_mult a p1) (point_mult a p0);
    assert(pointEqual (point_mult a p0) (pointAdd p1 (point_mult (a - 1) p1)))


val point_mult_of_point_infinity: #c: curve -> p: Spec.ECC.point #c {isPointAtInfinity #c p} 
  -> a: nat ->
  Lemma (isPointAtInfinity (point_mult a p))

let rec point_mult_of_point_infinity #c p a = 
  match a with 
  |0 -> point_mult_0 p 0 
  |_ -> 
    point_mult_of_point_infinity #c p (a - 1);
    curve_point_at_infinity_property (point_mult (a - 1) p);
    point_mult_ext (a - 1) p


val not_equal_precomputed1: #c: curve 
  -> a: nat {a <= 16} 
  -> b: nat {b < getOrder #c}
  -> p0: Spec.ECC.point #c #Jacobian
  -> Lemma (
    let pa = point_mult #c a p0 in 
    let pb = point_mult #c b p0 in 
    ~ (pointEqual pa pb) \/ (isPointAtInfinity #c #Jacobian pa /\ isPointAtInfinity #c #Jacobian pb))

let not_equal_precomputed1 #c a b p0 = 
  let pa = point_mult #c a p0 in 
  let pb = point_mult #c b p0 in  

  if (isPointAtInfinity #c p0) then begin
     point_mult_of_point_infinity p0 a;
     point_mult_of_point_infinity p0 b
    end
  else 
    if a = 0 || b = 0 then 
       point_mult_0 #c p0 0
    else
      if pointEqual pa pb then 
      begin
	let inv_pb = point_mult #c (getOrder #c - b) p0 in 
	curve_compatibility_with_translation_lemma pa pb inv_pb;
	
	point_mult_mult0 #c b (getOrder #c - b) p0;
	point_mult_0 p0 (getOrder #c); 
	assert(isPointAtInfinity (pointAdd pb inv_pb));

	point_mult_mult0 #c a (getOrder #c - b) p0;
	assert(pointEqual (pointAdd pa inv_pb) (point_mult (a - b + getOrder #c) p0));

	curve_order_is_the_smallest p0;  
	assert(~ (isPointAtInfinity (point_mult (a - b + getOrder #c) p0)));

	assert(False)
      end


val not_equal_precomputed: #c: curve 
  -> z: nat
  -> p: Spec.ECC.point #c #Jacobian
  -> si: nat {si <= 16} -> Lemma
    (requires ((z <= getOrder #c / 16) /\ pointEqual p (point_mult #c z (basePoint #c))))
    (ensures (
      let p_16 = Spec.ECC.Radix.getPointDoubleNTimes #c p 4 in 
      ~ (pointEqual #c p_16 (point_mult #c si (basePoint #c))) \/ (
      isPointAtInfinity #c #Jacobian p_16 /\ isPointAtInfinity #c #Jacobian (point_mult #c si (basePoint #c)))))

let not_equal_precomputed #c z p si = 
  point_mult_mult #c z 16 (basePoint #c);
  not_equal_precomputed0 16 (point_mult z (basePoint #c)) p;
  not_equal_precomputed1 #c si (16 * z) (basePoint #c)


val get_exists_: #c: curve
  -> p: Spec.ECC.point #c #Jacobian 
    {exists (z: nat). ((z <= getOrder #c / 16) /\ pointEqual p (point_mult #c z (basePoint #c)))}
  -> z_test: nat {forall (z: nat {z < z_test}).
    ~  ((z <= getOrder #c / 16) /\ pointEqual p (point_mult #c z (basePoint #c)))}
  -> Tot (z: nat { (z <= getOrder #c / 16) /\ pointEqual p (point_mult #c z (basePoint #c))})
  (decreases (getOrder #c - z_test))

let rec get_exists_ #c p z = 
  if (z <= getOrder #c / 16) && pointEqual p (point_mult #c z (basePoint #c)) 
  then z
  else get_exists_ #c p (z + 1)


val get_exists: #c: curve
  -> p: Spec.ECC.point #c #Jacobian 
    {exists (z: nat). ((z <= getOrder #c / 16) /\ pointEqual p (point_mult #c z (basePoint #c)))}
  -> Tot (z: nat { ((z <= getOrder #c / 16) /\ pointEqual p (point_mult #c z (basePoint #c)))})

let get_exists #c p = get_exists_ #c p 0


val not_equal_precomputed2: #c: curve 
  -> p: Spec.ECC.point #c #Jacobian
       { exists (z: nat {z <= getOrder #c / 16}). pointEqual p (point_mult #c z (basePoint #c))}
  -> si: nat {si <= 16} -> Lemma (
    let p_16 = Spec.ECC.Radix.getPointDoubleNTimes #c p 4 in 
    ~ (pointEqual #c p_16 (point_mult #c si (basePoint #c))) \/ (
    isPointAtInfinity #c #Jacobian p_16 /\ isPointAtInfinity #c #Jacobian (point_mult #c si (basePoint #c))))

let not_equal_precomputed2 #c p si = 
  let z = get_exists #c p in 
  not_equal_precomputed #c z p si
  
  
val radix_step_precomputed0: #c: curve -> p: Spec.ECC.point #c #Jacobian {isPointAtInfinity #c p} -> 
  Lemma (isPointAtInfinity #c (_point_double p))

let radix_step_precomputed0 #c p = 
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
    let fromDomainP_h0 = fromDomainPoint #c #DH (point_as_nat c h p) in 
    exists (z: nat {z <= getOrder #c / 16}). 
      pointEqual fromDomainP_h0 (point_mult #c z (basePoint #c)) /\
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

    let k = as_seq h0 scalar in 
    let scalar = scalar_as_nat k in 
    let si = Math.Lib.arithmetic_shift_right scalar (v (getScalarLen c) - ((v i - 1) + 2) * 4) % pow2 4 in  
    let pRadixed = Spec.ECC.Radix.getPointDoubleNTimes #c (fromDomainPoint #c #DH (point_as_nat c h0 p)) 4 in
    let pointPrecomputed = Spec.ECC.Radix.getPrecomputedPoint #c #Affine (basePoint #c) si in 

    curve_compatibility_with_translation_lemma_1  (fromDomainPoint #c #DH (toJacobianCoordinates #c (point_affine_as_nat c h1 pointToAdd))) (point_mult #c si (basePoint #c)) pRadixed;

    not_equal_precomputed2 #c (fromDomainPoint #c #DH (point_as_nat c h0 p)) si;

    if (isPointAtInfinity #c #Jacobian pRadixed && isPointAtInfinity #c #Jacobian pointPrecomputed) then 
	radix_step_precomputed0 #c pRadixed
    else
      begin 
	curve_compatibility_with_translation_lemma_1 (fromDomainPoint #c #DH (toJacobianCoordinates #c (point_affine_as_nat c h1 pointToAdd))) pointPrecomputed pRadixed;
	curve_compatibility_with_translation_lemma_1  (pointAdd pRadixed (fromDomainPoint #c #DH (toJacobianCoordinates #c (point_affine_as_nat c h1 pointToAdd)))) (pointAdd pRadixed pointPrecomputed) (fromDomainPoint #c #DH (point_as_nat c h3 p))
      end


inline_for_extraction noextract
val radix_precomputed_upload_point: #c: curve -> #buf_type: buftype -> p: point c
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


val montgomery_ladder_2_precomputed: #c: curve -> #buf_type: buftype 
  -> p: point c  -> 
  scalar: lbuffer_t buf_type uint8 (getScalarLenBytes c) -> 
  tempBuffer: lbuffer uint64 (size 17 *! getCoordinateLenU64 c)  -> 
  Stack unit
  (requires fun h -> live h p /\ live h scalar /\ live h tempBuffer /\ 
    point_eval c h p /\ LowStar.Monotonic.Buffer.all_disjoint [loc p; loc tempBuffer; loc scalar] /\ 
    scalar_as_nat (as_seq h scalar) < getOrder #c)
  (ensures fun h0 _ h1 -> modifies (loc p |+| loc tempBuffer) h0 h1 /\ point_eval c h1 p /\ (
    let p_n = fromDomainPoint #c #DH (point_as_nat c h1 p) in 
    pointEqual p_n (point_mult #c (scalar_as_nat (as_seq h0 scalar)) (basePoint #c))))


val lemma_test_2: #c: curve ->  scalar: nat {scalar < getOrder #c} 
  -> i: nat {i > 0 /\ i < v ((size 2 *! getScalarLenBytes c))} -> Lemma (scalar / pow2 4 <= (getOrder #c) / pow2 4)

let lemma_test_2 #c scalar i = 
  let o = getOrder #c in 
  assert(scalar <= o - 1);
  Math.Lemmas.lemma_div_le scalar (o - 1) (pow2 4);
  assert(scalar / (pow2 4) <= (o - 1) / (pow2 4));
  assert(o - 1 < o);
  Math.Lemmas.lemma_div_le (o - 1) o (pow2 4);
  assert((o - 1) / pow2 4 <= o / pow2 4);
  assert(scalar / pow2 4 <= o / pow2 4)

val lemma_test_1: #c: curve ->  scalar: nat {scalar < getOrder #c} 
  -> i: nat {i > 0 /\ i < v ((size 2 *! getScalarLenBytes c))} -> 
  Lemma (scalar / pow2 ((v (getScalarLen c) - i * 4)) <= (getOrder #c) / pow2 4)

let lemma_test_1 #c scalar i = 
  lemma_test_2 #c scalar i;
  assert(v (getScalarLen c) - 4 * i >= 4);
  Math.Lemmas.pow2_le_compat (v (getScalarLen c) - 4 * i) 4;
  assert(pow2 (v (getScalarLen c) - 4 * i) >= pow2 4);
  assert(1 / (pow2 (v (getScalarLen c) - 4 * i)) <= 1 / pow2 4);
  Math.Lemmas.lemma_mult_le_left scalar (1 / (pow2 (v (getScalarLen c) - 4 * i))) (1 / pow2 4);
  assert(scalar * (1 / (pow2 (v (getScalarLen c) - 4 * i))) <= scalar / pow2 4)


let montgomery_ladder_2_precomputed #c #a p scalar tempBuffer =  
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
	lemma_test_1 #c (scalar_as_nat (as_seq h0 scalar)) (v i);
      radix_step_precomputed p tempBuffer scalar i;
	Spec.ECC.Radix.pred0 #c #Affine (fromDomainPoint #c #DH (point_as_nat c h0_ p)) (as_seq h0_ scalar) (basePoint #c) (v i - 1))


(*

[@ CInline]
inline_for_extraction noextract  
val montgomery_ladder_step_radix: 
   #c: curve ->
  p: point P256 -> tempBuffer: lbuffer uint64 (size 88) -> 
  precomputedTable: lbuffer uint64 (size 192) ->
  scalar:  lbuffer uint8 (size 32) -> 
  i:size_t{v i < 256} -> 
  Stack unit
  (requires fun h -> live h p /\live h tempBuffer /\ live h scalar /\
    LowStar.Monotonic.Buffer.all_disjoint [loc p;loc tempBuffer; loc scalar])
  (ensures fun h0 _ h1 -> True)



let montgomery_ladder_step_radix #c p tempBuffer precomputedTable scalar i =  
  let bits = getScalar_4_byBit #c scalar i in 

  let pointToAdd = create (size 12) (u64 0) in 

  let invK h (k: nat) = True in 
  Lib.Loops.for 0ul 16ul invK
  (fun k -> 
      let mask = eq_mask (to_u64 bits) (to_u64 k) in 
      (* eq_mask_lemma d (to_u64 k);  *)
  
      let lut_cmb_x = sub precomputedTable (k *! 12) (size 4) in 
      let lut_cmb_y = sub precomputedTable (k *! 12 +! (size 4)) (size 4) in
      let lut_cmb_z = sub precomputedTable (k *! 12 +! (size 8)) (size 4) in 

      copy_conditional #c (sub pointToAdd (size 0) (size 4)) lut_cmb_x mask;
      copy_conditional #c (sub pointToAdd (size 4) (size 4)) lut_cmb_y mask;
      copy_conditional #c (sub pointToAdd (size 8) (size 4)) lut_cmb_z mask
      
      
      ); 
      
  
  point_double p p tempBuffer;
  point_double p p tempBuffer;
  point_double p p tempBuffer;
  point_double p p tempBuffer;

  point_add pointToAdd p p tempBuffer


[@ CInline]
val generatePrecomputedTable: #c: curve -> b: lbuffer uint64 (size 192) -> publicKey: point c ->
  tempBuffer: lbuffer uint64 (size 88) -> Stack unit  
  (requires fun h -> True)
  (ensures fun h0 _ h1 -> True)

let generatePrecomputedTable #c b publicKey tempBuffer = 
  let point0 = sub b (size 0) (size 12) in 
  let point1 = sub b (size 12) (size 12) in 
  let point2 = sub b (size 24) (size 12) in 
  let point3 = sub b (size 36) (size 12) in 
  let point4 = sub b (size 48) (size 12) in 
  let point5 = sub b (size 60) (size 12) in 
  let point6 = sub b (size 72) (size 12) in 
  let point7 = sub b (size 84) (size 12) in 
  let point8 = sub b (size 96) (size 12) in 
  let point9 = sub b (size 108) (size 12) in 
  let point10 = sub b (size 120) (size 12) in 
  let point11 = sub b (size 132) (size 12) in 
  let point12 = sub b (size 144) (size 12) in 
  let point13 = sub b (size 156) (size 12) in 
  let point14 = sub b (size 168) (size 12) in 
  let point15 = sub b (size 180) (size 12) in 

  Hacl.Impl.EC.LowLevel.uploadZeroPoint #c point0;
  Hacl.Impl.EC.LowLevel.copy_point #c publicKey point1;
  point_double #c publicKey point2 tempBuffer;
  point_add #c point2 point1 point3 tempBuffer;
  point_double #c point2 point4 tempBuffer;
  point_add #c point4 point1 point5 tempBuffer;
  point_double #c point3 point6 tempBuffer;
  point_add #c point6 point1 point7 tempBuffer;
  point_double #c point4 point8 tempBuffer;
  point_add #c point8 point1 point9 tempBuffer;
  point_double #c point5 point10 tempBuffer;
  point_add #c point10 point1 point11 tempBuffer;
  point_double #c point6 point12 tempBuffer;
  point_add #c point12 point1 point13 tempBuffer;
  point_double #c point7 point14 tempBuffer;
  point_add #c point14 point1 point15 tempBuffer



inline_for_extraction noextract
val montgomery_ladder_2: #buf_type: buftype -> #c: curve -> p: point c -> 
  scalar: lbuffer_t buf_type uint8 (size 32) -> 
  tempBuffer:  lbuffer uint64 (size 88)  -> 
  precomputedTable: lbuffer uint64 (size 192) ->
  Stack unit
  (requires fun h -> True )
  (ensures fun h0 _ h1 -> modifies (loc p |+| loc tempBuffer) h0 h1)

let montgomery_ladder_2 #a #c p scalar tempBuffer precomputedTable =  
 let h0 = ST.get() in 
   push_frame();

     [@inline_let]
     let spec_ml h0 = _ml_step #c (as_seq h0 scalar) in 


     [@inline_let]
     let inv h (i: nat {i <= 64}) = True in 


  let bits =  getScalar_4_byBit #c  scalar (u64 0) in 
  let pointToStart = sub precomputedTable  (bits *. size 12) (size 12) in 

  copy (sub p (size 0) (size 12)) pointToStart;
  
     for 1ul 64ul inv 
       (fun i -> let h2 = ST.get() in
   montgomery_ladder_step_radix #c p tempBuffer precomputedTable scalar i
       );
   pop_frame()





inline_for_extraction noextract
val scalar_multiplication_t_0: #c: curve -> #t:buftype ->  p: point c -> result: point c -> 
  scalar: scalar_t #t #c -> 
  tempBuffer: lbuffer uint64 (size 17 *! getCoordinateLenU64 c) ->
  Stack unit 
  (requires fun h -> True (* live h q /\ live h p /\ live h result /\ live h scalar /\ live h tempBuffer /\
    LowStar.Monotonic.Buffer.all_disjoint [loc p; loc q; loc tempBuffer; loc scalar] /\
    disjoint q result /\ eq_or_disjoint p result /\ disjoint result tempBuffer /\ disjoint result scalar /\
    point_eval c h p /\ ~ (isPointAtInfinity (point_as_nat c h p)) *))
  (ensures fun h0 _ h1 -> True (* modifies (loc q |+| loc result |+| loc tempBuffer) h0 h1 /\ point_eval c h1 q /\ (
    let i1 = point_as_nat c h0 p in point_mult_0 i1 0; 
    let pD = fromDomainPoint #c #DH (point_as_nat c h1 q) in
    let r0, r1 = montgomery_ladder_spec_left (as_seq h0 scalar) (pointAtInfinity, i1) in 
    pD == r0 *))


let scalar_multiplication_t_0 #c p result scalar tempBuffer = 
(*     let len = getCoordinateLenU64 c in 
  let q = sub tempBuffer (size 0) (size 3 *! len) in 
  uploadStartPoints q p result; 
  montgomery_ladder q result scalar tempBuffer;
  copy q result *)
  let bufferPrecomputed = create (size 192) (u64 0) in 
  generatePrecomputedTable bufferPrecomputed result tempBuffer;
  montgomery_ladder_2 result scalar tempBuffer bufferPrecomputed


inline_for_extraction noextract
val secretToPublic_0: #c: curve -> #t: buftype -> q: point c -> result: point c -> 
  scalar: lbuffer_t t uint8 (getScalarLenBytes c) -> 
  tempBuffer: lbuffer uint64 (size 17 *! getCoordinateLenU64 c) ->
  Stack unit 
  (requires fun h -> live h q /\ live h result /\ live h scalar /\ live h tempBuffer /\
    LowStar.Monotonic.Buffer.all_disjoint [loc q; loc tempBuffer; loc scalar] /\
    disjoint q result /\ disjoint result tempBuffer /\ disjoint result scalar)
  (ensures fun h0 _ h1 -> modifies (loc q |+| loc result |+| loc tempBuffer) h0 h1 /\ point_eval c h1 q /\ (
    let i1 = basePoint #c in 
    point_mult_0 #c i1 0; 
    let pD = fromDomainPoint #c #DH (point_as_nat c h1 q) in
    let r0, _ = montgomery_ladder_spec_left (as_seq h0 scalar) (pointAtInfinity #c , i1) in pD == r0))


let secretToPublic_0 #c q result scalar tempBuffer = 
(*   uploadStartPointsS2P q result; 
  montgomery_ladder q result scalar tempBuffer
 *)  montgomery_ladder_2_precomputed result scalar tempBuffer;
  copy q result
