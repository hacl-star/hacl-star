module Hacl.Impl.P256.PointAdd

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Hacl.Impl.P256.Arithmetics

open Lib.Buffer

open Hacl.Lemmas.P256
open Hacl.Spec.P256.Definition
open Hacl.Impl.SolinasReduction
open Hacl.Spec.P256.MontgomeryMultiplication
open Hacl.Impl.P256.LowLevel 
open Hacl.Impl.P256.LowLevel.PrimeSpecific
open Hacl.Impl.P256.MontgomeryMultiplication
open Spec.P256
open Hacl.Impl.P256.Math 

open FStar.Tactics 
open FStar.Tactics.Canon

open FStar.Math.Lemmas

friend Hacl.Spec.P256.MontgomeryMultiplication
open FStar.Mul


#set-options "--z3rlimit 300" 

noextract       
val lemma_pointAddToSpecification: 
  #c: curve -> 
  pxD: nat {pxD < getPrime c} -> pyD: nat {pyD < getPrime c} -> pzD: nat {pzD < getPrime c} -> 
  qxD: nat {qxD < getPrime c} -> qyD: nat {qyD < getPrime c} -> qzD: nat {qzD < getPrime c} -> 
  x3: nat -> y3: nat -> z3: nat -> 
  u1: nat -> u2: nat -> s1: nat -> s2: nat -> 
  h: nat -> r: nat -> 
  Lemma
    (requires (    
      let prime = getPrime c in 
      
      let x3D, y3D, z3D = fromDomain_ #c x3, fromDomain_ #c y3, fromDomain_ #c z3 in 

      let u1D, u2D = fromDomain_ #c u1, fromDomain_ #c u2 in 
      let s1D, s2D = fromDomain_ #c s1, fromDomain_ #c s2 in 
      let rD = fromDomain_ #c r in    
      let hD = fromDomain_ #c h in 
     
      u1 == toDomain_ #c (qzD * qzD * pxD % prime) /\
      u2 == toDomain_ #c (pzD * pzD * qxD % prime) /\
      s1 == toDomain_ #c (qzD * qzD * qzD * pyD % prime) /\
      s2 == toDomain_ #c (pzD * pzD * pzD * qyD % prime) /\
      
      h == toDomain_ #c ((u2D - u1D) % prime) /\
      r == toDomain_ #c ((s2D - s1D) % prime) /\
      (
      if qzD = 0 then 
	fromDomain_ #c x3 == pxD /\ fromDomain_ #c y3 == pyD /\ fromDomain_ #c z3 == pzD
      else if pzD = 0 then 
	fromDomain_ #c x3  == qxD /\ fromDomain_ #c y3 == qyD /\ fromDomain_ #c z3 == qzD 
      else
	x3 == toDomain_ #c ((rD * rD - hD * hD * hD - 2 * hD * hD * u1D) % prime) /\
	y3 == toDomain_ #c (((hD * hD * u1D - x3D) * rD - s1D * hD*hD*hD) % prime) /\
	z3 == toDomain_ #c ((pzD * qzD * hD) % prime)
      )
    )
  )
  (ensures 
  (    
    let x3D, y3D, z3D = fromDomain_ #c x3, fromDomain_ #c y3, fromDomain_ #c z3 in 
    let (xN, yN, zN) = _point_add #c (pxD, pyD, pzD) (qxD, qyD, qzD) in
    let u1D = fromDomain_ #c u1 in let u2D = fromDomain_ #c u2 in 
    let s1D = fromDomain_ #c s1 in let s2D = fromDomain_ #c s2 in 
    xN == x3D /\  yN == y3D /\ zN == z3D
  )
)


let lemma_pointAddToSpecification #c x1D y1D z1D x2D y2D z2D x3 y3 z3  u1 u2 s1 s2 h r = 
  let open FStar.Tactics in 
  let open FStar.Tactics.Canon in 

  let prime = getPrime c in 
   
  let u1D = fromDomain_ #c u1 in 
  let u2D = fromDomain_ #c u2 in 
  let s1D = fromDomain_ #c s1 in 
  let s2D = fromDomain_ #c s2 in 

  let hD = fromDomain_ #c h in 
  let rD = fromDomain_ #c r in 

  let x3D, y3D, z3D = fromDomain_ #c x3, fromDomain_ #c y3, fromDomain_ #c z3 in 

  let pxD, pyD, pzD = x1D, y1D, z1D in 
  let qxD, qyD, qzD = x2D, y2D, z2D in 

     assert(

     let prime = getPrime c in 

      u1 == toDomain_ #c (z2D * z2D * pxD % prime) /\
      u2 == toDomain_ #c (pzD * pzD * qxD % prime) /\
      s1 == toDomain_ #c (qzD * qzD * qzD * pyD % prime) /\
      s2 == toDomain_ #c (pzD * pzD * pzD * qyD % prime) /\
      
      h == toDomain_ #c ((u2D - u1D) % prime) /\
      r == toDomain_ #c ((s2D - s1D) % prime) /\
      (
      if qzD = 0 then 
	x3D == pxD /\ y3D == pyD /\  z3D == pzD
      else if pzD = 0 then 
	x3D == qxD /\ y3D == qyD /\ z3D == qzD 
      else
	x3 == toDomain_ #c ((rD * rD - hD * hD * hD - 2 * hD * hD * u1D) % prime) /\
	y3 == toDomain_ #c (((hD * hD * u1D - x3D) * rD - s1D * hD * hD * hD) % prime) /\
	z3 == toDomain_ #c ((pzD * qzD * hD) % prime)));

  let (xN, yN, zN) = _point_add #c (x1D, y1D, z1D) (x2D, y2D, z2D) in 

  assert_by_tactic (z2D * z2D * pxD = pxD * (z2D * z2D)) canon; 
  assert_by_tactic (z1D * z1D * x2D == x2D * (z1D * z1D)) canon;

  assert_by_tactic (z2D * z2D * z2D * y1D = y1D * z2D * (z2D * z2D)) canon;
  assert_by_tactic (z1D * z1D * z1D * y2D = y2D * z1D * (z1D * z1D)) canon;

  let z2z2 = z2D * z2D in
  let z1z1 = z1D * z1D in

  let u1 = x1D * z2z2 % prime in
  let u2 = x2D * z1z1 % prime in

  let s1 = y1D * z2D * z2z2 % prime in
  let s2 = y2D * z1D * z1z1 % prime in

  assert(u1 == u1D);
  assert(u2 == u2D);
  assert(s1 == s1D);
  assert(s2 == s2D);

  let h = (u2 - u1) % prime in
  assert(h == hD);
  
  let r = (s2 - s1) % prime in
  assert(r == rD);

  let rr = r * r in
  let hh = h * h in
  let hhh = h * h * h in

  let x3_ = (r * r - h * h * h - 2 * u1 * hh) % prime in 
    assert_by_tactic (2 * u1 * (h * h) == 2 * h * h * u1) canon;

  let y3_ = (r * (u1 * (h * h) - x3_) - s1 * (h * h * h)) % prime in
    assert_by_tactic ((h * h * u1 - x3_) == (u1 * (h * h) - x3_)) canon;
    assert_by_tactic ((r * (h * h * u1 - x3_) - s1 * (h * h * h)) = ((h * h * u1 - x3_) * r - s1 * h * h * h)) canon; 

  let z3_ = (h * z1D * z2D) % prime in 
    
    assert_by_tactic (z1D * z2D * hD = hD * z1D * z2D) canon;

  if z2D = 0 then
    assert(xN == x1D /\ yN == y1D /\ zN == z1D)
  else
    if z1D = 0 then
      assert(xN == x2D /\ yN == y2D /\ zN == z2D)
    else
      assert(xN == x3_ /\ yN == y3_ /\ zN == z3_)
      

val lemma_point_add_0: #cu: curve -> a: int -> b: int -> c: int -> Lemma 
  (
    let prime = getPrime cu in 
    (a - b - 2 * (c % prime)) % prime == (a - b - 2 * c) % prime)

let lemma_point_add_0 #cu a b c = 
  let prime = getPrime cu in 
  lemma_mod_sub_distr (a - b) (2 * (c % prime)) prime;
  lemma_mod_mul_distr_r 2 c prime;
  lemma_mod_sub_distr (a - b) (2 * c) prime


val lemma_point_add_1: #cu: curve -> a: int -> b: int -> c: int -> d: int -> e: int -> Lemma
  (
    let prime = getPrime cu in 
    (((a % prime) - b) * c - d * (e % prime)) % prime == ((a - b) * c - d * e) % prime)

let lemma_point_add_1 #cu a b c d e = 
  let prime = getPrime cu in 
  lemma_mod_add_distr (- d * (e % prime)) (((a % prime) - b) * c) prime;
  lemma_mod_mul_distr_l ((a % prime) - b) c prime;
  lemma_mod_add_distr (-b) a prime;
  lemma_mod_mul_distr_l (a - b) c prime;
  lemma_mod_add_distr (- d * (e % prime)) ((a - b) * c) prime;
 
  lemma_mod_sub_distr ((a - b) * c) (d * (e % prime)) prime;
  lemma_mod_mul_distr_r d e prime;
  lemma_mod_sub_distr ((a - b) * c) (d * e) prime



val copy_point_conditional: #c: curve ->  x3_out: felem c -> y3_out: felem c -> z3_out: felem c -> p: point c -> maskPoint: point c -> Stack unit
  (requires fun h -> live h x3_out /\ live h y3_out /\ live h z3_out /\ live h p /\ live h maskPoint /\ 
    LowStar.Monotonic.Buffer.all_disjoint [loc x3_out; loc y3_out; loc z3_out; loc p; loc maskPoint] /\
      (
	let prime = getPrime c in 
	let len = getCoordinateLenU64 c in 
	as_nat c h x3_out < prime /\ as_nat c h y3_out < prime /\ as_nat c h z3_out < prime  /\
	as_nat c h (gsub p (size 0) len) < prime /\ 
	as_nat c h (gsub p len len) < prime /\ 
	as_nat c h (gsub p (size 2 *! len) len) < prime 
    )
  )
  (ensures fun h0 _ h1 -> modifies (loc x3_out |+| loc y3_out |+| loc z3_out) h0 h1 /\ 
    (
      let prime = getPrime c in 
      let len = getCoordinateLenU64 c in 
      
      as_nat c h1 x3_out < prime /\
      as_nat c h1 y3_out < prime /\
      as_nat c h1 z3_out < prime  /\
      (
	let coordinateMask = gsub maskPoint (size 2 *! len) len in 
	let mask = as_nat c h0 coordinateMask in 
	
	let x, y, z = gsub p (size 0) len, gsub p len len, gsub p (size 2 *! len) len in
	if mask = 0 then 
	  as_nat c h1 x3_out == as_nat c h0 x /\ 
	  as_nat c h1 y3_out == as_nat c h0 y /\ 
	  as_nat c h1 z3_out == as_nat c h0 z
	else 
	  as_nat c h1 x3_out == as_nat c h0 x3_out /\ 
	  as_nat c h1 y3_out == as_nat c h0 y3_out /\ 
	  as_nat c h1 z3_out == as_nat c h0 z3_out
	) 
    ) 
)


let copy_point_conditional #c x3_out y3_out z3_out p maskPoint = 
  let len : FStar.UInt32.t = getCoordinateLenU64 c in 
  
  let z = sub maskPoint (size 2 *! len) len in 
  let mask = isZero_uint64_CT #c z in 
  
  let p_x = sub p (size 0) len in 
  let p_y = sub p len len in 
  let p_z = sub p (size 2 *! len) len in 

  copy_conditional x3_out p_x mask;
  copy_conditional y3_out p_y mask;
  copy_conditional z3_out p_z mask


inline_for_extraction noextract 
val move_from_jacobian_coordinates: #c: curve -> u1: felem c -> u2: felem c -> s1: felem c -> s2: felem c -> p: point c -> q: point c -> 
  tempBuffer16: lbuffer uint64 (size 4 *! getCoordinateLenU64 c) -> 
  Stack unit (requires fun h -> live h u1 /\ live h u2 /\ live h s1 /\ live h s2 /\ live h p /\ live h q /\ live h tempBuffer16 /\
   LowStar.Monotonic.Buffer.all_disjoint [loc tempBuffer16; loc p; loc q; loc u1; loc u2; loc s1; loc s2] /\
     (
       let prime = getPrime c in 
       let len = getCoordinateLenU64 c in 
       
       as_nat c h (gsub p (size 0) len) < prime /\ 
       as_nat c h (gsub p len len) < prime /\ 
       as_nat c h (gsub p (size 2 *! len) len) < prime /\
       
       as_nat c h (gsub q (size 0) len) < prime /\ 
       as_nat c h (gsub q len len) < prime /\ 
       as_nat c h (gsub q (size 2 *! len) len) < prime
     )
    )
  (ensures fun h0 _ h1 ->  
    modifies (loc u1 |+| loc u2 |+| loc s1 |+| loc s2 |+| loc tempBuffer16) h0 h1 /\
      (
	let prime = getPrime c in 
	let len = getCoordinateLenU64 c in 
	
	as_nat c h1 u1 < prime /\ as_nat c h1 u2 < prime /\ as_nat c h1 s1 < prime /\ as_nat c h1 s2 < prime  /\
	(
	let pX, pY, pZ = as_nat c h0 (gsub p (size 0) len), as_nat c h0 (gsub p len len), as_nat c h0 (gsub p (size 2 *! len) len) in 
	let qX, qY, qZ = as_nat c h0 (gsub q (size 0) len), as_nat c h0 (gsub q len len), as_nat c h0 (gsub q (size 2 *! len) len) in 
      
	let pxD, pyD, pzD = fromDomain_ #c pX, fromDomain_ #c pY, fromDomain_ #c pZ in 
	let qxD, qyD, qzD = fromDomain_ #c qX, fromDomain_ #c qY, fromDomain_ #c qZ in 

	as_nat c h1 u1 == toDomain_ #c (qzD * qzD * pxD % prime) /\
	as_nat c h1 u2 == toDomain_ #c (pzD * pzD * qxD % prime) /\
	as_nat c h1 s1 == toDomain_ #c (qzD * qzD * qzD * pyD % prime) /\
	as_nat c h1 s2 == toDomain_ #c (pzD * pzD * pzD * qyD % prime)
    )
  )
)

let move_from_jacobian_coordinates #c u1 u2 s1 s2 p q tempBuffer = 
  let h0 = ST.get() in 

  let len = getCoordinateLenU64 c in 
    
  let pX = sub p (size 0) len in 
  let pY = sub p len len in 
  let pZ = sub p (size 2 *! len) len in 

  let qX = sub q (size 0) len in 
  let qY = sub q len len in 
  let qZ = sub q (size 2 *! len) len in 

  let z2Square = sub tempBuffer (size 0) len in 
  let z1Square = sub tempBuffer len len in 
  let z2Cube = sub tempBuffer (size 2 *! len) len in 
  let z1Cube = sub tempBuffer (size 3 *! len) len in  

  montgomery_square_buffer #c qZ z2Square;
  montgomery_square_buffer #c pZ z1Square;
  montgomery_multiplication_buffer #c z2Square qZ z2Cube;
   
  montgomery_multiplication_buffer #c z1Square pZ z1Cube;
  montgomery_multiplication_buffer #c z2Square pX u1;
  montgomery_multiplication_buffer #c  z1Square qX u2;
    
  montgomery_multiplication_buffer #c z2Cube pY s1;
  montgomery_multiplication_buffer #c z1Cube qY s2;

  let prime = getPrime c in 

     lemma_mod_mul_distr_l (fromDomain_ #c (as_nat c h0 qZ) * fromDomain_ #c (as_nat c h0 qZ)) (fromDomain_ #c (as_nat c h0 qZ)) prime;
     lemma_mod_mul_distr_l (fromDomain_ #c (as_nat c h0 pZ) * fromDomain_ #c (as_nat c h0 pZ)) (fromDomain_ #c (as_nat c h0 pZ)) prime;
     lemma_mod_mul_distr_l (fromDomain_ #c (as_nat c h0 qZ) * fromDomain_ #c (as_nat c h0 qZ)) (fromDomain_ #c (as_nat c h0 pX)) prime;   
     
     lemma_mod_mul_distr_l (fromDomain_ #c (as_nat c h0 pZ) * fromDomain_ #c (as_nat c h0 pZ)) (fromDomain_ #c (as_nat c h0 qX)) prime;
     lemma_mod_mul_distr_l (fromDomain_ #c (as_nat c h0 qZ) * fromDomain_ #c (as_nat c h0 qZ) * fromDomain_ #c (as_nat c h0 qZ)) (fromDomain_ #c (as_nat c h0 pY)) prime;
     lemma_mod_mul_distr_l (fromDomain_ #c (as_nat c h0 pZ) * fromDomain_ #c (as_nat c h0 pZ) * fromDomain_ #c (as_nat c h0 pZ)) (fromDomain_ #c (as_nat c h0 qY)) prime


inline_for_extraction noextract 
val compute_common_params_point_add: #c: curve -> h: felem c -> r: felem c -> uh: felem c -> 
  hCube: felem c -> u1: felem c -> u2: felem c -> s1: felem c -> s2: felem c -> 
  tempBuffer: lbuffer uint64 (size 4 *! getCoordinateLenU64 c) -> 
  Stack unit 
    (requires fun h0 -> 
      let prime = getPrime c in 
      live h0 h /\ live h0 r /\ live h0 uh /\ live h0 hCube /\ live h0 u1 /\ 
      live h0 u2 /\ live h0 s1 /\ live h0 s2 /\ live h0 tempBuffer /\  
      LowStar.Monotonic.Buffer.all_disjoint [loc u1; loc u2; loc s1; loc s2; loc h; loc r; loc uh; loc hCube; loc tempBuffer] /\ 
      as_nat c h0 u1 < prime /\ 
      as_nat c h0 u2 < prime /\ 
      as_nat c h0 s1 < prime /\ 
      as_nat c h0 s2 < prime)
    (ensures fun h0 _ h1 -> 
      modifies (loc h |+| loc r |+| loc uh |+| loc hCube |+| loc tempBuffer) h0 h1 /\ (
      let prime = getPrime c in 
      as_nat c h1 h < prime /\ 
      as_nat c h1 r < prime /\ 
      as_nat c h1 uh < prime /\ 
      as_nat c h1 hCube < prime /\ (
      
      let u1D = fromDomain_ #c (as_nat c h0 u1) in 
      let u2D = fromDomain_ #c (as_nat c h0 u2) in 
      let s1D = fromDomain_ #c (as_nat c h0 s1) in 
      let s2D = fromDomain_ #c (as_nat c h0 s2) in 
	
      let hD = fromDomain_ #c (as_nat c h1 h) in 
      
      as_nat c h1 h == toDomain_ #c ((u2D - u1D) % prime) /\
      as_nat c h1 r == toDomain_ #c ((s2D - s1D) % prime) /\
      as_nat c h1 uh == toDomain_ #c (hD * hD * u1D % prime) /\
      as_nat c h1 hCube == toDomain_ #c (hD * hD * hD % prime)))
  )


let compute_common_params_point_add #c h r uh hCube u1 u2 s1 s2 tempBuffer =  
    let h0 = ST.get() in 
  let len = getCoordinateLenU64 c in
  let temp = sub tempBuffer (size 0) len in 
  
  felem_sub u2 u1 h; 
  let h1 = ST.get() in
  felem_sub s2 s1 r; 
  let h2 = ST.get() in   
  montgomery_square_buffer h temp;
  let h3 = ST.get() in   
  montgomery_multiplication_buffer temp u1 uh;
  montgomery_multiplication_buffer temp h hCube;

  let prime = getPrime c in 
  lemma_mod_mul_distr_l (fromDomain_ #c (as_nat c h2 h) * fromDomain_ #c (as_nat c h2 h)) (fromDomain_ #c (as_nat c h3 u1)) prime;
  lemma_mod_mul_distr_l (fromDomain_ #c (as_nat c h2 h) * fromDomain_ #c (as_nat c h2 h)) (fromDomain_ #c (as_nat c h1 h)) prime


inline_for_extraction noextract 
val computeX3_point_add: #c : curve -> x3: felem c -> hCube: felem c -> uh: felem c -> 
  r: felem c -> tempBuffer: lbuffer uint64 (size 4 *! getCoordinateLenU64 c) ->  
  Stack unit 
  (requires fun h0 -> 
    let prime = getPrime c in  
    live h0 x3 /\ live h0 hCube /\ live h0 uh /\ live h0 r /\ live h0 tempBuffer /\
    LowStar.Monotonic.Buffer.all_disjoint [loc x3; loc hCube; loc uh; loc r; loc tempBuffer] /\
    as_nat c h0 hCube < prime /\as_nat c h0 uh < prime /\ as_nat c h0 r < prime)
  (ensures fun h0 _ h1 -> 
    let prime = getPrime c in 
    modifies (loc x3 |+| loc tempBuffer) h0 h1 /\ as_nat c h1 x3 < prime /\ 
    (
      let hCubeD = fromDomain_ #c (as_nat c h0 hCube) in 
      let uhD = fromDomain_ #c (as_nat c h0 uh) in 
      let rD = fromDomain_ #c (as_nat c h0 r) in 
      as_nat c h1 x3 == toDomain_ #c ((rD * rD - hCubeD - 2 * uhD) % prime)
    )  
  )

let computeX3_point_add #c x3 hCube uh r tempBuffer = 
  let h0 = ST.get() in
  
  let len = getCoordinateLenU64 c in 
  
  let rSquare = sub tempBuffer (size 0) len in 
  let rH = sub tempBuffer len len in 
  let twoUh = sub tempBuffer (size 2 *! len) len in 
  montgomery_square_buffer r rSquare; 
    let h1 = ST.get() in 
  felem_sub rSquare hCube rH;
    let h2 = ST.get() in 
  multByTwo uh twoUh;
    let h3 = ST.get() in
  felem_sub rH twoUh x3; 

  let prime = getPrime c in 
  lemma_mod_add_distr (- fromDomain_ #c (as_nat c h1 hCube)) (fromDomain_ #c (as_nat c h0 r) * fromDomain_ #c (as_nat c h0 r)) prime;
  lemma_mod_add_distr (- fromDomain_ #c (as_nat c h3 twoUh)) (fromDomain_ #c (as_nat c h0 r) * fromDomain_ #c (as_nat c h0 r) - fromDomain_ #c (as_nat c h1 hCube)) prime;
  lemma_mod_sub_distr (fromDomain_ #c (as_nat c h0 r) * fromDomain_ #c (as_nat c h0 r) - fromDomain_ #c (as_nat c h1 hCube)) (2 * fromDomain_ #c (as_nat c h2 uh)) prime


inline_for_extraction noextract 
val computeY3_point_add: #c: curve -> y3: felem c -> s1: felem c -> 
  hCube: felem c -> uh: felem c -> x3_out: felem c -> r: felem c -> 
  tempBuffer: lbuffer uint64 (size 4 *! getCoordinateLenU64 c) -> 
  Stack unit 
    (requires fun h -> 
      let prime = getPrime c in 
      live h y3 /\ live h s1 /\ live h hCube /\ live h uh /\ live h x3_out /\ 
      live h r /\ live h tempBuffer /\ 
      LowStar.Monotonic.Buffer.all_disjoint [loc y3; loc s1; loc hCube; loc uh; loc x3_out; loc r; loc tempBuffer] /\
      as_nat c h s1 < prime /\ 
      as_nat c h hCube < prime /\
      as_nat c h uh < prime /\ 
      as_nat c h x3_out < prime /\ 
      as_nat c h r < prime)
    (ensures fun h0 _ h1 -> 
      let prime = getPrime c in 
      modifies (loc y3 |+| loc tempBuffer) h0 h1 /\ as_nat c h1 y3 < prime /\ 
      (
	let s1D = fromDomain_ #c (as_nat c h0 s1) in 
	let hCubeD = fromDomain_ #c (as_nat c h0 hCube) in 
	let uhD = fromDomain_ #c (as_nat c h0 uh) in 
	let x3D = fromDomain_ #c (as_nat c h0 x3_out) in 
	let rD = fromDomain_ #c (as_nat c h0 r) in 
	as_nat c h1 y3 = toDomain_ #c (((uhD - x3D) * rD - s1D * hCubeD) % prime))
      )

    
let computeY3_point_add #c y3 s1 hCube uh x3 r tempBuffer = 
  let h0 = ST.get() in
  
  let len = getCoordinateLenU64 c in 
  let s1hCube = sub tempBuffer (size 0) len in 
  let u1hx3 = sub tempBuffer len len in 
  let ru1hx3 = sub tempBuffer (size 2 *! len) len in 

  montgomery_multiplication_buffer s1 hCube s1hCube;
  felem_sub uh x3 u1hx3;
  montgomery_multiplication_buffer u1hx3 r ru1hx3;
  felem_sub #c ru1hx3 s1hCube y3;
  
  let h3 = ST.get() in 
  let prime = getPrime c in
    lemma_mod_mul_distr_l (fromDomain_ #c (as_nat c h0 uh) - fromDomain_ #c (as_nat c h0 x3)) (fromDomain_ #c (as_nat c h0 r)) prime;

    lemma_mod_add_distr (- (fromDomain_ #c (as_nat c h3 s1hCube)))  ((fromDomain_ #c (as_nat c h0 uh) - fromDomain_ #c (as_nat c h0 x3)) * fromDomain_ #c (as_nat c h0 r)) prime;
    lemma_mod_sub_distr ((fromDomain_ #c (as_nat c h0 uh) - fromDomain_ #c (as_nat c h0 x3)) * fromDomain_ #c (as_nat c h0 r)) (fromDomain_ #c (as_nat c h0 s1) * fromDomain_ #c (as_nat c h0 hCube)) prime


inline_for_extraction noextract 
val computeZ3_point_add: #c: curve -> z3: felem  c ->  z1: felem c -> z2: felem c ->
  h: felem c -> tempBuffer: lbuffer uint64 (size 4 *! getCoordinateLenU64 c) -> 
  Stack unit (requires fun h0 -> 
    let prime = getPrime c in 
    live h0 z3 /\ live h0 z1 /\ live h0 z2 /\ live h0 h /\ 
    live h0 tempBuffer /\ live h0 z3 /\
    LowStar.Monotonic.Buffer.all_disjoint [loc z1; loc z2; loc h; loc tempBuffer; loc z3] /\
    as_nat c h0 z1 < prime /\ as_nat c h0 z2 < prime /\ as_nat  c h0 h < prime)
  (ensures fun h0 _ h1 ->
    let prime = getPrime c in 
    modifies (loc z3 |+| loc tempBuffer) h0 h1 /\ 
    as_nat  c h1 z3 < getPrime c /\ 
    (
      let z1D = fromDomain_ #c (as_nat c h0 z1) in 
      let z2D = fromDomain_ #c (as_nat c h0 z2) in 
      let hD = fromDomain_ #c (as_nat c h0 h) in 
      as_nat c h1 z3 == toDomain_ #c (z1D * z2D * hD % prime)
    )  
  )  


let computeZ3_point_add #c z3 z1 z2 h tempBuffer = 
    let h0 = ST.get() in 
  let z1z2 = sub tempBuffer (size 0) (getCoordinateLenU64 c) in
  montgomery_multiplication_buffer z1 z2 z1z2;
  montgomery_multiplication_buffer z1z2 h z3;
    lemma_mod_mul_distr_l (fromDomain_ #c (as_nat c h0 z1) * fromDomain_ #c (as_nat c h0 z2)) (fromDomain_ #c (as_nat c h0 h)) (getPrime c)

val felem_eval: #c: curve -> h: mem -> b: lbuffer uint64 (getCoordinateLenU64 c) -> Type0

let felem_eval #c h b = as_nat c h b < getPrime c

#push-options "--z3rlimit 500" 


inline_for_extraction noextract 
val point_add_if_second_branch_impl: #c: curve -> result: point c -> p: point c -> 
  q: point c -> u1: felem c -> u2: felem c -> s1: felem c -> 
  s2: felem c -> r: felem c -> h: felem c -> uh: felem c -> hCube: felem c -> 
  tempBuffer28 : lbuffer uint64 (size 7 *! getCoordinateLenU64 c) -> 
  Stack unit 
    (requires fun h0 -> 
      let prime = getPrime c in 
      let len = getCoordinateLenU64 c in
      let len2 : size_t = size 2 *! len in 
      
      live h0 result /\ live h0 p /\ live h0 q /\ live h0 u1 /\ live h0 u2 /\ live h0 s1 /\ 
      live h0 s2 /\ live h0 r /\ live h0 h /\ live h0 uh /\ live h0 hCube /\ live h0 tempBuffer28 /\
  
      felem_eval #c h0 u1 /\ felem_eval #c h0 u2 /\ felem_eval #c h0 s1 /\ felem_eval #c h0 s2 /\
      felem_eval #c h0 h /\ felem_eval #c h0 uh /\ felem_eval #c h0 r /\ felem_eval #c h0 hCube /\

      eq_or_disjoint p result /\

      LowStar.Monotonic.Buffer.all_disjoint [loc p; loc q; loc u1; loc u2; loc s1; loc s2; loc r; loc h; loc uh; loc hCube; loc tempBuffer28] /\ 
      disjoint result tempBuffer28 /\

      (
	let pX = as_nat c h0 (gsub p (size 0) len) in 
	let pY = as_nat c h0 (gsub p len len) in 
	let pZ = as_nat c h0 (gsub p len2 len) in 

	let qX = as_nat c h0 (gsub q (size 0) len) in 
	let qY = as_nat c h0 (gsub q len len) in 
	let qZ = as_nat c h0 (gsub q len2 len) in 

	let pxD, pyD, pzD = fromDomain_ #c pX, fromDomain_ #c pY, fromDomain_ #c pZ in 
	let qxD, qyD, qzD = fromDomain_ #c qX, fromDomain_ #c qY, fromDomain_ #c qZ in 

	let u1D = fromDomain_ #c (as_nat c h0 u1) in 
	let u2D = fromDomain_ #c (as_nat c h0 u2) in 
	let s1D = fromDomain_ #c (as_nat c h0 s1) in 
	let s2D = fromDomain_ #c (as_nat c h0 s2) in 

	let hD = fromDomain_ #c (as_nat c h0 h) in 
      
	pX < prime /\ pY < prime /\ pZ < prime /\
	qX < prime /\ qY < prime /\ qZ < prime /\
	
	as_nat c h0 u1 == toDomain_ #c (qzD * qzD * pxD % prime) /\
	as_nat c h0 u2 == toDomain_ #c (pzD * pzD * qxD % prime) /\
	as_nat c h0 s1 == toDomain_ #c (qzD * qzD * qzD * pyD % prime) /\
	as_nat c h0 s2 == toDomain_ #c (pzD * pzD * pzD * qyD % prime) /\
      
	as_nat c h0 h == toDomain_ #c ((u2D - u1D) % prime) /\
	as_nat c h0 r == toDomain_ #c ((s2D - s1D) % prime) /\
	as_nat c h0 uh == toDomain_ #c (hD * hD * u1D % prime) /\
	as_nat c h0 hCube == toDomain_ #c (hD * hD * hD % prime) 
    )
)
 
  (ensures fun h0 _ h1 -> modifies (loc tempBuffer28 |+| loc result) h0 h1 /\
    (
      let prime = getPrime c in 
      let len = getCoordinateLenU64 c in 
      let len2 : size_t = size 2 *! len in 
  
      let x3, y3, z3 = as_nat c h1 (gsub result (size 0) len), as_nat c h1 (gsub result len len), as_nat c h1 (gsub result len2 len) in  
      
      x3 < prime /\ y3 < prime /\ z3 < prime /\
      (
	let pX, pY, pZ = as_nat c h0 (gsub p (size 0) len), as_nat c h0 (gsub p len len), as_nat c h0 (gsub p len2 len) in 
	let qX, qY, qZ = as_nat c h0 (gsub q (size 0) len), as_nat c h0 (gsub q len len), as_nat c h0 (gsub q len2 len) in 

	let pxD, pyD, pzD = fromDomain_ #c pX, fromDomain_ #c pY, fromDomain_ #c pZ in 
	let qxD, qyD, qzD = fromDomain_ #c qX, fromDomain_ #c qY, fromDomain_ #c qZ in 
	let x3D, y3D, z3D = fromDomain_ #c x3, fromDomain_ #c y3, fromDomain_ #c z3 in 

	let rD = fromDomain_ #c (as_nat c h0 r) in 
	let hD = fromDomain_ #c (as_nat c h0 h) in 
	let s1D = fromDomain_ #c (as_nat c h0 s1) in 
	let u1D = fromDomain_ #c (as_nat c h0 u1) in 

	if qzD = 0 then 
	  x3D == pxD /\ y3D == pyD /\ z3D == pzD
	else if pzD = 0 then 
	  x3D == qxD /\  y3D == qyD /\ z3D == qzD
	else 
	  x3 == toDomain_ #c ((rD * rD - hD * hD * hD - 2 * hD * hD * u1D) % prime) /\ 
	  y3 == toDomain_ #c (((hD * hD * u1D - fromDomain_  #c x3) * rD - s1D * hD * hD * hD) % prime) /\
	  z3 == toDomain_ #c (pzD * qzD * hD % prime) 
  )
  )
)


let point_add_if_second_branch_impl #c result p q u1 u2 s1 s2 r h uh hCube tempBuffer28 = 
  let h0 = ST.get() in
  let len = getCoordinateLenU64 c in 
  
  let pZ = sub p (size 2 *! len) len in 
  let qZ = sub q (size 2 *! len) len in 

  let tempBuffer16 = sub tempBuffer28 (size 0) (size 4 *! len) in admit();
  
  let x3_out = Lib.Buffer.sub tempBuffer28 (size 4 *! len) len in 
  let y3_out = Lib.Buffer.sub tempBuffer28 (size 5 *! len) len in 
  let z3_out = Lib.Buffer.sub tempBuffer28 (size 6 *! len) len in admit();
  
  computeX3_point_add x3_out hCube uh r tempBuffer16; 
    let h1 = ST.get() in 
  computeY3_point_add y3_out s1 hCube uh x3_out r tempBuffer16; 
  computeZ3_point_add z3_out pZ qZ h tempBuffer16;
  
  copy_point_conditional x3_out y3_out z3_out q p;
  copy_point_conditional x3_out y3_out z3_out p q;

  concat3 len x3_out len y3_out len z3_out result; 

  let hEnd = ST.get() in 

  let prime = getPrime c in 

  let rD = fromDomain_ #c (as_nat c h0 r) in 
  let hD = fromDomain_ #c (as_nat c h0 h) in
  let u1D = fromDomain_ #c (as_nat c h0 u1) in 
  let uhD = fromDomain_ #c (as_nat c h0 uh) in 

  let s1D = fromDomain_ #c (as_nat c h0 s1) in 
  let x3D = fromDomain_ #c (as_nat c h1 x3_out) in 

  lemma_point_add_0 #c (rD * rD) (hD * hD * hD) (hD * hD * u1D);
  lemma_mod_sub_distr (rD * rD - 2 * uhD) (hD * hD * hD) prime;
  assert_by_tactic (2 * (hD * hD * u1D) == 2 * hD * hD * u1D) canon;

  lemma_point_add_1 #c (hD * hD * u1D) x3D rD s1D (hD * hD * hD);
  assert_by_tactic (s1D * (hD * hD * hD) == s1D * hD * hD * hD) canon;

  assert_norm (modp_inv2 #P256 (getPower2 P256) > 0);
  assert_norm (modp_inv2 #P384 (getPower2 P384) > 0);
  
  assert_norm (modp_inv2 #P256 (getPower2 P256) % prime <> 0); 
  assert_norm (modp_inv2 #P384 (getPower2 P384) % prime <> 0); 

  lemma_multiplication_not_mod_prime (as_nat c h0 pZ);
  lemma_multiplication_not_mod_prime (as_nat c h0 qZ);
  lemmaFromDomain #c (as_nat c h0 pZ);
  lemmaFromDomain #c (as_nat c h0 qZ);
  admit()

#pop-options


let point_add #c p q result tempBuffer = 
  let h0 = ST.get() in 

  let len = getCoordinateLenU64 c in 
  
  let z1 = sub p (size 2 *! len) len in 
  let z2 = sub q (size 2 *! len) len in 

  let tempBuffer16 = sub tempBuffer (size 0) (size 4 *! len) in 
   
  let u1 = sub tempBuffer (size 4 *! len) len in 
  let u2 = sub tempBuffer (size 5 *! len) len in 
  let s1 = sub tempBuffer (size 6 *! len) len in 
  let s2 = sub tempBuffer (size 7 *! len) len in 

  let h = sub tempBuffer (size 8 *! len) len in 
  let r = sub tempBuffer (size 9 *! len) len in 
  let uh = sub tempBuffer (size 10 *! len) len in 

  let hCube = sub tempBuffer (size 11 *! len) len in 

  let x3_out = sub tempBuffer (size 12 *! len) len in 
  let y3_out = sub tempBuffer (size 13 *! len) len in 
  let z3_out = sub tempBuffer (size 14 *! len) len in 

  let tempBuffer28 = sub tempBuffer (size 15 *! len) (size 7 *! len) in 
  
  move_from_jacobian_coordinates u1 u2 s1 s2 p q tempBuffer16;
  compute_common_params_point_add #c h r uh hCube u1 u2 s1 s2 tempBuffer16;
  point_add_if_second_branch_impl result p q u1 u2 s1 s2 r h uh hCube tempBuffer28;
  
    let h1 = ST.get() in 
      let pxD = fromDomain_ #c (as_nat c h0 (gsub p (size 0) len)) in 
      let pyD = fromDomain_ #c (as_nat c h0 (gsub p len len)) in 
      let pzD = fromDomain_ #c (as_nat c h0 (gsub p (size 2 *! len) len)) in
      
      let qxD = fromDomain_ #c (as_nat c h0 (gsub q (size 0) len)) in 
      let qyD = fromDomain_ #c (as_nat c h0 (gsub q len len)) in 
      let qzD = fromDomain_ #c (as_nat c h0 (gsub q (size 2 *! len) len)) in 
      
      let x3 = as_nat c h1 (gsub result (size 0) len) in 
      let y3 = as_nat c h1 (gsub result len len) in 
      let z3 = as_nat c h1 (gsub result (size 2 *! len) len) in 
      lemma_pointAddToSpecification #c  pxD pyD pzD qxD qyD qzD x3 y3 z3 (as_nat c h1 u1) (as_nat c h1 u2) (as_nat c h1 s1) (as_nat c h1 s2) (as_nat c h1 h) (as_nat c h1 r)

