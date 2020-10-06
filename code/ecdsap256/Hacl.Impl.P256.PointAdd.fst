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
open Hacl.Impl.P.LowLevel
open Hacl.Impl.P256.MontgomeryMultiplication
open Spec.P256
open Hacl.Impl.P256.Math 

open FStar.Tactics 
open FStar.Tactics.Canon

open FStar.Math.Lemmas

friend Hacl.Spec.P256.MontgomeryMultiplication
open FStar.Mul


val point_eval: c: curve -> h: mem -> p: point c -> Type0

let point_eval c h p = 
  felem_eval c h (gsub p (size 0) (getCoordinateLenU64 c)) /\ 
  felem_eval c h (gsub p (getCoordinateLenU64 c) (getCoordinateLenU64 c)) /\ 
  felem_eval c h (gsub p (size 2 *! getCoordinateLenU64 c) (getCoordinateLenU64 c)) 

val getTempXYZ: #c: curve -> tempBuffer7: lbuffer uint64 (size 7 *! getCoordinateLenU64 c) -> 
  GTot (tuple3 (felem c) (felem c) (felem c))

let getTempXYZ #c tempBuffer7 = 
  let len = getCoordinateLenU64 c in 
  let x3_out = gsub tempBuffer7 (size 0) len in 
  let y3_out = gsub tempBuffer7 len len in 
  let z3_out = gsub tempBuffer7 (size 2 *! len) len in 
  (x3_out, y3_out, z3_out)


val getPointZ: #c: curve -> p: point c -> GTot (felem c)

let getPointZ #c p = gsub p (size 2 *! getCoordinateLenU64 c) (getCoordinateLenU64 c)


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
	y3 == toDomain_ #c (((hD * hD * u1D - x3D) * rD - s1D * hD * hD * hD) % prime) /\
	z3 == toDomain_ #c ((pzD * qzD * hD) % prime)
      )
    )
  )
  (ensures 
  (    
    let x3D, y3D, z3D = fromDomain_ #c x3, fromDomain_ #c y3, fromDomain_ #c z3 in 
    let (xN, yN, zN) = _point_add #c (pxD, pyD, pzD) (qxD, qyD, qzD) in
    xN == x3D /\  yN == y3D /\ zN == z3D
  )
)


let lemma_pointAddToSpecification #c pxD pyD pzD qxD qyD qzD x3 y3 z3  u1 u2 s1 s2 h r = 
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

  calc (==)
  {
    qzD * qzD * pxD;
    (==) {_ by (canon())}
    pxD * (qzD * qzD);};

  calc (==)
  {
    pzD * pzD * qxD;
    (==) {_ by (canon())}
    qxD * (pzD * pzD);};  

  calc (==) 
  {
    qzD * qzD * qzD * pyD;
    (==) {_ by (canon())}
    pyD * qzD * (qzD * qzD);};

  calc (==)
  {
    pzD * pzD * pzD * qyD;
    (==) {_ by (canon())}
    qyD * pzD * (pzD * pzD);};

  calc (==) 
  {
    rD * rD - hD * hD * hD - 2 * hD * hD * u1D;
    (==) {_ by (canon())}
    (rD * rD) - (hD * hD * hD) - 2 * u1D * (hD * hD);};

  calc (==)
  {
    (hD * hD * u1D - x3D) * rD - s1D * hD * hD * hD;
    (==) {_ by (canon())}
    rD * (u1D * (hD * hD) - x3D) - s1D * (hD * hD * hD);};

  calc (==) 
  {
    pzD * qzD * hD;
    (==) {_ by (canon())}
    hD * pzD * qzD;}


val lemma_point_add_0: #cu: curve -> a: int -> b: int -> c: int -> Lemma (
  let prime = getPrime cu in 
  (a - b - 2 * (c % prime)) % prime == (a - b - 2 * c) % prime)

let lemma_point_add_0 #cu a b c = 
  let prime = getPrime cu in 
  lemma_mod_sub_distr (a - b) (2 * (c % prime)) prime;
  lemma_mod_mul_distr_r 2 c prime;
  lemma_mod_sub_distr (a - b) (2 * c) prime


val lemma_point_add_1: #cu: curve -> a: int -> b: int -> c: int -> d: int -> e: int -> Lemma (
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


val copy_point_conditional: #c: curve ->  x3_out: felem c -> y3_out: felem c -> z3_out: felem c -> p: point c -> mask: point c -> Stack unit
  (requires fun h -> 
    live h x3_out /\ live h y3_out /\ live h z3_out /\ live h p /\ live h mask /\ 
    LowStar.Monotonic.Buffer.all_disjoint [loc x3_out; loc y3_out; loc z3_out; loc p; loc mask]
  )
  (ensures fun h0 _ h1 -> modifies (loc x3_out |+| loc y3_out |+| loc z3_out) h0 h1 /\ (
    let mask = point_z_as_nat c h0 mask in 
    let x, y, z = point_x_as_nat c h0 p, point_y_as_nat c h0 p, point_z_as_nat c h0 p in
    if mask = 0 then 
      as_nat c h1 x3_out == x /\
      as_nat c h1 y3_out == y /\ 
      as_nat c h1 z3_out == z
    else 
      as_nat c h1 x3_out == as_nat c h0 x3_out /\ 
      as_nat c h1 y3_out == as_nat c h0 y3_out /\ 
      as_nat c h1 z3_out == as_nat c h0 z3_out))


let copy_point_conditional #c x3_out y3_out z3_out p maskPoint = 
  let len  = getCoordinateLenU64 c in 
  
  let z = sub maskPoint (size 2 *! len) len in 
  let mask = isZero_uint64_CT #c z in 
  
  let p_x = sub p (size 0) len in 
  let p_y = sub p len len in 
  let p_z = sub p (size 2 *! len) len in 

  copy_conditional x3_out p_x mask;
  copy_conditional y3_out p_y mask;
  copy_conditional z3_out p_z mask




inline_for_extraction noextract 
val _move_from_jacobian_coordinates: #c: curve -> u1: felem c -> u2: felem c -> 
  s1: felem c -> s2: felem c -> p: point c -> q: point c -> 
  tempBuffer4: lbuffer uint64 (size 4 *! getCoordinateLenU64 c) -> 
  Stack unit (requires fun h ->  
    live h u1 /\ live h u2 /\ live h s1 /\ live h s2 /\ 
    live h p /\ live h q /\ live h tempBuffer4 /\
    LowStar.Monotonic.Buffer.all_disjoint [loc tempBuffer4; loc p; loc q; loc u1; loc u2; loc s1; loc s2] /\ 
    point_eval c h p /\ point_eval c h q)
  (ensures fun h0 _ h1 ->  
  
    let prime = getPrime c in 
    modifies (loc u1 |+| loc u2 |+| loc s1 |+| loc s2 |+| loc tempBuffer4) h0 h1 /\ 
    felem_eval c h1 u1 /\ felem_eval c h1 u2 /\ felem_eval c h1 s1 /\ felem_eval c h1 s1 /\ (
    let pX, pY, pZ = point_x_as_nat c h0 p, point_y_as_nat c h0 p, point_z_as_nat c h0 p in 
    let qX, qY, qZ = point_x_as_nat c h0 q, point_y_as_nat c h0 q, point_z_as_nat c h0 q in 
      
    let pxD, pyD, pzD = fromDomain_ #c pX, fromDomain_ #c pY, fromDomain_ #c pZ in 
    let qxD, qyD, qzD = fromDomain_ #c qX, fromDomain_ #c qY, fromDomain_ #c qZ in 

    as_nat c h1 u1 == toDomain_ #c (qzD * qzD * pxD % prime) /\
    as_nat c h1 u2 == toDomain_ #c (pzD * pzD * qxD % prime) /\
    as_nat c h1 s1 == toDomain_ #c (qzD * qzD * qzD * pyD % prime) /\
    as_nat c h1 s2 == toDomain_ #c (pzD * pzD * pzD * qyD % prime)
    )
  )


let _move_from_jacobian_coordinates #c u1 u2 s1 s2 p q tempBuffer = 
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
val move_from_jacobian_coordinates: #c: curve -> p: point c -> q: point c -> 
  tempBuffer22: lbuffer uint64 (size 22 *! getCoordinateLenU64 c) -> 
  Stack unit (requires fun h ->  
    live h p /\ live h q /\ live h tempBuffer22 /\
    LowStar.Monotonic.Buffer.all_disjoint [loc tempBuffer22; loc p; loc q] /\ 
    point_eval c h p /\ point_eval c h q)
  (ensures fun h0 _ h1 ->  
    let prime = getPrime c in 
    let len = getCoordinateLenU64 c in 
    
    modifies (loc tempBuffer22) h0 h1 /\ (
    let u1 = gsub tempBuffer22 (size 4 *! len) len in 
    let u2 = gsub tempBuffer22 (size 5 *! len) len in 
    let s1 = gsub tempBuffer22 (size 6 *! len) len in 
    let s2 = gsub tempBuffer22 (size 7 *! len) len in 

    felem_eval c h1 u1 /\ felem_eval c h1 u2 /\ felem_eval c h1 s1 /\ felem_eval c h1 s1 /\ (
    let pX, pY, pZ = point_x_as_nat c h0 p, point_y_as_nat c h0 p, point_z_as_nat c h0 p in 
    let qX, qY, qZ = point_x_as_nat c h0 q, point_y_as_nat c h0 q, point_z_as_nat c h0 q in 
      
    let pxD, pyD, pzD = fromDomain_ #c pX, fromDomain_ #c pY, fromDomain_ #c pZ in 
    let qxD, qyD, qzD = fromDomain_ #c qX, fromDomain_ #c qY, fromDomain_ #c qZ in 

    as_nat c h1 u1 == toDomain_ #c (qzD * qzD * pxD % prime) /\
    as_nat c h1 u2 == toDomain_ #c (pzD * pzD * qxD % prime) /\
    as_nat c h1 s1 == toDomain_ #c (qzD * qzD * qzD * pyD % prime) /\
    as_nat c h1 s2 == toDomain_ #c (pzD * pzD * pzD * qyD % prime)
    ) 
  )
)

let move_from_jacobian_coordinates #c p q tempBuffer22 = 
  let len = getCoordinateLenU64 c in   
  
  let tempBuffer4 = sub tempBuffer22 (size 0) (size 4 *! len) in 
   
  let u1 = sub tempBuffer22 (size 4 *! len) len in 
  let u2 = sub tempBuffer22 (size 5 *! len) len in 
  let s1 = sub tempBuffer22 (size 6 *! len) len in 
  let s2 = sub tempBuffer22 (size 7 *! len) len in 

  _move_from_jacobian_coordinates #c u1 u2 s1 s2 p q tempBuffer4


inline_for_extraction noextract 
val _compute_common_params_point_add: #c: curve -> h: felem c -> r: felem c -> uh: felem c -> 
  hCube: felem c -> u1: felem c -> u2: felem c -> s1: felem c -> s2: felem c -> 
  tempBuffer: lbuffer uint64 (size 4 *! getCoordinateLenU64 c) -> 
  Stack unit 
    (requires fun h0 -> 
      live h0 h /\ live h0 r /\ live h0 uh /\ live h0 hCube /\ live h0 u1 /\ 
      live h0 u2 /\ live h0 s1 /\ live h0 s2 /\ live h0 tempBuffer /\  
      LowStar.Monotonic.Buffer.all_disjoint [loc u1; loc u2; loc s1; loc s2; loc h; loc r; loc uh; loc hCube; loc tempBuffer] /\ 
      felem_eval c h0 u1 /\ 
      felem_eval c h0 u2 /\
      felem_eval c h0 s1 /\
      felem_eval c h0 s2)
    (ensures fun h0 _ h1 -> 
      modifies (loc h |+| loc r |+| loc uh |+| loc hCube |+| loc tempBuffer) h0 h1 /\ (
      let prime = getPrime c in 
      
      felem_eval c h1 h /\ 
      felem_eval c h1 r /\
      felem_eval c h1 uh /\
      felem_eval c h1 hCube /\ (
      
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


let _compute_common_params_point_add #c h r uh hCube u1 u2 s1 s2 tempBuffer =  
    let h0 = ST.get() in 
  [@inline_let]
  let len = getCoordinateLenU64 c in
  let temp = sub tempBuffer (size 0) len in 
  
  felem_sub u2 u1 h; 
  felem_sub s2 s1 r;    
  montgomery_square_buffer h temp;
  let h1 = ST.get() in   
  montgomery_multiplication_buffer temp u1 uh;
  montgomery_multiplication_buffer temp h hCube;

  let prime = getPrime c in 
  lemma_mod_mul_distr_l (fromDomain_ #c (as_nat c h1 h) * fromDomain_ #c (as_nat c h1 h)) (fromDomain_ #c (as_nat c h1 u1)) prime;
  lemma_mod_mul_distr_l (fromDomain_ #c (as_nat c h1 h) * fromDomain_ #c (as_nat c h1 h)) (fromDomain_ #c (as_nat c h1 h)) prime


val compute_common_params_point_add: #c: curve -> 
  tempBuffer22: lbuffer uint64 (size 22 *! getCoordinateLenU64 c) -> 
  Stack unit 
    (requires fun h0 ->
      let len = getCoordinateLenU64 c in 
    
      let u1 = gsub tempBuffer22 (size 4 *! len) len in 
      let u2 = gsub tempBuffer22 (size 5 *! len) len in 
      let s1 = gsub tempBuffer22 (size 6 *! len) len in 
      let s2 = gsub tempBuffer22 (size 7 *! len) len in 
      
      live h0 tempBuffer22 /\  
      felem_eval c h0 u1 /\ 
      felem_eval c h0 u2 /\
      felem_eval c h0 s1 /\
      felem_eval c h0 s2
    )
    (ensures fun h0 _ h1 -> 
      modifies (loc tempBuffer22) h0 h1 /\ (
      let prime = getPrime c in 
      let len = getCoordinateLenU64 c in 

      let u1 = gsub tempBuffer22 (size 4 *! len) len in 
      let u2 = gsub tempBuffer22 (size 5 *! len) len in 
      let s1 = gsub tempBuffer22 (size 6 *! len) len in 
      let s2 = gsub tempBuffer22 (size 7 *! len) len in 
  
      let h = gsub tempBuffer22 (size 8 *! len) len in 
      let r = gsub tempBuffer22 (size 9 *! len) len in 
      let uh = gsub tempBuffer22 (size 10 *! len) len in 

      let hCube = gsub tempBuffer22 (size 11 *! len) len in 

      
      felem_eval c h1 h /\ 
      felem_eval c h1 r /\
      felem_eval c h1 uh /\
      felem_eval c h1 hCube /\ (
      
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


let compute_common_params_point_add #c tempBuffer =
  let len = getCoordinateLenU64 c in

  let tempBuffer4 = sub tempBuffer (size 0) (size 4 *! len) in 

  let u1 = sub tempBuffer (size 4 *! len) len in 
  let u2 = sub tempBuffer (size 5 *! len) len in 
  let s1 = sub tempBuffer (size 6 *! len) len in 
  let s2 = sub tempBuffer (size 7 *! len) len in 

  let h = sub tempBuffer (size 8 *! len) len in 
  let r = sub tempBuffer (size 9 *! len) len in 
  let uh = sub tempBuffer (size 10 *! len) len in 

  let hCube = sub tempBuffer (size 11 *! len) len in 

  _compute_common_params_point_add #c h r uh hCube u1 u2 s1 s2 tempBuffer4



inline_for_extraction noextract
val _computeX3_point_add: #c : curve -> x3: felem c -> hCube: felem c -> uh: felem c -> 
  r: felem c -> tempBuffer: lbuffer uint64 (size 4 *! getCoordinateLenU64 c) ->  
  Stack unit 
  (requires fun h0 -> 
    let prime = getPrime c in  
    live h0 x3 /\ live h0 hCube /\ live h0 uh /\ live h0 r /\ live h0 tempBuffer /\
    disjoint hCube tempBuffer /\ disjoint uh tempBuffer /\ disjoint x3 tempBuffer /\
    felem_eval c h0 hCube /\ felem_eval c h0 uh /\ felem_eval c h0 r)
  (ensures fun h0 _ h1 -> 
    let prime = getPrime c in 
    modifies (loc x3 |+| loc tempBuffer) h0 h1 /\ 
    felem_eval c h1 x3 /\ 
    (
      let hCubeD = fromDomain_ #c (as_nat c h0 hCube) in 
      let uhD = fromDomain_ #c (as_nat c h0 uh) in 
      let rD = fromDomain_ #c (as_nat c h0 r) in 
      as_nat c h1 x3 == toDomain_ #c ((rD * rD - hCubeD - 2 * uhD) % prime)
    )  
  )

let _computeX3_point_add #c x3 hCube uh r tempBuffer = 
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


val computex3_point_add: #c : curve -> hCube: felem c -> uh: felem c -> 
  r: felem c -> tempBuffer7: lbuffer uint64 (size 7 *! getCoordinateLenU64 c) ->  
  Stack unit 
  (requires fun h0 -> 
    live h0 hCube /\ live h0 uh /\ live h0 r /\ live h0 tempBuffer7 /\
    disjoint hCube tempBuffer7 /\ disjoint uh tempBuffer7 /\
    felem_eval c h0 hCube /\ felem_eval c h0 uh /\ felem_eval c h0 r)
  (ensures fun h0 _ h1 -> 
    let prime = getPrime c in 
    let x3 = gsub tempBuffer7 (size 0) (getCoordinateLenU64 c) in 
    modifies (loc tempBuffer7) h0 h1 /\ felem_eval c h1 x3 /\ 
    (
      let hCubeD = fromDomain_ #c (as_nat c h0 hCube) in 
      let uhD = fromDomain_ #c (as_nat c h0 uh) in 
      let rD = fromDomain_ #c (as_nat c h0 r) in 
      as_nat c h1 x3 == toDomain_ #c ((rD * rD - hCubeD - 2 * uhD) % prime)
    )  
  )


let computex3_point_add #c hCube uh r tempBuffer7 = 
  let x3 = sub tempBuffer7 (size 0) (getCoordinateLenU64 c) in 
  let tempBuffer4 = sub tempBuffer7 (size 3 *! getCoordinateLenU64 c) (size 4 *! getCoordinateLenU64 c) in 
  _computeX3_point_add x3 hCube uh r tempBuffer4
  

inline_for_extraction noextract 
val _computeY3_point_add: #c: curve -> y3: felem c -> s1: felem c -> 
  hCube: felem c -> uh: felem c -> x3_out: felem c -> r: felem c -> 
  tempBuffer: lbuffer uint64 (size 4 *! getCoordinateLenU64 c) -> 
  Stack unit 
    (requires fun h -> 
      let prime = getPrime c in 
      live h y3 /\ live h s1 /\ live h hCube /\ live h uh /\ live h x3_out /\ 
      live h r /\ live h tempBuffer /\ 
      disjoint uh tempBuffer /\
      disjoint x3_out tempBuffer /\
      disjoint y3 tempBuffer /\
      disjoint r tempBuffer /\
      felem_eval c h s1 /\ 
      felem_eval c h hCube /\
      felem_eval c h uh/\ 
      felem_eval c h x3_out /\ 
      felem_eval c h r)
    (ensures fun h0 _ h1 -> 
      let prime = getPrime c in 
      modifies (loc y3 |+| loc tempBuffer) h0 h1 /\ felem_eval c h1 y3 /\ 
      (
	let s1D = fromDomain_ #c (as_nat c h0 s1) in 
	let hCubeD = fromDomain_ #c (as_nat c h0 hCube) in 
	let uhD = fromDomain_ #c (as_nat c h0 uh) in 
	let x3D = fromDomain_ #c (as_nat c h0 x3_out) in 
	let rD = fromDomain_ #c (as_nat c h0 r) in 
	as_nat c h1 y3 = toDomain_ #c (((uhD - x3D) * rD - s1D * hCubeD) % prime))
      )


let _computeY3_point_add #c y3 s1 hCube uh x3 r tempBuffer = 
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


val computeY3_point_add: #c: curve -> s1: felem c -> hCube: felem c -> uh: felem c -> r: felem c -> 
  tempBuffer7: lbuffer uint64 (size 7 *! getCoordinateLenU64 c) -> 
  Stack unit 
    (requires fun h -> 
      let prime = getPrime c in 
      let x3_out = gsub tempBuffer7 (size 0) (getCoordinateLenU64 c) in 
      live h s1 /\ live h hCube /\ live h uh /\ live h r /\ live h tempBuffer7 /\ 
      
      disjoint uh tempBuffer7 /\
      disjoint r tempBuffer7 /\
      
      felem_eval c h s1 /\ 
      felem_eval c h hCube /\
      felem_eval c h uh /\ 
      felem_eval c h x3_out /\ 
      felem_eval c h r)
    (ensures fun h0 _ h1 -> 
      let prime = getPrime c in 
      let x3_out = gsub tempBuffer7 (size 0) (getCoordinateLenU64 c) in 
      let y3_out = gsub tempBuffer7 (getCoordinateLenU64 c) (getCoordinateLenU64 c) in 
      modifies (loc tempBuffer7) h0 h1 /\ felem_eval c h1 y3_out /\ 
      as_nat c h0 x3_out == as_nat c h1 x3_out /\
      (
	let s1D = fromDomain_ #c (as_nat c h0 s1) in 
	let hCubeD = fromDomain_ #c (as_nat c h0 hCube) in 
	let uhD = fromDomain_ #c (as_nat c h0 uh) in 
	let x3D = fromDomain_ #c (as_nat c h0 x3_out) in 
	let rD = fromDomain_ #c (as_nat c h0 r) in 
	as_nat c h1 y3_out = toDomain_ #c (((uhD - x3D) * rD - s1D * hCubeD) % prime))
      )


let computeY3_point_add #c s1 hCube uh r tempBuffer7 = 
  let x3 = sub tempBuffer7 (size 0) (getCoordinateLenU64 c) in 
  let y3 = sub tempBuffer7 (getCoordinateLenU64 c) (getCoordinateLenU64 c) in 
  let tempBuffer4 = sub tempBuffer7 (size 3 *! getCoordinateLenU64 c) (size 4 *! getCoordinateLenU64 c) in 
  _computeY3_point_add #c y3 s1 hCube uh x3 r tempBuffer4


inline_for_extraction noextract 
val __computeZ3_point_add: #c: curve -> z3: felem  c ->  z1: felem c -> z2: felem c ->
  h: felem c -> tempBuffer: lbuffer uint64 (size 4 *! getCoordinateLenU64 c) -> 
  Stack unit (requires fun h0 -> 
    live h0 z3 /\ live h0 z1 /\ live h0 z2 /\ live h0 h /\ 
    live h0 tempBuffer /\ live h0 z3 /\
    disjoint tempBuffer h /\ 
    felem_eval c h0 z1 /\ felem_eval c h0 z2 /\ felem_eval c h0 h)
  (ensures fun h0 _ h1 ->
    let prime = getPrime c in 
    modifies (loc z3 |+| loc tempBuffer) h0 h1 /\ 
    felem_eval c h1 z3 /\ 
    (
      let z1D = fromDomain_ #c (as_nat c h0 z1) in 
      let z2D = fromDomain_ #c (as_nat c h0 z2) in 
      let hD = fromDomain_ #c (as_nat c h0 h) in 
      as_nat c h1 z3 == toDomain_ #c (z1D * z2D * hD % prime)
    )  
  )  


let __computeZ3_point_add #c z3 z1 z2 h tempBuffer = 
    let h0 = ST.get() in 
  let z1z2 = sub tempBuffer (size 0) (getCoordinateLenU64 c) in
  montgomery_multiplication_buffer z1 z2 z1z2;
  montgomery_multiplication_buffer z1z2 h z3;
    lemma_mod_mul_distr_l (fromDomain_ #c (as_nat c h0 z1) * fromDomain_ #c (as_nat c h0 z2)) (fromDomain_ #c (as_nat c h0 h)) (getPrime c)


inline_for_extraction noextract 
val _computeZ3_point_add: #c: curve -> z1: felem c -> z2: felem c ->
  h: felem c -> tempBuffer7: lbuffer uint64 (size 7 *! getCoordinateLenU64 c) -> 
  Stack unit (requires fun h0 -> 
    live h0 z1 /\ live h0 z2 /\ live h0 h /\ 
    live h0 tempBuffer7 /\ 
    disjoint tempBuffer7 h /\ 
    felem_eval c h0 z1 /\ felem_eval c h0 z2 /\ felem_eval c h0 h)
  (ensures fun h0 _ h1 ->
    let prime = getPrime c in 

    let x3_out, y3_out, z3_out = getTempXYZ tempBuffer7 in
    
    as_nat c h0 x3_out == as_nat c h1 x3_out /\
    as_nat c h0 y3_out == as_nat c h1 y3_out /\
    modifies (loc tempBuffer7) h0 h1 /\ 
    felem_eval c h1 z3_out /\ 
    (
      let z1D = fromDomain_ #c (as_nat c h0 z1) in 
      let z2D = fromDomain_ #c (as_nat c h0 z2) in 
      let hD = fromDomain_ #c (as_nat c h0 h) in 
      as_nat c h1 z3_out == toDomain_ #c (z1D * z2D * hD % prime)
    )  
  )  


let _computeZ3_point_add #c z1 z2 h tempBuffer7 = 
  let len = getCoordinateLenU64 c in 
  assert(v (size 2 *! len) + v len <= v (size 7 *! len));
  let z3 = sub tempBuffer7 (size 2 *! len) len in 
  let tempBuffer4 = sub tempBuffer7 (size 3 *! len) (size 4 *! len) in 
  __computeZ3_point_add z3 z1 z2 h tempBuffer4


inline_for_extraction noextract 
val computeZ3_point_add: #c: curve -> p: point c -> q: point c ->
  h: felem c -> tempBuffer7: lbuffer uint64 (size 7 *! getCoordinateLenU64 c) -> 
  Stack unit (requires fun h0 -> 
    live h0 p /\ live h0 q /\ live h0 h /\ 
    live h0 tempBuffer7 /\ 
    disjoint tempBuffer7 h /\ 
    point_eval c h0 p /\ point_eval c h0 q /\ felem_eval c h0 h)
  (ensures fun h0 _ h1 ->
    let prime = getPrime c in 
    let len = getCoordinateLenU64 c in 

    let x3_out, y3_out, z3_out = getTempXYZ #c tempBuffer7 in 
    
    as_nat c h0 x3_out == as_nat c h1 x3_out /\
    as_nat c h0 y3_out == as_nat c h1 y3_out /\
   
    modifies (loc tempBuffer7) h0 h1 /\ 
 
    felem_eval c h1 z3_out  /\
    (
      let z1D = fromDomain_ #c (point_z_as_nat c h0 p) in 
      let z2D = fromDomain_ #c (point_z_as_nat c h0 q) in 
      let hD = fromDomain_ #c (as_nat c h0 h) in 
      as_nat c h1 z3_out == toDomain_ #c (z1D * z2D * hD % prime) 
    ))  
    


let computeZ3_point_add #c p q h tempBuffer7 = 
  let len = getCoordinateLenU64 c in 

  let z1 : felem c = sub p (size 2 *! len) len in 
  let z2 : felem c = sub q (size 2 *! len) len in 

  _computeZ3_point_add #c z1 z2 h tempBuffer7


val copy_result_point_add: #c: curve 
  -> tempBuffer7: lbuffer uint64 (size 7 *! (getCoordinateLenU64 c)) 
  -> p: point c -> q: point c -> result: point c ->
  Stack unit 
    (requires fun h -> live h tempBuffer7 /\ live h p /\ live h q /\ live h result /\
      eq_or_disjoint p result /\
      disjoint tempBuffer7 result /\
      LowStar.Monotonic.Buffer.all_disjoint [loc tempBuffer7; loc p; loc q]
    )
    (ensures fun h0 _ h1 -> 
      let x3_out, y3_out, z3_out = getTempXYZ #c tempBuffer7 in 
      
      modifies (loc tempBuffer7 |+| loc result) h0 h1 /\ (
      if point_z_as_nat c h0 q = 0 then 
	point_x_as_nat c h1 result == point_x_as_nat c h0 p /\
	point_y_as_nat c h1 result == point_y_as_nat c h0 p /\ 
	point_z_as_nat c h1 result == point_z_as_nat c h0 p
      else if point_z_as_nat c h0 p = 0 then 
	point_x_as_nat c h1 result == point_x_as_nat c h0 q /\
	point_y_as_nat c h1 result == point_y_as_nat c h0 q /\ 
	point_z_as_nat c h1 result == point_z_as_nat c h0 q
      else 
	point_x_as_nat c h1 result == as_nat c h0 x3_out /\ 
	point_y_as_nat c h1 result == as_nat c h0 y3_out /\ 
	point_z_as_nat c h1 result == as_nat c h0 z3_out )
    )


let copy_result_point_add #c tempBuffer7 p q result = 
  let h0 = ST.get() in 
  let len = getCoordinateLenU64 c in 

  let x3_out = sub tempBuffer7 (size 0) (getCoordinateLenU64 c) in 
  let y3_out = sub tempBuffer7 ((getCoordinateLenU64 c)) (getCoordinateLenU64 c) in 
  let z3_out = sub tempBuffer7 (size 2 *!  (getCoordinateLenU64 c)) (getCoordinateLenU64 c) in 
    
  copy_point_conditional x3_out y3_out z3_out q p;
  copy_point_conditional x3_out y3_out z3_out p q;
  concat3 len x3_out len y3_out len z3_out result


val computeXY: #c: curve -> hCube: felem c -> uh: felem c 
  -> r: felem c -> tempBuffer7: lbuffer uint64 (size 7 *! getCoordinateLenU64 c) 
  -> s1: felem c -> h: felem c ->
  Stack unit 
    (requires fun h0 -> 
      live h0 hCube /\ live h0 uh /\ live h0 r /\  live h0 tempBuffer7 /\ live h0 s1 /\ live h0 h /\
      felem_eval c h0 hCube /\ felem_eval c h0 uh /\ felem_eval c h0 r /\
      felem_eval c h0 s1 /\ felem_eval c h0 h /\
      
      disjoint hCube tempBuffer7 /\ disjoint uh tempBuffer7 /\ 
      disjoint r tempBuffer7 /\ disjoint tempBuffer7 s1 
      )
    (ensures fun h0 _ h1 -> modifies (loc tempBuffer7) h0 h1 /\ (
      let prime = getPrime c in 
      
      let x3_out, y3_out, _ = getTempXYZ #c tempBuffer7 in 

      felem_eval c h1 x3_out /\
      felem_eval c h1 y3_out /\ 
      
      (
	let s1D = fromDomain_ #c (as_nat c h0 s1) in 
	let rD = fromDomain_ #c (as_nat c h0 r) in 
	let hCubeD = fromDomain_ #c (as_nat c h0 hCube) in 
	let uhD = fromDomain_ #c (as_nat c h0 uh) in 
	let rD = fromDomain_ #c (as_nat c h0 r) in 
	let x3D = fromDomain_ #c (as_nat c h1 x3_out) in
	
	as_nat c h1 x3_out == toDomain_ #c ((rD * rD - hCubeD - 2 * uhD) % prime) /\
	as_nat c h1 y3_out == toDomain_ #c (((uhD - x3D) * rD - s1D * hCubeD) % prime))))


let computeXY #c hCube uh r tempBuffer7 s1 h = 
  computex3_point_add #c hCube uh r tempBuffer7; 
  computeY3_point_add #c s1 hCube uh r tempBuffer7


val computeXYZ: #c: curve -> p: point c -> q: point c -> hCube: felem c -> uh: felem c 
  -> r: felem c -> tempBuffer7: lbuffer uint64 (size 7 *! getCoordinateLenU64 c) 
  -> s1: felem c -> h: felem c ->
  Stack unit 
    (requires fun h0 -> 
      felem_eval c h0 hCube /\ felem_eval c h0 uh /\ felem_eval c h0 r /\
      felem_eval c h0 s1 /\ felem_eval c h0 h /\ 
      
       point_eval c h0 q /\  point_eval c h0 p /\
      
      live h0 p /\ live h0 q /\ live h0 hCube /\ live h0 uh /\ live h0 r /\ 
      live h0 tempBuffer7 /\ live h0 s1 /\ live h0 h /\
      
      disjoint hCube tempBuffer7 /\ disjoint uh tempBuffer7 /\ 
      disjoint r tempBuffer7 /\ disjoint tempBuffer7 s1 /\
      disjoint tempBuffer7 h /\  
      disjoint tempBuffer7 p /\ disjoint tempBuffer7 q
    )
    (ensures fun h0 _ h1 -> modifies (loc tempBuffer7) h0 h1 /\
      (
	let prime = getPrime c in 
	let len = (getCoordinateLenU64 c) in 

	let x3_out, y3_out, z3_out = getTempXYZ tempBuffer7 in
	
	felem_eval c h1 x3_out /\
	felem_eval c h1 y3_out /\ 
      
	(
	  let s1D = fromDomain_ #c (as_nat c h0 s1) in 
	  let rD = fromDomain_ #c (as_nat c h0 r) in 
	  let hCubeD = fromDomain_ #c (as_nat c h0 hCube) in 
	  let uhD = fromDomain_ #c (as_nat c h0 uh) in 
	  let rD = fromDomain_ #c (as_nat c h0 r) in 
	  let x3D = fromDomain_ #c (as_nat c h1 x3_out) in

	  let z1D = fromDomain_ #c (point_z_as_nat c h0 p) in 
	  let z2D = fromDomain_ #c (point_z_as_nat c h0 q) in 
	  let hD = fromDomain_ #c (as_nat c h0 h) in 
	
	  as_nat c h1 x3_out == toDomain_ #c ((rD * rD - hCubeD - 2 * uhD) % prime) /\
	  as_nat c h1 y3_out == toDomain_ #c (((uhD - x3D) * rD - s1D * hCubeD) % prime) /\
	  as_nat c h1 z3_out == toDomain_ #c (z1D * z2D * hD % prime)
    ))
)

val lemma_point_eval: c: curve -> h0: mem -> h1: mem -> p: point c -> Lemma
  (requires (as_seq h0 p == as_seq h1 p))
  (ensures (point_eval c h1 p))

let lemma_point_eval c h0 h1 p = ()

val lemma_coord_eval: c: curve -> h0: mem -> h1 : mem -> p: point c -> 
  Lemma 
    (requires (as_seq h1 p == as_seq h0 p))
    (ensures (as_nat c h1 (getPointZ p) == as_nat c h0 (getPointZ p)))

let lemma_coord_eval c h0 h1 p = 
  let len = getCoordinateLenU64 c in 
  let f = gsub p (size 2 *! len) len in 
  assert(as_nat c h0 f == as_nat c h1 f)

let computeXYZ #c p q hCube uh r tempBuffer7 s1 h = 
    let h0 = ST.get() in 
    computeXY #c hCube uh r tempBuffer7 s1 h;  
    let h1 = ST.get() in 
    lemma_point_eval c h0 h1 p; 
    lemma_point_eval c h0 h1 q;
  computeZ3_point_add #c p q h tempBuffer7;
  lemma_coord_eval c h0 h1 p;
  lemma_coord_eval c h0 h1 q


val point_add_if_second_branch_impl: #c: curve -> result: point c -> p: point c -> 
  q: point c -> u1: felem c -> u2: felem c -> s1: felem c -> 
  s2: felem c -> r: felem c -> h: felem c -> uh: felem c -> hCube: felem c -> 
  tempBuffer7 : lbuffer uint64 (size 7 *! getCoordinateLenU64 c) -> 
  Stack unit (requires fun h0 -> 
    let prime = getPrime c in 

    live h0 result /\ live h0 p /\ live h0 q /\ live h0 u1 /\ live h0 u2 /\ live h0 s1 /\ 
    live h0 s2 /\ live h0 r /\ live h0 h /\ live h0 uh /\ live h0 hCube /\ live h0 tempBuffer7 /\

    felem_eval c h0 u1 /\ felem_eval c h0 u2 /\ felem_eval c h0 s1 /\
    felem_eval c h0 s2 /\ felem_eval c h0 h /\ felem_eval c h0 uh /\ 
    felem_eval c h0 r /\ felem_eval c h0 hCube /\
    point_eval c h0 p /\ point_eval c h0 q /\ 
   
    eq_or_disjoint p result /\ disjoint result tempBuffer7 /\ disjoint p q /\

    disjoint hCube tempBuffer7 /\ disjoint uh tempBuffer7 /\ disjoint r tempBuffer7 /\ disjoint tempBuffer7 s1 /\ disjoint tempBuffer7 h /\ disjoint tempBuffer7 p /\ disjoint tempBuffer7 q /\
    (
      let pX, pY, pZ = point_x_as_nat c h0 p, point_y_as_nat c h0 p, point_z_as_nat c h0 p in 
      let qX, qY, qZ = point_x_as_nat c h0 q, point_y_as_nat c h0 q, point_z_as_nat c h0 q in 
      let pxD, pyD, pzD = fromDomain_ #c pX, fromDomain_ #c pY, fromDomain_ #c pZ in 
      let qxD, qyD, qzD = fromDomain_ #c qX, fromDomain_ #c qY, fromDomain_ #c qZ in 

      let u1D = fromDomain_ #c (as_nat c h0 u1) in 
      let u2D = fromDomain_ #c (as_nat c h0 u2) in 
      let s1D = fromDomain_ #c (as_nat c h0 s1) in 
      let s2D = fromDomain_ #c (as_nat c h0 s2) in 
      let hD = fromDomain_ #c (as_nat c h0 h) in 
	
    as_nat c h0 u1 == toDomain_ #c (qzD * qzD * pxD % prime) /\
    as_nat c h0 u2 == toDomain_ #c (pzD * pzD * qxD % prime) /\
    as_nat c h0 s1 == toDomain_ #c (qzD * qzD * qzD * pyD % prime) /\
    as_nat c h0 s2 == toDomain_ #c (pzD * pzD * pzD * qyD % prime) /\
      
    as_nat c h0 h == toDomain_ #c ((u2D - u1D) % prime) /\
    as_nat c h0 r == toDomain_ #c ((s2D - s1D) % prime) /\
    as_nat c h0 uh == toDomain_ #c (hD * hD * u1D % prime) /\
    as_nat c h0 hCube == toDomain_ #c (hD * hD * hD % prime))
  )
  (ensures fun h0 _ h1 -> modifies (loc tempBuffer7 |+| loc result) h0 h1 /\ (
    let prime = getPrime c in 
    
    let x3, y3, z3 = point_x_as_nat c h1 result, point_y_as_nat c h1 result, point_z_as_nat c h1 result in
    let pX, pY, pZ = point_x_as_nat c h0 p, point_y_as_nat c h0 p, point_z_as_nat c h0 p in 
    let qX, qY, qZ = point_x_as_nat c h0 q, point_y_as_nat c h0 q, point_z_as_nat c h0 q in 

    let pxD, pyD, pzD = fromDomain_ #c pX, fromDomain_ #c pY, fromDomain_ #c pZ in 
    let qxD, qyD, qzD = fromDomain_ #c qX, fromDomain_ #c qY, fromDomain_ #c qZ in 
    let x3D, y3D, z3D = fromDomain_ #c x3, fromDomain_ #c y3, fromDomain_ #c z3 in 

    let rD = fromDomain_ #c (as_nat c h0 r) in 
    let hD = fromDomain_ #c (as_nat c h0 h) in 
    let s1D = fromDomain_ #c (as_nat c h0 s1) in 
    let u1D = fromDomain_ #c (as_nat c h0 u1) in 
    
    point_eval c h1 result /\ (
    if qzD = 0 then 
      x3D == pxD /\ y3D == pyD /\ z3D == pzD
    else if pzD = 0 then 
      x3D == qxD /\  y3D == qyD /\ z3D == qzD
    else 
      x3 == toDomain_ #c ((rD * rD - hD * hD * hD - 2 * hD * hD * u1D) % prime) /\ 
      y3 == toDomain_ #c (((hD * hD * u1D - fromDomain_  #c x3) * rD - s1D * hD * hD * hD) % prime) /\
      z3 == toDomain_ #c (pzD * qzD * hD % prime)))
  )

val point_x_modifies_lemma: c: curve -> h0: mem -> h1 : mem -> q: point c -> 
  Lemma (requires (as_seq h0 q == as_seq h1 q))
  (ensures (point_x_as_nat c h0 q == point_x_as_nat c h1 q))

let point_x_modifies_lemma c h0 h1 q = ()

val point_y_modifies_lemma: c: curve -> h0: mem -> h1 : mem -> q: point c -> 
  Lemma (requires (as_seq h0 q == as_seq h1 q))
  (ensures (point_y_as_nat c h0 q == point_y_as_nat c h1 q))

let point_y_modifies_lemma c h0 h1 q = ()

val point_z_modifies_lemma: c: curve -> h0: mem -> h1 : mem -> q: point c -> 
  Lemma (requires (as_seq h0 q == as_seq h1 q))
  (ensures (point_z_as_nat c h0 q == point_z_as_nat c h1 q))

let point_z_modifies_lemma c h0 h1 q = ()


let point_add_if_second_branch_impl #c result p q u1 u2 s1 s2 r h uh hCube tempBuffer7 = 
  let h0 = ST.get() in
    computeXYZ #c p q hCube uh r tempBuffer7 s1 h;
  let h1 = ST.get() in 
    copy_result_point_add tempBuffer7 p q result;
  let h2 = ST.get() in 
  
  let prime = getPrime c in 
  
  let x3_out, y3_out, z3_out = getTempXYZ tempBuffer7 in
  point_x_modifies_lemma c h0 h1 p;
  point_x_modifies_lemma c h0 h1 q;

  point_y_modifies_lemma c h0 h1 p;
  point_y_modifies_lemma c h0 h1 q;

  point_z_modifies_lemma c h0 h1 p;
  point_z_modifies_lemma c h0 h1 q;
  
  let rD = fromDomain_ #c (as_nat c h0 r) in 
  let hD = fromDomain_ #c (as_nat c h0 h) in 
  let u1D = fromDomain_ #c (as_nat c h0 u1) in 
  let s1D = fromDomain_ #c (as_nat c h0 s1) in 
  let x3D = fromDomain_ #c (as_nat c h1 x3_out) in

  calc (==)
  {
    (rD * rD - (hD * hD * hD % prime) - 2 * (hD * hD * u1D % prime)) % prime;
    (==) {lemma_mod_sub_distr (rD * rD - (hD * hD * hD % prime)) (2 * (hD * hD * u1D % prime)) prime}
    (rD * rD - (hD * hD * hD % prime) - 2 * (hD * hD * u1D % prime) % prime) % prime;
    (==) {lemma_mod_mul_distr_r 2 (hD * hD * u1D) prime}
    (rD * rD - (hD * hD * hD % prime) - 2 * (hD * hD * u1D) % prime) % prime;
    (==) {_ by (canon())}
    (rD * rD - (hD * hD * hD % prime) - 2 * hD * hD * u1D % prime) % prime;
    (==) {lemma_mod_sub_distr (rD * rD - (hD * hD * hD % prime)) (2 * hD * hD * u1D) prime}
    (rD * rD - (hD * hD * hD % prime) - 2 * hD * hD * u1D) % prime;
    (==) {_ by (canon())}
    (rD * rD  - 2 * hD * hD * u1D - (hD * hD * hD % prime)) % prime;
    (==) {lemma_mod_sub_distr (rD * rD -  2 * hD * hD * u1D) (hD * hD * hD) prime}
    (rD * rD  - 2 * hD * hD * u1D - hD * hD * hD) % prime;
    (==) {_ by (canon())}
    (rD * rD - hD * hD * hD - 2 * hD * hD * u1D) % prime;
  };

  let rh = s1D * hD * hD * hD in
  let lh = hD * hD * u1D in 


  calc (==)
  {
    (((hD * hD * u1D % prime) - x3D) * rD - s1D * (hD * hD * hD % prime)) % prime;
    (==) {lemma_mod_sub_distr (((hD * hD * u1D % prime) - x3D) * rD) (s1D * (hD * hD * hD % prime)) prime}
    (((hD * hD * u1D % prime) - x3D) * rD - s1D * (hD * hD * hD % prime) % prime) % prime;
    (==) {lemma_mod_mul_distr_r s1D (hD * hD * hD) prime}
    (((hD * hD * u1D % prime) - x3D) * rD - s1D * (hD * hD * hD) % prime) % prime;
    (==) {_ by (canon()) }
    (((hD * hD * u1D % prime) - x3D) * rD - s1D * hD * hD * hD % prime) % prime;
    (==) {lemma_mod_sub_distr (((hD * hD * u1D % prime) - x3D) * rD) (s1D * hD * hD * hD) prime}
    ((((lh % prime) - x3D) * rD) - rh) % prime;
    (==) {_ by (canon())}
    (-rh + (((lh % prime) - x3D) * rD)) % prime;
    (==) {lemma_mod_add_distr (-rh) (((lh % prime) - x3D) * rD) prime}
    (-rh + (((lh % prime) - x3D) * rD) % prime) % prime;
    (==) {lemma_mod_mul_distr_l ((lh % prime) - x3D) rD prime}
    (-rh + (((lh % prime) - x3D) % prime * rD) % prime) % prime;
    (==) {_ by (canon())} 
    (-rh + ((-x3D + (lh % prime)) % prime * rD) % prime) % prime;
    (==) {lemma_mod_add_distr (-x3D) lh prime}
    (-rh + ((-x3D + lh) % prime * rD) % prime) % prime;
    (==) {lemma_mod_mul_distr_l (-x3D + lh) rD prime}
    (-rh + ((-x3D + lh) * rD) % prime) % prime;
    (==) {_ by (canon())}
    (-rh + ((lh - x3D) * rD) % prime) % prime;
    (==) {lemma_mod_add_distr (-rh) ((lh - x3D) * rD) prime}
    (-rh + (lh - x3D) * rD) % prime;
    (==) {_ by (canon())}
    ((lh - x3D) * rD - rh) % prime;
    (==) {}
    ((hD * hD * u1D - x3D) * rD - s1D * hD * hD * hD) % prime;};

  lemma_multiplication_not_mod_prime #c (point_z_as_nat c h0 q);
  lemma_multiplication_not_mod_prime #c (point_z_as_nat c h0 p);

  assert(point_z_as_nat c h0 q = 0 <==> fromDomain_ #c (point_z_as_nat c h0 q) = 0);
  assert(point_z_as_nat c h0 p = 0 <==> fromDomain_ #c (point_z_as_nat c h0 p) = 0)


let point_add #c p q result tempBuffer = 
  admit();
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
  
  move_from_jacobian_coordinates p q tempBuffer28;
  compute_common_params_point_add #c tempBuffer28;
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

