module Hacl.Impl.P256.PointAdd

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Hacl.Impl.EC.Arithmetics

open Lib.Buffer

open Hacl.Impl.EC.LowLevel
open Hacl.Impl.EC.MontgomeryMultiplication
open Spec.P256

open FStar.Tactics 
open FStar.Tactics.Canon

open FStar.Math.Lemmas
open  Hacl.Spec.P256.Definition


open Hacl.Spec.P.MontgomeryMultiplication
open FStar.Mul

open Hacl.Impl.P.PointAdd.Aux


#set-options "--z3rlimit 300 --ifuel 0 --fuel 0"  

val copy_point_conditional: #c: curve -> x3_out: felem c -> y3_out: felem c -> z3_out: felem c -> p: point c -> mask: point c ->
  Stack unit
  (requires fun h -> 
    live h x3_out /\ live h y3_out /\ live h z3_out /\ live h p /\ live h mask /\ 
    LowStar.Monotonic.Buffer.all_disjoint [loc x3_out; loc y3_out; loc z3_out; loc p; loc mask])
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
  [@inline_let]
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
    live h u1 /\ live h u2 /\ live h s1 /\ live h s2 /\ live h tempBuffer4 /\ live h p /\ live h q /\
    LowStar.Monotonic.Buffer.all_disjoint [loc tempBuffer4; loc p; loc q; loc u1; loc u2; loc s1; loc s2] /\ 
    point_eval c h p /\ point_eval c h q)
  (ensures fun h0 _ h1 ->  
    modifies (loc u1 |+| loc u2 |+| loc s1 |+| loc s2 |+| loc tempBuffer4) h0 h1 /\
    u1Invariant #c h0 h1 u1 p q /\
    u2Invariant #c h0 h1 u2 p q /\ 
    s1Invariant #c h0 h1 s1 p q /\
    s2Invariant #c h0 h1 s2 p q)


let _move_from_jacobian_coordinates #c u1 u2 s1 s2 p q tempBuffer = 
  let h0 = ST.get() in 
  
  [@inline_let]
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

  let h0 = ST.get() in 

  montgomery_square_buffer #c qZ z2Square; 
  montgomery_square_buffer #c pZ z1Square;

  montgomery_multiplication_buffer #c z2Square qZ z2Cube;
  montgomery_multiplication_buffer #c z1Square pZ z1Cube;

  montgomery_multiplication_buffer #c z2Square pX u1;
  montgomery_multiplication_buffer #c z1Square qX u2;
    
  montgomery_multiplication_buffer #c z2Cube pY s1;
  montgomery_multiplication_buffer #c z1Cube qY s2;

  let prime = getPrime c in 
  
  let fromDomain = fromDomain_ #c in 
  let toDomain = toDomain_ #c in 
  
  let as_nat = as_nat c in 


  let pxD = fromDomain (as_nat h0 pX) in 
  let qxD = fromDomain (as_nat h0 qX) in 

  let pyD = fromDomain (as_nat h0 pY) in 
  let qyD = fromDomain (as_nat h0 qY) in 

  let pzD = fromDomain_ #c (as_nat h0 pZ) in 
  let qzD = fromDomain_ #c (as_nat h0 qZ) in 


  calc (==)
  {
    toDomain ((qzD * qzD % prime) * pxD % prime);
    (==) {lemma_mod_mul_distr_l (qzD * qzD) pxD prime}
    toDomain (qzD * qzD * pxD % prime);
  };  
    

  calc (==)
  {
    toDomain ((pzD * pzD % prime) * qxD % prime);
    (==) {lemma_mod_mul_distr_l (pzD * pzD) qxD prime}
    toDomain (pzD * pzD * qxD % prime);
  };


  calc (==)
  {
    toDomain (((qzD * qzD % prime) * qzD % prime) * pyD % prime);
    (==) {lemma_mod_mul_distr_l (qzD * qzD) qzD prime}
    toDomain ((qzD * qzD * qzD % prime) * pyD % prime);
    (==) {lemma_mod_mul_distr_l (qzD * qzD * qzD) pyD prime}
    toDomain (qzD * qzD * qzD * pyD % prime);
  };

  calc (==) 
  {
    toDomain (((pzD * pzD % prime) * pzD % prime) * qyD % prime);
    (==) {lemma_mod_mul_distr_l (pzD * pzD) pzD prime}
    toDomain(((pzD * pzD) * pzD % prime) * qyD % prime);
    (==) {lemma_mod_mul_distr_l (pzD * pzD * pzD) qyD prime}
    toDomain(pzD * pzD * pzD * qyD % prime);
  }


inline_for_extraction noextract 
val move_from_jacobian_coordinates: #c: curve -> p: point c -> q: point c -> 
  t12: lbuffer uint64 (size 12 *! getCoordinateLenU64 c) -> 
  Stack unit (requires fun h -> 
    live h t12 /\ live h p /\ live h q /\
    LowStar.Monotonic.Buffer.all_disjoint [loc t12; loc p; loc q] /\ 
    point_eval c h p /\ point_eval c h q)
  (ensures fun h0 _ h1 -> 
    let u1, u2, s1, s2, _, _, _, _ = getU1HCube t12 in 
    modifies (loc t12) h0 h1 /\ (
    u1Invariant #c h0 h1 u1 p q /\
    u2Invariant #c h0 h1 u2 p q /\ 
    s1Invariant #c h0 h1 s1 p q /\
    s2Invariant #c h0 h1 s2 p q))


let move_from_jacobian_coordinates #c p q t12 = 
  [@inline_let]
  let len = getCoordinateLenU64 c in   
  
  let t4 = sub t12 (size 0) (size 4 *! len) in 
   
  let u1 = sub t12 (size 4 *! len) len in 
  let u2 = sub t12 (size 5 *! len) len in 
  let s1 = sub t12 (size 6 *! len) len in 
  let s2 = sub t12 (size 7 *! len) len in 

  _move_from_jacobian_coordinates #c u1 u2 s1 s2 p q t4



inline_for_extraction noextract 
val _compute_common_params_point_add: #c: curve -> h: felem c -> r: felem c -> uh: felem c -> 
  hCube: felem c -> u1: felem c -> u2: felem c -> s1: felem c -> s2: felem c -> 
  t4: lbuffer uint64 (size 4 *! getCoordinateLenU64 c) -> 
  Stack unit (requires fun h0 -> 
    live h0 h /\ live h0 r /\ live h0 uh /\ live h0 hCube /\ live h0 t4 /\ 
    live h0 u1 /\ live h0 u2 /\ live h0 s1 /\ live h0 s2 /\
    LowStar.Monotonic.Buffer.all_disjoint [loc u1; loc u2; loc s1; loc s2; loc h; loc r; loc uh; loc hCube; loc t4] /\ 
    felem_eval c h0 u1 /\ felem_eval c h0 u2 /\ felem_eval c h0 s1 /\ felem_eval c h0 s2)
  (ensures fun h0 _ h1 -> 
    modifies (loc h |+| loc r |+| loc uh |+| loc hCube |+| loc t4) h0 h1 /\
    hInvariant #c h1 h u1 u2 /\
    rInvariant #c h1 r s1 s2 /\
    uhInvariant #c h1 uh h u1 /\
    hCubeInvariant #c h1 hCube h
  )


let _compute_common_params_point_add #c h r uh hCube u1 u2 s1 s2 t4 =  
  [@inline_let]
  let len = getCoordinateLenU64 c in
  let temp = sub t4 (size 0) len in 
  
  felem_sub u2 u1 h; 
  felem_sub s2 s1 r;    
  montgomery_square_buffer h temp;
    let h1 = ST.get() in   
  montgomery_multiplication_buffer temp u1 uh;
  montgomery_multiplication_buffer temp h hCube;

  let prime = getPrime c in 
  lemma_mod_mul_distr_l (fromDomain_ #c (as_nat c h1 h) * fromDomain_ #c (as_nat c h1 h)) (fromDomain_ #c (as_nat c h1 u1)) prime;
  lemma_mod_mul_distr_l (fromDomain_ #c (as_nat c h1 h) * fromDomain_ #c (as_nat c h1 h)) (fromDomain_ #c (as_nat c h1 h)) prime


val compute_common_params_point_add: #c: curve -> t12: lbuffer uint64 (size 12 *! getCoordinateLenU64 c) -> 
  Stack unit 
  (requires fun h0 ->
    live h0 t12 /\ (
    let u1, u2, s1, s2, _, _, _, _ = getU1HCube t12 in  
    felem_eval c h0 u1 /\ felem_eval c h0 u2 /\ felem_eval c h0 s1 /\ felem_eval c h0 s2))
    (ensures fun h0 _ h1 -> 
      let  u1, u2, s1, s2, h, r, uh, hCube = getU1HCube t12 in 

      modifies (loc t12) h0 h1 /\
      as_nat c h0 u1 == as_nat c h1 u1 /\
      as_nat c h0 u2 == as_nat c h1 u2 /\
      as_nat c h0 s1 == as_nat c h1 s1 /\
      as_nat c h0 s2 == as_nat c h1 s2 /\

      hInvariant #c h1 h u1 u2 /\
      rInvariant #c h1 r s1 s2 /\
      uhInvariant #c h1 uh h u1 /\
      hCubeInvariant #c h1 hCube h)


let compute_common_params_point_add #c t12 =
  [@inline_let]
  let len = getCoordinateLenU64 c in
  lemma_ICuttable_common #c;

  let t4 = sub t12 (size 0) (size 4 *! len) in 

  let u1 = sub t12 (size 4 *! len) len in 
  let u2 = sub t12 (size 5 *! len) len in 
  let s1 = sub t12 (size 6 *! len) len in 
  let s2 = sub t12 (size 7 *! len) len in

  let h = sub t12 (size 8 *! len) len in 
  let r = sub t12 (size 9 *! len) len in 
  let uh = sub t12 (size 10 *! len) len in
  let hCube = sub t12 (size 11 *! len) len in 

  _compute_common_params_point_add #c h r uh hCube u1 u2 s1 s2 t4


inline_for_extraction noextract
val _computeX3_point_add: #c : curve -> x3: felem c -> hCube: felem c -> uh: felem c -> 
  r: felem c -> t3: lbuffer uint64 (size 3 *! getCoordinateLenU64 c) ->  
  Stack unit 
  (requires fun h0 -> 
    live h0 x3 /\ live h0 hCube /\ live h0 uh /\ live h0 r /\ live h0 r /\ live h0 t3 /\
    
    disjoint hCube t3 /\  disjoint uh t3 /\  disjoint x3 t3 /\ disjoint r t3 /\ 
    disjoint x3 r /\ disjoint x3 hCube /\ disjoint x3 uh /\
    
    felem_eval c h0 hCube /\ felem_eval c h0 uh /\ felem_eval c h0 r)
  (ensures fun h0 _ h1 -> 
    modifies (loc x3 |+| loc t3) h0 h1 /\ x3Invariant #c h0 h1 x3 r hCube uh)


let _computeX3_point_add #c x3 hCube uh r t3 = 
  let h0 = ST.get() in
  [@inline_let]
  let len = getCoordinateLenU64 c in 
  
  let rSquare = sub t3 (size 0) len in 
  let rH = sub t3 len len in 
  let twoUh = sub t3 (size 2 *! len) len in 
  
  montgomery_square_buffer r rSquare; 
  felem_sub rSquare hCube rH;
  multByTwo uh twoUh;
  felem_sub rH twoUh x3; 

  let prime = getPrime c in 
  let r = as_nat c h0 r in 

  let as_nat = as_nat c in 
  let toDomain = toDomain_ #c in 
  let fromDomain = fromDomain_ #c in 
  
  calc (==)
  {
    toDomain (((((fromDomain r * fromDomain r  % prime) - fromDomain (as_nat h0 hCube)) % prime) - (2 * fromDomain (as_nat h0 uh) % prime)) % prime);
    (==) {lemma_mod_add_distr (- fromDomain (as_nat h0 hCube)) (fromDomain r * fromDomain r) prime}
    toDomain (((fromDomain r * fromDomain r - fromDomain (as_nat h0 hCube)) % prime - (2 * fromDomain (as_nat h0 uh) % prime)) % prime);
    (==) {lemma_mod_sub_distr ((fromDomain r * fromDomain r - fromDomain (as_nat h0 hCube)) % prime) (2 * fromDomain (as_nat h0 uh)) prime}
    toDomain (((fromDomain r * fromDomain r - fromDomain (as_nat h0 hCube)) % prime - (2 * fromDomain (as_nat h0 uh))) % prime);
    (==) {lemma_mod_add_distr (- (2 * fromDomain (as_nat h0 uh))) ((fromDomain r * fromDomain r - fromDomain (as_nat h0 hCube))) prime}
    toDomain ((fromDomain r * fromDomain r - fromDomain (as_nat h0 hCube) - (2 * fromDomain (as_nat h0 uh))) % prime);
    (==) {_ by (canon())}
    toDomain ((fromDomain r * fromDomain r - fromDomain (as_nat h0 hCube) - 2 * fromDomain (as_nat h0 uh)) % prime);
  }


val computex3_point_add: #c : curve -> hCube: felem c -> uh: felem c -> 
  r: felem c -> t5: lbuffer uint64 (size 5 *! getCoordinateLenU64 c) ->  
  Stack unit 
  (requires fun h0 -> 
    live h0 hCube /\ live h0 uh /\ live h0 r /\ live h0 t5 /\
    disjoint hCube t5 /\ disjoint uh t5 /\ disjoint r t5 /\
    felem_eval c h0 hCube /\ felem_eval c h0 uh /\ felem_eval c h0 r)
  (ensures fun h0 _ h1 -> 
    let x3 = gsub t5 (size 0) (getCoordinateLenU64 c) in 
    modifies (loc t5) h0 h1 /\ 
    x3Invariant #c h0 h1 x3 r hCube uh
  )


let computex3_point_add #c hCube uh r t4 = 
  [@inline_let]
  let len = getCoordinateLenU64 c in 
  
  let x3 = sub t4 (size 0) len in 
  let tempBuffer3 = sub t4 len (size 3 *! len) in 
  _computeX3_point_add x3 hCube uh r tempBuffer3


inline_for_extraction noextract 
val _computeY3_point_add: #c: curve -> y3: felem c -> s1: felem c -> 
  hCube: felem c -> uh: felem c -> x3_out: felem c -> r: felem c -> 
  t3: lbuffer uint64 (size 3 *! getCoordinateLenU64 c) -> 
  Stack unit 
    (requires fun h -> 
      live h y3 /\ live h s1 /\ live h hCube /\ live h uh /\ live h uh /\ live h x3_out /\ live h r /\ live h t3 /\
      
      disjoint uh t3 /\
      disjoint x3_out t3 /\
      disjoint y3 t3 /\
      disjoint r t3 /\
      disjoint s1 t3 /\
      disjoint hCube t3 /\ 

      disjoint y3 s1 /\ disjoint y3 hCube /\ disjoint y3 uh /\ disjoint y3 x3_out /\ disjoint y3 r /\
      
      felem_eval c h s1 /\ felem_eval c h hCube /\ felem_eval c h uh /\ felem_eval c h x3_out /\ 
      felem_eval c h r)
    (ensures fun h0 _ h1 ->
      modifies (loc y3 |+| loc t3) h0 h1 /\ y3Invariant #c h0 h1 y3 s1 hCube uh x3_out r)
      

let _computeY3_point_add #c y3 s1 hCube uh x3 r t3 = 
  let h0 = ST.get() in

  [@inline_let]
  let len = getCoordinateLenU64 c in 
  
  let s1hCube = sub t3 (size 0) len in 
  let u1hx3 = sub t3 len len in 
  let ru1hx3 = sub t3 (size 2 *! len) len in 

  montgomery_multiplication_buffer s1 hCube s1hCube;
  felem_sub uh x3 u1hx3; 
  montgomery_multiplication_buffer u1hx3 r ru1hx3; 
  felem_sub #c ru1hx3 s1hCube y3;

  let h3 = ST.get() in 


  let prime = getPrime c in

  let s1D = fromDomain_ #c (as_nat c h0 s1) in 
  let hCubeD = fromDomain_ #c (as_nat c h0 hCube) in 
  let uhD = fromDomain_ #c (as_nat c h0 uh) in 
  let x3D = fromDomain_ #c (as_nat c h0 x3) in 
  let rD = fromDomain_ #c (as_nat c h0 r) in 

  calc (==)
  {
    toDomain_ #c (((uhD - x3D) % prime * rD % prime  - (s1D * hCubeD % prime)) % getPrime c);
    (==) {lemma_mod_mul_distr_l (uhD - x3D) rD prime}
    toDomain_ #c (((uhD - x3D) * rD % prime  - (s1D * hCubeD % prime)) % getPrime c);
    (==) {_ by (canon())}
    toDomain_ #c (((uhD - x3D) * rD % prime  - s1D * hCubeD % prime) % getPrime c);
    (==) {lemma_mod_sub_distr ((uhD - x3D) * rD % prime) (s1D * hCubeD) prime}
    toDomain_ #c (((uhD - x3D) * rD % prime - s1D * hCubeD) % getPrime c);
    (==) {lemma_mod_add_distr (-s1D * hCubeD) ((uhD - x3D) * rD) prime}
    toDomain_ #c (((uhD - x3D) * rD - s1D * hCubeD) % getPrime c);
  }


val computeY3_point_add: #c: curve -> s1: felem c -> hCube: felem c -> uh: felem c -> r: felem c -> 
  t5: lbuffer uint64 (size 5 *! getCoordinateLenU64 c) -> 
  Stack unit 
    (requires fun h -> 
      let x3_out = gsub t5 (size 0) (getCoordinateLenU64 c) in 
      live h s1 /\ live h hCube /\ live h uh /\ live h r /\ live h t5 /\
      
      disjoint uh t5 /\
      disjoint r t5 /\
      disjoint s1 t5 /\
      disjoint hCube t5 /\ 
      
      felem_eval c h s1 /\ 
      felem_eval c h hCube /\
      felem_eval c h uh /\ 
      felem_eval c h x3_out /\ 
      felem_eval c h r)
    (ensures fun h0 _ h1 -> 
      let len = getCoordinateLenU64 c in 
      let x3_out = gsub t5 (size 0) len in 
      let y3_out = gsub t5 len len in 
      modifies (loc t5) h0 h1 /\
      as_nat c h0 x3_out == as_nat c h1 x3_out /\
      y3Invariant #c h0 h1 y3_out s1 hCube uh x3_out r)


let computeY3_point_add #c s1 hCube uh r tempBuffer5 = 
  let x3 = sub tempBuffer5 (size 0) (getCoordinateLenU64 c) in 
  let y3 = sub tempBuffer5 (getCoordinateLenU64 c) (getCoordinateLenU64 c) in 
  let tempBuffer3 = sub tempBuffer5 (size 2 *! getCoordinateLenU64 c) (size 3 *! getCoordinateLenU64 c) in 
  _computeY3_point_add #c y3 s1 hCube uh x3 r tempBuffer3



inline_for_extraction noextract 
val __computeZ3_point_add: #c: curve -> z3: felem  c ->  z1: felem c -> z2: felem c ->
  h: felem c -> tempBuffer: felem c -> 
  Stack unit
  (requires fun h0 -> 
    live h0 z3 /\ live h0 z1 /\ live h0 z2 /\ live h0 h /\  live h0 tempBuffer /\
    disjoint z3 z1 /\ disjoint z1 tempBuffer /\ disjoint tempBuffer h /\
    disjoint h z3 /\ disjoint z2 tempBuffer /\ disjoint z3 z2 /\
    felem_eval c h0 z1 /\ felem_eval c h0 z2 /\ felem_eval c h0 h)
  (ensures fun h0 _ h1 ->
    modifies (loc z3 |+| loc tempBuffer) h0 h1 /\ 
    z3Invariant #c h0 h1 z3 z1 z2 h)  


let __computeZ3_point_add #c z3 z1 z2 h tempBuffer = 
  let h0 = ST.get() in 
  let z1z2 = sub tempBuffer (size 0) (getCoordinateLenU64 c) in
  montgomery_multiplication_buffer z1 z2 z1z2;
  montgomery_multiplication_buffer z1z2 h z3;

  calc (==)
  {
    toDomain_ #c ((fromDomain_ #c (as_nat c h0 z1) * fromDomain_ #c (as_nat c h0 z2) % getPrime c) * fromDomain_ #c (as_nat c h0 h) % getPrime c);
    (==) {lemma_mod_mul_distr_l (fromDomain_ #c (as_nat c h0 z1) * fromDomain_ #c (as_nat c h0 z2)) (fromDomain_ #c (as_nat c h0 h)) (getPrime c)}
    toDomain_ #c (fromDomain_ #c (as_nat c h0 z1) * fromDomain_ #c (as_nat c h0 z2) * fromDomain_ #c (as_nat c h0 h) % getPrime c);}


inline_for_extraction noextract 
val computeZ3_point_add: #c: curve -> p: point c -> q: point c ->
  h: felem c -> t5: lbuffer uint64 (size 5 *! getCoordinateLenU64 c) -> 
  Stack unit 
  (requires fun h0 -> 
    live h0 t5 /\ live h0 p /\ live h0 q /\ live h0 h /\ 
    disjoint t5 p /\ disjoint t5 h /\ disjoint t5 q /\
    point_eval c h0 p /\ point_eval c h0 q /\ felem_eval c h0 h)
  (ensures fun h0 _ h1 ->     
    modifies (loc t5) h0 h1 /\ (
    let len = getCoordinateLenU64 c in 
    let z1 = getZ p in 
    let z2 = getZ q in 
    
    let x3, y3, z3 = getXYZ #c t5 in 
    
    as_nat c h0 x3 == as_nat c h1 x3 /\
    as_nat c h0 y3 == as_nat c h1 y3 /\
    z3Invariant #c h0 h1 z3 z1 z2 h))

let computeZ3_point_add #c p q h t5 = 
  [@inline_let]
  let len = getCoordinateLenU64 c in 

  let z1 = sub p (size 2 *! len) len in 
  let z2 = sub q (size 2 *! len) len in 
  let z3 = sub t5 (size 2 *! len) len in 
  let t1 = sub t5 (size 3 *! len) len in 

  __computeZ3_point_add z3 z1 z2 h t1


val copy_result_point_add: #c: curve 
  -> t5: lbuffer uint64 (size 5 *! (getCoordinateLenU64 c)) 
  -> p: point c -> q: point c -> result: point c ->
  Stack unit 
    (requires fun h -> live h t5 /\ live h p /\ live h q /\ live h result /\
      eq_or_disjoint p result /\
      disjoint t5 result /\
      LowStar.Monotonic.Buffer.all_disjoint [loc t5; loc p; loc q]
    )
    (ensures fun h0 _ h1 -> 
      let x3_out, y3_out, z3_out = getXYZ #c t5 in 
      modifies (loc t5 |+| loc result) h0 h1 /\ (
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


let copy_result_point_add #c t5 p q result = 
  let h0 = ST.get() in 
  [@inline_let]
  let len = getCoordinateLenU64 c in 

  let x3_out = sub t5 (size 0) len in 
  let y3_out = sub t5 len len in 
  let z3_out = sub t5 (size 2 *! len) len in 

  copy_point_conditional x3_out y3_out z3_out q p;
  copy_point_conditional x3_out y3_out z3_out p q;
  concat3 len x3_out len y3_out len z3_out result


val computeXY: #c: curve -> hCube: felem c -> uh: felem c 
  -> r: felem c -> t5: lbuffer uint64 (size 5 *! getCoordinateLenU64 c) 
  -> s1: felem c -> h: felem c ->
  Stack unit 
  (requires fun h0 -> 
    live h0 t5 /\ live h0 hCube /\ live h0 uh /\ live h0 r /\ live h0 s1 /\ live h0 h /\
    felem_eval c h0 hCube /\ felem_eval c h0 uh /\ felem_eval c h0 r /\ 
    felem_eval c h0 s1 /\ felem_eval c h0 h /\
    disjoint uh t5 /\ disjoint t5 hCube /\ disjoint hCube t5 /\ disjoint r t5 /\ disjoint t5 s1)
  (ensures fun h0 _ h1 -> modifies (loc t5) h0 h1 /\ (
    let x3_out, y3_out, _ = getXYZ #c t5 in 
    x3Invariant #c h0 h1 x3_out r hCube uh /\
    y3Invariant #c h0 h1 y3_out s1 hCube uh x3_out r))

let computeXY #c hCube uh r t5 s1 h = 
  computex3_point_add #c hCube uh r t5; 
  computeY3_point_add #c s1 hCube uh r t5



val computeXYZ: #c: curve -> p: point c -> q: point c -> hCube: felem c -> uh: felem c 
  -> r: felem c -> t5: lbuffer uint64 (size 5 *! getCoordinateLenU64 c) 
  -> s1: felem c -> h: felem c ->
  Stack unit 
    (requires fun h0 ->  
      live h0 p /\ live h0 q /\ live h0 hCube /\ live h0 uh /\ live h0 r /\ live h0 t5 /\ live h0 s1 /\ live h0 h /\

      felem_eval c h0 hCube /\ felem_eval c h0 uh /\ felem_eval c h0 r /\
      felem_eval c h0 s1 /\ felem_eval c h0 h /\ 
      
      point_eval c h0 q /\  point_eval c h0 p /\
      
      disjoint hCube t5 /\ disjoint uh t5 /\ disjoint r t5 /\ 
      disjoint t5 s1 /\ disjoint t5 h /\ disjoint t5 p /\ disjoint t5 q
    )
    (ensures fun h0 _ h1 -> modifies (loc t5) h0 h1 /\
      (
	let z1, z2 = getZ p, getZ q in 
	
	let x3_out, y3_out, z3_out = getXYZ t5 in
	
	x3Invariant #c h0 h1 x3_out r hCube uh /\
	y3Invariant #c h0 h1 y3_out s1 hCube uh x3_out r /\ 
	z3Invariant #c h0 h1 z3_out z1 z2 h))


let computeXYZ #c p q hCube uh r t5 s1 h = 
    let h0 = ST.get() in 
  computeXY #c hCube uh r t5 s1 h;  
    let h1 = ST.get() in 
    lemma_point_eval c h0 h1 p; 
    lemma_point_eval c h0 h1 q;
    lemma_coord_eval c h0 h1 p;
    lemma_coord_eval c h0 h1 q;

  computeZ3_point_add #c p q h t5


val __point_add_if_second_branch_impl: #c: curve -> result: point c 
  -> p: point c -> q: point c 
  -> u1: felem c -> u2: felem c -> s1: felem c -> s2: felem c 
  -> r: felem c -> h: felem c -> uh: felem c -> hCube: felem c 
  -> t5 : lbuffer uint64 (size 5 *! getCoordinateLenU64 c) -> 
  Stack unit (requires fun h0 -> 
    live h0 result /\ live h0 t5 /\ live h0 p /\ live h0 q /\ live h0 u1 /\ live h0 u2 /\ live h0 s1 /\ live h0 s2 /\ live h0 r /\ live h0 h /\ live h0 uh /\ live h0 hCube /\
    
    point_eval c h0 p /\ point_eval c h0 q /\ 
   
    eq_or_disjoint p result /\ disjoint result t5 /\ disjoint p q /\ 
    felem_eval c h0 r /\ felem_eval c h0 s1 /\ felem_eval c h0 h /\ 

    disjoint hCube t5 /\ disjoint uh t5 /\ disjoint r t5 /\ 
    disjoint t5 s1 /\ disjoint t5 h /\ 
    disjoint t5 p /\ disjoint t5 q /\
    
    uhInvariant #c h0 uh h u1 /\
    hCubeInvariant #c h0 hCube h 
  )
  (ensures fun h0 _ h1 -> modifies (loc t5 |+| loc result) h0 h1 /\ (
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
      z3 == toDomain_ #c (pzD * qzD * hD % prime))))



let __point_add_if_second_branch_impl #c result p q u1 u2 s1 s2 r h uh hCube t5 = 
    let h0 = ST.get() in
  computeXYZ #c p q hCube uh r t5 s1 h;
    let h1 = ST.get() in
  copy_result_point_add t5 p q result;
    let h2 = ST.get() in
    lemma_coord_eval c h0 h1 p;
    lemma_coord_eval c h0 h1 q;
    lemma_point_add_if #c p q result t5 u1 u2 s1 s2 r h uh hCube h0 h1 h2


val _point_add_if_second_branch_impl: #c: curve -> result: point c 
  -> p: point c -> q: point c 
  -> x3y3z3u1u2s1s2: lbuffer uint64 (size 8 *! getCoordinateLenU64 c) 
  -> r: felem c -> h: felem c -> uh: felem c -> hCube: felem c 
  -> t5 : lbuffer uint64 (size 5 *! getCoordinateLenU64 c) -> 
  Stack unit (requires fun h0 -> 

    let u1, u2, s1, s2 = getU1S2 x3y3z3u1u2s1s2 in 

    live h0 result /\ live h0 x3y3z3u1u2s1s2 /\ live h0 p /\ live h0 q /\ live h0 t5 /\ live h0 r /\ live h0 h /\ live h0 uh /\ live h0 hCube /\
    point_eval c h0 p /\ point_eval c h0 q /\ 
   
    eq_or_disjoint p result /\ disjoint result t5 /\ disjoint p q /\
    felem_eval c h0 r /\ felem_eval c h0 s1 /\ felem_eval c h0 h /\ 

    disjoint hCube t5 /\ disjoint uh t5 /\ 
    disjoint r t5 /\ disjoint t5 x3y3z3u1u2s1s2 /\
    disjoint t5 h /\  
    disjoint t5 p /\ disjoint t5 q /\
    
    
    uhInvariant #c h0 uh h u1 /\
    hCubeInvariant #c h0 hCube h 
  )
  (ensures fun h0 _ h1 -> modifies (loc t5 |+| loc result) h0 h1 /\ (
    let prime = getPrime c in 

    let u1, u2, s1, s2 = getU1S2 x3y3z3u1u2s1s2 in 
  
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
      z3 == toDomain_ #c (pzD * qzD * hD % prime))))


let _point_add_if_second_branch_impl #c result p q x3y3z3u1u2s1s2 r h uh hCube t5 = 
  [@inline_let]
  let len = getCoordinateLenU64 c in 

  lemma_ICuttable_point_add0 #c; 

  let u1 = sub x3y3z3u1u2s1s2 (size 4 *! len) len in 
  let u2 = sub x3y3z3u1u2s1s2 (size 5 *! len) len in 
  let s1 = sub x3y3z3u1u2s1s2 (size 6 *! len) len in 
  let s2 = sub x3y3z3u1u2s1s2 (size 7 *! len) len in 
  
  __point_add_if_second_branch_impl result p q u1 u2 s1 s2 r h uh hCube t5 


val _point_add_if_second_branch_impl0: #c: curve -> result: point c 
  -> p: point c -> q: point c 
  -> x3y3z3u1u2s1s2: lbuffer uint64 (size 8 *! getCoordinateLenU64 c) 
  -> rhuhhCube: lbuffer uint64 (size 4 *! getCoordinateLenU64 c)
  -> t5 : lbuffer uint64 (size 5 *! getCoordinateLenU64 c) -> 
  Stack unit (requires fun h0 -> 
    let u1, u2, s1, s2 = getU1S2 x3y3z3u1u2s1s2 in 
    let h, r, uh, hCube = getHHCube rhuhhCube in 

    live h0 result /\ live h0 p /\ live h0 q /\ live h0 x3y3z3u1u2s1s2 /\ live h0 rhuhhCube /\ live h0 t5 /\ 

    point_eval c h0 p /\ point_eval c h0 q /\ 
   
    eq_or_disjoint p result /\ disjoint result t5 /\ disjoint p q /\

    disjoint hCube t5 /\ disjoint uh t5 /\ 
    disjoint r t5 /\ disjoint t5 x3y3z3u1u2s1s2 /\
    disjoint t5 h /\ disjoint t5 p /\ disjoint t5 q /\
    
    felem_eval c h0 r /\ felem_eval c h0 s1 /\ felem_eval c h0 h /\ 
    
    uhInvariant #c h0 uh h u1 /\
    hCubeInvariant #c h0 hCube h 
  )
  (ensures fun h0 _ h1 -> modifies (loc t5 |+| loc result) h0 h1 /\ (
    let prime = getPrime c in 

    let u1, u2, s1, s2 = getU1S2 x3y3z3u1u2s1s2 in 
    let h, r, uh, hCube = getHHCube rhuhhCube in 
  
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
      z3 == toDomain_ #c (pzD * qzD * hD % prime))))


let _point_add_if_second_branch_impl0 #c result p q x3y3z3u1u2s1s2 rhuhhCube tempBuffer5 = 
  [@inline_let]
  let len = getCoordinateLenU64 c in 

  let h = sub rhuhhCube (size 0) len in 
  let r = sub rhuhhCube len len in 
  let uh = sub rhuhhCube (size 2 *! len) len in 
  let hCube = sub rhuhhCube (size 3 *! len) len in 
  
  _point_add_if_second_branch_impl result p q x3y3z3u1u2s1s2 r h uh hCube tempBuffer5


val _point_add_if_second_branch_impl1: #c: curve -> result: point c 
  -> p: point c -> q: point c 
  -> x3hCube: lbuffer uint64 (size 12 *! getCoordinateLenU64 c) 
  -> t5 : lbuffer uint64 (size 5 *! getCoordinateLenU64 c) -> 
  Stack unit (requires fun h0 -> 
    let  u1, u2, s1, s2, h, r, uh, hCube = getU1HCube x3hCube in 

    live h0 result /\ live h0 p /\ live h0 q /\ live h0 x3hCube /\ live h0 t5 /\ 

    point_eval c h0 p /\ point_eval c h0 q /\ 
   
    eq_or_disjoint p result /\ disjoint result t5 /\ disjoint p q /\
    
    disjoint t5 x3hCube /\  disjoint t5 p /\ disjoint t5 q /\
    felem_eval c h0 r /\ felem_eval c h0 s1 /\ felem_eval c h0 h /\ 
    
    uhInvariant #c h0 uh h u1 /\
    hCubeInvariant #c h0 hCube h 
  )
  (ensures fun h0 _ h1 -> modifies (loc t5 |+| loc result) h0 h1 /\ (
    let prime = getPrime c in 

    let  u1, u2, s1, s2, h, r, uh, hCube = getU1HCube x3hCube in 
  
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
      z3 == toDomain_ #c (pzD * qzD * hD % prime))))



let _point_add_if_second_branch_impl1 #c result p q x3hCube t5 = 
  [@inline_let]
  let len = getCoordinateLenU64 c in 
  
  let x3y3z3u1u2s1s2 = sub x3hCube (size 0) (size 8 *! len) in 
  let rhuhhCube = sub x3hCube (size 8 *! len) (size 4 *! len) in 
  let h0 = ST.get() in 

  l0 #c x3hCube h0 p q;
  lemma_disjoint_invariant #c x3hCube t5;
  _point_add_if_second_branch_impl0 #c result p q x3y3z3u1u2s1s2 rhuhhCube t5


val _point_add_0: #c: curve -> p: point c -> q: point c -> t12: lbuffer uint64 (size 12 *! getCoordinateLenU64 c) -> 
  Stack unit 
    (requires fun h0 ->   
      live h0 p /\ live h0 q /\ live h0 t12 /\
      LowStar.Monotonic.Buffer.all_disjoint [loc t12; loc p; loc q] /\ 
      point_eval c h0 p /\ point_eval c h0 q)
    (ensures fun h0 _ h1 -> 
      modifies (loc t12) h0 h1 /\ point_eval c h1 p /\ point_eval c h1 q /\  (
      let  u1, u2, s1, s2, h, r, uh, hCube = getU1HCube t12 in 
      
      u1Invariant #c h0 h1 u1 p q /\
      u2Invariant #c h0 h1 u2 p q /\ 
      s1Invariant #c h0 h1 s1 p q /\
      s2Invariant #c h0 h1 s2 p q /\ 
      hInvariant #c h1 h u1 u2 /\
      rInvariant #c h1 r s1 s2 /\
      uhInvariant #c h1 uh h u1 /\
      hCubeInvariant #c h1 hCube h))
      
  
let _point_add_0 #c p q t12 = 
  [@inline_let]
  let len = getCoordinateLenU64 c in 
  let h0 = ST.get() in 
  
  move_from_jacobian_coordinates p q t12;
  compute_common_params_point_add t12;
  let h1 = ST.get() in
  lemma_point_eval c h0 h1 p;
  lemma_point_eval c h0 h1 q 
  


let point_add #c p q result tempBuffer = 
  let h0 = ST.get() in 
  let t12 = sub tempBuffer (size 0) (size 12 *! getCoordinateLenU64 c) in 
  let t5 = sub tempBuffer (size 12 *! getCoordinateLenU64 c) (size 5 *! getCoordinateLenU64 c) in 

  _point_add_0 #c p q t12;
  let h1 = ST.get() in 
  _point_add_if_second_branch_impl1 result p q t12 t5;
  
  let h2 = ST.get() in 
  lemma_coord_eval c h0 h1 p;
  lemma_coord_eval c h0 h1 q;

  
  let prime = getPrime c in 

  let x3, y3, z3 = point_x_as_nat c h2 result, point_y_as_nat c h2 result, point_z_as_nat c h2 result in
  let pX, pY, pZ = point_x_as_nat c h0 p, point_y_as_nat c h0 p, point_z_as_nat c h0 p in 
  let qX, qY, qZ = point_x_as_nat c h0 q, point_y_as_nat c h0 q, point_z_as_nat c h0 q in 

  let pxD, pyD, pzD = fromDomain_ #c pX, fromDomain_ #c pY, fromDomain_ #c pZ in 
  let qxD, qyD, qzD = fromDomain_ #c qX, fromDomain_ #c qY, fromDomain_ #c qZ in 
  let x3D, y3D, z3D = fromDomain_ #c x3, fromDomain_ #c y3, fromDomain_ #c z3 in 


  calc (==)
  {
    qzD * qzD * pxD % prime;
    (==) {_ by (canon())}
    pxD * (qzD * qzD) % prime; };
    
  calc (==)
  {
    pzD * pzD * qxD % prime;
    (==) {_ by (canon())}
    qxD * (pzD * pzD) % prime;
  };
    
  calc (==)
  {
    qzD * qzD * qzD * pyD % prime;
    (==) {_ by (canon())}
    pyD * qzD * (qzD * qzD) % prime;
  };

  calc(==)
  {
    pzD * pzD * pzD * qyD % prime;
    (==) {_ by (canon())}
    qyD * pzD * (pzD * pzD) % prime;
  };


  let u1D = pxD * (qzD * qzD) % prime in
  let u2D = qxD * (pzD * pzD) % prime in    

  let s1D = pyD * qzD * (qzD * qzD) % prime in 
  let s2D = qyD * pzD * (pzD * pzD) % prime in 
    
  let hD = (u2D - u1D) % prime in
  let rD = (s2D - s1D) % prime in  

  calc (==)
  {
    (rD * rD - hD * hD * hD - 2 * hD * hD * u1D) % prime;
    (==) {_ by (canon())}
    ((rD * rD) - (hD * hD * hD) - (2 * u1D * (hD * hD))) % prime;
  };

  calc (==)
  {
    (((hD * hD * u1D - fromDomain_  #c x3) * rD - s1D * hD * hD * hD) % prime);
    (==) {_ by (canon())}
    (rD * (u1D * (hD * hD) - fromDomain_  #c x3) - s1D * (hD * hD * hD)) % prime;
  };

  calc (==)
  {
    (pzD * qzD * hD % prime);
    (==) {_ by (canon())}
    (hD * pzD * qzD) % prime;
  }
