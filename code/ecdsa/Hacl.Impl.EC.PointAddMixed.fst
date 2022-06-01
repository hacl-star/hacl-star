module Hacl.Impl.EC.PointAddMixed

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Hacl.Impl.EC.Arithmetics

open Lib.Buffer

open Hacl.Impl.EC.LowLevel
open Hacl.Impl.EC.MontgomeryMultiplication
open Spec.ECC

open FStar.Tactics 
open FStar.Tactics.Canon

open FStar.Math.Lemmas
open Hacl.Impl.EC.Masking

open Hacl.Spec.MontgomeryMultiplication
open FStar.Mul

open Hacl.Impl.P.PointAdd.Aux
open Hacl.Impl.P.PointAddMixed.Aux
open Hacl.Impl.EC.MixedPA.MM


#set-options "--z3rlimit 300 --ifuel 0 --fuel 0"  

inline_for_extraction noextract 
val pointAffineIsNotZero: #c: curve -> p: pointAffine c -> Stack uint64
  (requires fun h -> live h p /\ point_aff_eval c h p)
  (ensures fun h0 r h1 -> modifies0 h0 h1 /\ (v r == 0 \/ v r == pow2 64 - 1) /\ (
    v r == pow2 64 - 1 <==> isPointAtInfinityAffine (point_affine_as_nat c h0 p)))

let pointAffineIsNotZero #c p = 
  let len = getCoordinateLenU64 c in 
  
  let x = sub p (size 0) len in 
  let y = sub p len len in 

  let xZero = isZero_uint64_CT #c x in 
  let yZero = isZero_uint64_CT #c y in 

  logand_lemma xZero yZero;
  logand xZero yZero

inline_for_extraction noextract
val copy_point_conditional_: #c: curve -> x3_out: felem c -> y3_out: felem c -> z3_out: felem c 
  -> p: pointAffine c -> mask: point c -> temp : felem c ->
  Stack unit
  (requires fun h -> point_eval c h mask /\ point_aff_eval c h p /\ 
    felem_eval c h x3_out /\ felem_eval c h y3_out /\ felem_eval c h z3_out /\
    disjoint temp z3_out /\ disjoint temp x3_out /\ disjoint temp y3_out /\ disjoint temp p /\ 
    live h x3_out /\ live h y3_out /\ live h z3_out /\ live h p /\ live h mask /\ live h temp /\ 
    LowStar.Monotonic.Buffer.all_disjoint [loc x3_out; loc y3_out; loc z3_out; loc p; loc mask])
  (ensures fun h0 _ h1 -> modifies (loc x3_out |+| loc y3_out |+| loc z3_out |+| loc temp) h0 h1 /\
    felem_eval c h1 x3_out /\ felem_eval c h1 y3_out /\ felem_eval c h1 z3_out /\ (
    let x, y = point_affine_x_as_nat c h0 p, point_affine_y_as_nat c h0 p in
    if isPointAtInfinity (point_as_nat c h0 mask) then
      as_nat c h1 x3_out == x /\
      as_nat c h1 y3_out == y /\ 
      as_nat c h1 z3_out == 1
    else 
      as_nat c h1 x3_out == as_nat c h0 x3_out /\ 
      as_nat c h1 y3_out == as_nat c h0 y3_out /\
      as_nat c h1 z3_out == as_nat c h0 z3_out)) 


let copy_point_conditional_ #c x3_out y3_out z3_out p maskPoint temp = 
  let h0 = ST.get() in 
  [@inline_let]
  let len = getCoordinateLenU64 c in 

  let z = sub maskPoint (size 2 *! len) len in 
  let mask = isZero_uint64_CT #c z in 
  
  let p_x = sub p (size 0) len in 
  let p_y = sub p len len in 

  uploadOneImpl #c temp;
  
  copy_conditional x3_out p_x mask;
  copy_conditional y3_out p_y mask;
  copy_conditional z3_out temp mask


let copy_point_conditional_p256 = copy_point_conditional_ #P256

let copy_point_conditional_p384 = copy_point_conditional_ #P384


inline_for_extraction noextract
val copy_point_conditional: #c: curve -> x3_out: felem c -> y3_out: felem c -> z3_out: felem c 
  -> p: pointAffine c -> mask: point c -> temp : felem c ->
  Stack unit
  (requires fun h -> point_eval c h mask /\ point_aff_eval c h p /\ 
    felem_eval c h x3_out /\ felem_eval c h y3_out /\ felem_eval c h z3_out /\
    disjoint temp z3_out /\ disjoint temp x3_out /\ disjoint temp y3_out /\ disjoint temp p /\ 
    live h x3_out /\ live h y3_out /\ live h z3_out /\ live h p /\ live h mask /\ live h temp /\ 
    LowStar.Monotonic.Buffer.all_disjoint [loc x3_out; loc y3_out; loc z3_out; loc p; loc mask])
  (ensures fun h0 _ h1 -> modifies (loc x3_out |+| loc y3_out |+| loc z3_out |+| loc temp) h0 h1 /\
    felem_eval c h1 x3_out /\ felem_eval c h1 y3_out /\ felem_eval c h1 z3_out /\ (
    let x, y = point_affine_x_as_nat c h0 p, point_affine_y_as_nat c h0 p in
    if isPointAtInfinity (point_as_nat c h0 mask) then
      as_nat c h1 x3_out == x /\
      as_nat c h1 y3_out == y /\ 
      as_nat c h1 z3_out == 1
    else 
      as_nat c h1 x3_out == as_nat c h0 x3_out /\ 
      as_nat c h1 y3_out == as_nat c h0 y3_out /\
      as_nat c h1 z3_out == as_nat c h0 z3_out)) 


let copy_point_conditional #c x3_out y3_out z3_out p maskPoint temp = 
  match c with 
  |P256 -> copy_point_conditional_p256 x3_out y3_out z3_out p maskPoint temp
  |P384 -> copy_point_conditional_p384 x3_out y3_out z3_out p maskPoint temp


inline_for_extraction noextract
val copy_point_conditional1_: #c: curve -> x3_out: felem c -> y3_out: felem c -> z3_out: felem c -> p: point c 
  -> q: pointAffine c ->
  Stack unit
  (requires fun h -> point_eval c h p /\ point_aff_eval c h q /\
    felem_eval c h x3_out /\ felem_eval c h y3_out /\ felem_eval c h z3_out /\ 
    live h x3_out /\ live h y3_out /\ live h z3_out /\ live h p /\ live h q /\
    LowStar.Monotonic.Buffer.all_disjoint [loc x3_out; loc y3_out; loc z3_out; loc p; loc q])
  (ensures fun h0 _ h1 -> modifies (loc x3_out |+| loc y3_out |+| loc z3_out) h0 h1 /\ point_aff_eval c h0 q /\
    felem_eval c h1 x3_out /\ felem_eval c h1 y3_out /\ felem_eval c h1 z3_out /\ (
    let len = getCoordinateLenU64 c in 
    let x, y, z = point_x_as_nat c h0 p, point_y_as_nat c h0 p, point_z_as_nat c h0 p in
    if isPointAtInfinityAffine (point_affine_as_nat c h0 q) then
      as_nat c h1 x3_out == x /\
      as_nat c h1 y3_out == y /\ 
      as_nat c h1 z3_out == z
    else 
      as_nat c h1 x3_out == as_nat c h0 x3_out /\ 
      as_nat c h1 y3_out == as_nat c h0 y3_out /\ 
      as_nat c h1 z3_out == as_nat c h0 z3_out))


let copy_point_conditional1_ #c x3_out y3_out z3_out p q = 
  [@inline_let]
  let len = getCoordinateLenU64 c in 

  let mask = pointAffineIsNotZero #c q in 

  let p_x = sub p (size 0) len in 
  let p_y = sub p len len in 
  let p_z = sub p (size 2 *! len) len in 

  copy_conditional x3_out p_x mask;
  copy_conditional y3_out p_y mask;
  copy_conditional z3_out p_z mask


let copy_point_conditional1_p256 = copy_point_conditional1_ #P256

let copy_point_conditional1_p384 = copy_point_conditional1_ #P384


inline_for_extraction noextract
val copy_point_conditional1: #c: curve -> x3_out: felem c -> y3_out: felem c -> z3_out: felem c -> p: point c 
  -> q: pointAffine c ->
  Stack unit
  (requires fun h -> point_eval c h p /\ point_aff_eval c h q /\
    felem_eval c h x3_out /\ felem_eval c h y3_out /\ felem_eval c h z3_out /\ 
    live h x3_out /\ live h y3_out /\ live h z3_out /\ live h p /\ live h q /\
    LowStar.Monotonic.Buffer.all_disjoint [loc x3_out; loc y3_out; loc z3_out; loc p; loc q])
  (ensures fun h0 _ h1 -> modifies (loc x3_out |+| loc y3_out |+| loc z3_out) h0 h1 /\ point_aff_eval c h0 q /\
    felem_eval c h1 x3_out /\ felem_eval c h1 y3_out /\ felem_eval c h1 z3_out /\ (
    let len = getCoordinateLenU64 c in 
    let x, y, z = point_x_as_nat c h0 p, point_y_as_nat c h0 p, point_z_as_nat c h0 p in
    if isPointAtInfinityAffine (point_affine_as_nat c h0 q) then
      as_nat c h1 x3_out == x /\
      as_nat c h1 y3_out == y /\ 
      as_nat c h1 z3_out == z
    else 
      as_nat c h1 x3_out == as_nat c h0 x3_out /\ 
      as_nat c h1 y3_out == as_nat c h0 y3_out /\ 
      as_nat c h1 z3_out == as_nat c h0 z3_out))


let copy_point_conditional1 #c x3_out y3_out z3_out p q = 
  match c with
  | P256 -> copy_point_conditional1_p256 x3_out y3_out z3_out p q
  | P384 -> copy_point_conditional1_p384 x3_out y3_out z3_out p q


inline_for_extraction noextract 
val _move_from_jacobian_coordinates: #c: curve -> u1: felem c -> u2: felem c -> 
  s1: felem c -> s2: felem c -> p: point c -> q: pointAffine c -> 
  tempBuffer4: lbuffer uint64 (size 4 *! getCoordinateLenU64 c) -> 
  Stack unit (requires fun h ->  
    live h u1 /\ live h u2 /\ live h s1 /\ live h s2 /\ live h tempBuffer4 /\ live h p /\ 
    live h q /\ point_eval c h p /\ point_aff_eval c h q /\
    LowStar.Monotonic.Buffer.all_disjoint [loc tempBuffer4; loc p; loc q; loc u1; loc u2; loc s1; loc s2])
  (ensures fun h0 _ h1 ->  
    modifies (loc u1 |+| loc u2 |+| loc s1 |+| loc s2 |+| loc tempBuffer4) h0 h1 /\
    u1Invariant #c h0 h1 u1 p /\ u2Invariant #c h0 h1 u2 p q /\
    s1Invariant #c h0 h1 s1 p /\ s2Invariant #c h0 h1 s2 p q)


let _move_from_jacobian_coordinates #c u1 u2 s1 s2 p q tempBuffer = 
  let h0 = ST.get() in 
  
  [@inline_let]
  let len = getCoordinateLenU64 c in 
    
  let pX = sub p (size 0) len in 
  let pY = sub p len len in 
  let pZ = sub p (size 2 *! len) len in 

  let qX = sub q (size 0) len in 
  let qY = sub q len len in 

  let z2Square = sub tempBuffer (size 0) len in 
  let z1Square = sub tempBuffer len len in 
  let z2Cube = sub tempBuffer (size 2 *! len) len in 
  let z1Cube = sub tempBuffer (size 3 *! len) len in  

  let h0 = ST.get() in 

  montgomery_multiplication_buffer_by_one_mixed #c z2Square;
  montgomery_square_buffer_dh #c pZ z1Square;

  montgomery_multiplication_buffer_by_one_dh #c z2Square z2Cube;
  montgomery_multiplication_buffer_dh #c z1Square pZ z1Cube;

  montgomery_multiplication_buffer_dh #c z2Square pX u1;
  montgomery_multiplication_buffer_dh #c z1Square qX u2;
    
  montgomery_multiplication_buffer_dh #c z2Cube pY s1;
  montgomery_multiplication_buffer_dh #c z1Cube qY s2;

  let h1 = ST.get() in 

  let prime = getPrime c in 
  
  let fromDomain = fromDomain #c in 
  let toDomain = toDomain #c in   
  let as_nat = as_nat c in 

  let pxD = fromDomain (as_nat h0 pX) in 
  let qxD = fromDomain (point_affine_x_as_nat c h0 q) in 

  let pyD = fromDomain (as_nat h0 pY) in 
  let qyD = fromDomain (point_affine_y_as_nat c h0 q) in 

  let pzD = fromDomain (as_nat h0 pZ) in 
  let oD = fromDomain 1 in 
  let oDD = fromDomain oD in 


  calc (==) {as_nat h1 u1; 
    (==) {}
    toDomain (fromDomain oD * pxD % prime);
    (==) {lemmaFromDomain #c #DH oD}
    toDomain ((oD * 1 * modp_inv2_prime (pow2 (getPower c)) prime % prime) * pxD % prime);
    (==) {assert_by_tactic (oD * 1 * modp_inv2_prime (pow2 (getPower c)) prime ==
    oD * (1 * modp_inv2_prime (pow2 (getPower c)) prime)) canon}
    toDomain ((oD * (1 * modp_inv2_prime (pow2 (getPower c)) prime) % prime) * pxD % prime);
    (==) {lemma_mod_mul_distr_r oD (1 * modp_inv2_prime (pow2 (getPower c)) prime) prime}
    toDomain ((oD * (1 * modp_inv2_prime (pow2 (getPower c)) prime % prime) % prime) * pxD % prime);
    (==) {lemmaFromDomain #c #DH 1} 
    toDomain ((oD * oD % prime) * pxD % prime);
    (==) {lemma_mod_mul_distr_l (oD * oD) pxD prime}
    toDomain (oD * oD * pxD % prime);
  };

  let k = modp_inv2_prime (pow2 (getPower c)) prime in 

  calc (==)
  {
    toDomain ((pzD * pzD % prime) * qxD % prime);
    (==) {lemma_mod_mul_distr_l (pzD * pzD) qxD prime}
    toDomain (pzD * pzD * qxD % prime);
  };
 
  calc (==) 
  {
    as_nat h1 s1;
    (==) {}
    toDomain (fromDomain oDD * pyD % prime);
    (==) {lemmaFromDomain #c #DH oDD}
    toDomain (fromDomain oD * k % prime * pyD % prime);
    (==) {lemmaFromDomain #c #DH oD}
    toDomain (oD * k % prime * k % prime * pyD % prime);
    (==) {assert_by_tactic (oD * 1 * k == oD * (1 * k)) canon}
    toDomain (oD * (1 * k) % prime * k % prime * pyD % prime);
    (==) {lemma_mod_mul_distr_r oD (1 * k) prime}
    toDomain (oD * (1 * k % prime) % prime * k % prime * pyD % prime);
    (==) {lemmaFromDomain #c #DH 1}
    toDomain (oD * oD % prime * (1 * k) % prime * pyD % prime);
    (==) {lemma_mod_mul_distr_r (oD * oD % prime) (1 * k) prime}
    toDomain (oD * oD % prime * (1 * k % prime) % prime * pyD % prime);
    (==) {lemmaFromDomain #c #DH 1}
    toDomain (oD * oD % prime * oD % prime * pyD % prime);
    (==) {lemma_mod_mul_distr_l (oD * oD) oD prime}
    toDomain (oD * oD * oD % prime * pyD % prime);
    (==) {lemma_mod_mul_distr_l (oD * oD * oD) pyD prime}
    toDomain (oD * oD * oD * pyD % prime);
  };

  calc (==) 
  {
    as_nat h1 s2;
    (==) {}
    toDomain (((pzD * pzD % prime) * pzD % prime) * qyD % prime);
    (==) {lemma_mod_mul_distr_l (pzD * pzD) pzD prime}
    toDomain(((pzD * pzD) * pzD % prime) * qyD % prime);
    (==) {lemma_mod_mul_distr_l (pzD * pzD * pzD) qyD prime}
    toDomain (pzD * pzD * pzD * qyD % prime);
  }



inline_for_extraction noextract 
val move_from_jacobian_coordinates: #c: curve -> p: point c -> q: pointAffine c -> 
  t12: lbuffer uint64 (size 12 *! getCoordinateLenU64 c) -> 
  Stack unit (requires fun h -> 
    live h t12 /\ live h p /\ live h q /\
    LowStar.Monotonic.Buffer.all_disjoint [loc t12; loc p; loc q] /\ 
    point_eval c h p /\ point_aff_eval c h q)
  (ensures fun h0 _ h1 -> 
    let u1, u2, s1, s2, _, _, _, _ = getU1HCube t12 in 
    modifies (loc t12) h0 h1 /\ (
    u1Invariant #c h0 h1 u1 p /\ u2Invariant #c h0 h1 u2 p q /\ 
    s1Invariant #c h0 h1 s1 p /\ s2Invariant #c h0 h1 s2 p q))


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
val compute_common_params_point_add: #c: curve 
  -> t12: lbuffer uint64 (size 12 *! getCoordinateLenU64 c) -> 
  Stack unit 
  (requires fun h0 -> live h0 t12 /\ (
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

  let temp = sub t12 (size 0) len in 

  let u1 = sub t12 (size 4 *! len) len in 
  let u2 = sub t12 (size 5 *! len) len in 
  let s1 = sub t12 (size 6 *! len) len in 
  let s2 = sub t12 (size 7 *! len) len in

  let h = sub t12 (size 8 *! len) len in 
  let r = sub t12 (size 9 *! len) len in 
  let uh = sub t12 (size 10 *! len) len in
  let hCube = sub t12 (size 11 *! len) len in 

  felem_sub #c u2 u1 h; 
  felem_sub #c s2 s1 r;    
  montgomery_square_buffer_dh #c h temp;
    let h1 = ST.get() in   
  montgomery_multiplication_buffer_dh #c temp u1 uh;
  montgomery_multiplication_buffer_dh #c temp h hCube;

  let prime = getPrime c in 
  lemma_mod_mul_distr_l (fromDomain #c (as_nat c h1 h) * fromDomain #c (as_nat c h1 h)) (fromDomain #c (as_nat c h1 u1)) prime;
  lemma_mod_mul_distr_l (fromDomain #c (as_nat c h1 h) * fromDomain #c (as_nat c h1 h)) (fromDomain #c (as_nat c h1 h)) prime


inline_for_extraction noextract
val computex3_point_add: #c : curve -> hCube: felem c -> uh: felem c -> 
  r: felem c -> t5: lbuffer uint64 (size 5 *! getCoordinateLenU64 c) ->  
  Stack unit 
  (requires fun h0 -> 
    live h0 hCube /\ live h0 uh /\ live h0 r /\ live h0 t5 /\
    disjoint hCube t5 /\ disjoint uh t5 /\ disjoint r t5 /\
    felem_eval c h0 hCube /\ felem_eval c h0 uh /\ felem_eval c h0 r)
  (ensures fun h0 _ h1 -> modifies (loc t5) h0 h1 /\ (
    let x3 = gsub t5 (size 0) (getCoordinateLenU64 c) in
    x3Invariant #c h0 h1 x3 r hCube uh))

let computex3_point_add #c hCube uh r t4 = 
    let h0 = ST.get() in
  [@inline_let]
  let len = getCoordinateLenU64 c in 
  
  let x3 = sub t4 (size 0) len in 
  let rSquare = sub t4 len len in 
  let rH = sub t4 (size 2 *! len) len in 
  let twoUh = sub t4 (size 3 *! len) len in 
  
  montgomery_square_buffer_dh r rSquare; 
  felem_sub rSquare hCube rH;
  multByTwo uh twoUh;
  felem_sub #c rH twoUh x3; 

  let prime = getPrime c in 
  let r = as_nat c h0 r in 

  let as_nat = as_nat c in 
  let toDomain = toDomain #c in 
  let fromDomain = fromDomain #c in 
  
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


inline_for_extraction noextract
val computeY3_point_add: #c: curve -> s1: felem c -> hCube: felem c -> uh: felem c -> r: felem c 
  -> t5: lbuffer uint64 (size 5 *! getCoordinateLenU64 c) -> 
  Stack unit 
  (requires fun h -> 
    let x3_out = gsub t5 (size 0) (getCoordinateLenU64 c) in 
    live h s1 /\ live h hCube /\ live h uh /\ live h r /\ live h t5 /\
    disjoint uh t5 /\ disjoint r t5 /\ disjoint s1 t5 /\ disjoint hCube t5 /\ 
    eq_or_disjoint s1 hCube /\ 
    felem_eval c h s1 /\ felem_eval c h hCube /\ felem_eval c h uh /\ felem_eval c h x3_out /\ felem_eval c h r)
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

  let h0 = ST.get() in

  [@inline_let]
  let len = getCoordinateLenU64 c in 
  
  let s1hCube = sub tempBuffer5 (size 2 *! getCoordinateLenU64 c) len in 
  let u1hx3 = sub tempBuffer5 (size 3 *! getCoordinateLenU64 c) len in 
  let ru1hx3 = sub tempBuffer5 (size 4 *! getCoordinateLenU64 c) len in 
  
  montgomery_multiplication_buffer_dh s1 hCube s1hCube;
  felem_sub uh x3 u1hx3; 
  montgomery_multiplication_buffer_dh u1hx3 r ru1hx3; 
  felem_sub #c ru1hx3 s1hCube y3;

  let h3 = ST.get() in 

  let prime = getPrime c in

  let s1D = fromDomain #c (as_nat c h0 s1) in 
  let hCubeD = fromDomain #c (as_nat c h0 hCube) in 
  let uhD = fromDomain #c (as_nat c h0 uh) in 
  let x3D = fromDomain #c (as_nat c h0 x3) in 
  let rD = fromDomain #c (as_nat c h0 r) in 

  calc (==)
  {
    toDomain #c (((uhD - x3D) % prime * rD % prime  - (s1D * hCubeD % prime)) % getPrime c);
    (==) {lemma_mod_mul_distr_l (uhD - x3D) rD prime}
    toDomain #c (((uhD - x3D) * rD % prime  - (s1D * hCubeD % prime)) % getPrime c);
    (==) {_ by (canon())}
    toDomain #c (((uhD - x3D) * rD % prime  - s1D * hCubeD % prime) % getPrime c);
    (==) {lemma_mod_sub_distr ((uhD - x3D) * rD % prime) (s1D * hCubeD) prime}
    toDomain #c (((uhD - x3D) * rD % prime - s1D * hCubeD) % getPrime c);
    (==) {lemma_mod_add_distr (-s1D * hCubeD) ((uhD - x3D) * rD) prime}
    toDomain #c (((uhD - x3D) * rD - s1D * hCubeD) % getPrime c);
  }



inline_for_extraction noextract 
val computeZ3_point_add: #c: curve -> p: point c ->
  h: felem c -> t5: lbuffer uint64 (size 5 *! getCoordinateLenU64 c) -> 
  Stack unit 
  (requires fun h0 -> 
    live h0 t5 /\ live h0 p /\ live h0 h /\ 
    disjoint t5 p /\ disjoint t5 h /\
    point_eval c h0 p /\  felem_eval c h0 h)
  (ensures fun h0 _ h1 -> modifies (loc t5) h0 h1 /\ (
    let len = getCoordinateLenU64 c in 
    let z1 = getZ p in
    let x3, y3, z3 = getXYZ #c t5 in 
    as_nat c h0 x3 == as_nat c h1 x3 /\
    as_nat c h0 y3 == as_nat c h1 y3 /\
    z3Invariant #c h0 h1 z3 z1 h))

let computeZ3_point_add #c p h t5 = 
    let h0 = ST.get() in 
  [@inline_let]
  let len = getCoordinateLenU64 c in 

  let z1 = sub p (size 2 *! len) len in 
  let z3 = sub t5 (size 2 *! len) len in 
  
  let z1z2 = sub t5 (size 3 *! len) len in 

  montgomery_multiplication_buffer_by_one_dh #c z1 z1z2;
  montgomery_multiplication_buffer_dh #c z1z2 h z3;

  let h1 = ST.get() in 

  let hD = fromDomain #c (as_nat c h0 h) in 
  let z1D = fromDomain #c (as_nat c h0 z1) in 
  
  let prime = getPrime c in 
  let k = modp_inv2_prime (pow2 (getPower c)) prime in 


  calc (==)
  {
    as_nat c h1 z3;
    (==) {}
    toDomain #c (fromDomain #c z1D * hD % prime);
    (==) {lemmaFromDomain #c #DH z1D}
    toDomain #c (z1D * (1 * k) % prime * hD % prime);
    (==) {lemma_mod_mul_distr_r z1D (1 * k) prime}
    toDomain #c (z1D * (1 * k % prime) % prime * hD % prime);
    (==) {lemmaFromDomain #c #DH 1}
    toDomain #c (z1D * fromDomain #c 1 % prime * hD % prime);
    (==) {lemma_mod_mul_distr_l (z1D * fromDomain #c 1) hD prime}
    toDomain #c (z1D * fromDomain #c 1 * hD % prime);
    
  }


inline_for_extraction noextract
val copy_result_point_add: #c: curve 
  -> t5: lbuffer uint64 (size 5 *! (getCoordinateLenU64 c)) 
  -> p: point c -> q: pointAffine c -> result: point c ->
  Stack unit 
  (requires fun h -> live h t5 /\ live h p /\ live h q /\ live h result /\
    eq_or_disjoint p result /\ disjoint t5 result /\ 
    point_aff_eval c h q /\ point_eval c h p /\ (
    
    let len = getCoordinateLenU64 c in 
    let x3_out = gsub t5 (size 0) len in 
    let y3_out = gsub t5 len len in 
    let z3_out = gsub t5 (size 2 *! len) len in 
    felem_eval c h x3_out /\ felem_eval c h y3_out /\ felem_eval c h z3_out /\ 
    LowStar.Monotonic.Buffer.all_disjoint [loc t5; loc p; loc q]))
  (ensures fun h0 _ h1 -> 
    let x3_out, y3_out, z3_out = getXYZ #c t5 in 
    modifies (loc t5 |+| loc result) h0 h1 /\ point_eval c h1 result /\ (
    if isPointAtInfinityAffine (point_affine_as_nat c h0 q) then
      point_x_as_nat c h1 result == point_x_as_nat c h0 p /\
      point_y_as_nat c h1 result == point_y_as_nat c h0 p /\ 
      point_z_as_nat c h1 result == point_z_as_nat c h0 p
    else if point_z_as_nat c h0 p = 0 then 
      point_x_as_nat c h1 result == point_affine_x_as_nat c h0 q /\
      point_y_as_nat c h1 result == point_affine_y_as_nat c h0 q /\ 
      point_z_as_nat c h1 result == 1
    else 
      point_x_as_nat c h1 result == as_nat c h0 x3_out /\ 
      point_y_as_nat c h1 result == as_nat c h0 y3_out /\ 
      point_z_as_nat c h1 result == as_nat c h0 z3_out))


let copy_result_point_add #c t5 p q result = 
  let h0 = ST.get() in 
  [@inline_let]
  let len = getCoordinateLenU64 c in 

  let x3_out = sub t5 (size 0) len in 
  let y3_out = sub t5 len len in 
  let z3_out = sub t5 (size 2 *! len) len in 

  let temp = sub t5 (size 3 *! len) len in 

  copy_point_conditional x3_out y3_out z3_out q p temp;
  copy_point_conditional1 x3_out y3_out z3_out p q;

  copy (sub result (size 0) len) x3_out;
  copy (sub result len len) y3_out;
  copy (sub result (size 2 *! len) len) z3_out



inline_for_extraction noextract
val computeXYZ: #c: curve -> result: point c 
  -> p: point c -> q: pointAffine c 
  -> u1: felem c -> u2: felem c -> s1: felem c -> s2: felem c 
  -> r: felem c -> h: felem c -> uh: felem c -> hCube: felem c 
  -> t5 : lbuffer uint64 (size 5 *! getCoordinateLenU64 c) -> 
  Stack unit 
  (requires fun h0 -> 
    live h0 result /\ live h0 t5 /\ live h0 p /\ live h0 q /\ live h0 u1 /\ live h0 u2 /\ live h0 s1 /\ live h0 s2 /\ 
    live h0 r /\ live h0 h /\ live h0 uh /\ live h0 hCube /\
    point_eval c h0 p /\ point_aff_eval c h0 q /\ 
    eq_or_disjoint p q /\ eq_or_disjoint s1 hCube /\ 
    felem_eval c h0 r /\ felem_eval c h0 s1 /\ felem_eval c h0 h /\ 
    uhInvariant #c h0 uh h u1 /\ hCubeInvariant #c h0 hCube h /\
    
    eq_or_disjoint p result /\ disjoint result t5 /\ disjoint p q /\ disjoint hCube t5 /\ disjoint uh t5 /\ disjoint r t5 /\ 
    disjoint t5 s1 /\ disjoint t5 h /\ disjoint t5 p /\ disjoint t5 q)
  (ensures fun h0 _ h1 -> modifies (loc t5 |+| loc result) h0 h1 /\ point_eval c h1 result /\ (
    let prime = getPrime c in 

    let x3, y3, z3 = point_x_as_nat c h1 result, point_y_as_nat c h1 result, point_z_as_nat c h1 result in
    let pX, pY, pZ = point_x_as_nat c h0 p, point_y_as_nat c h0 p, point_z_as_nat c h0 p in 
    let qX, qY = point_affine_x_as_nat c h0 q, point_affine_y_as_nat c h0 q in 

    let pxD, pyD, pzD = fromDomain #c pX, fromDomain #c pY, fromDomain #c pZ in 
    let qxD, qyD = fromDomain #c qX, fromDomain #c qY in 
    let x3D, y3D, z3D = fromDomain #c x3, fromDomain #c y3, fromDomain #c z3 in 

    let rD = fromDomain #c (as_nat c h0 r) in  
    let hD = fromDomain #c (as_nat c h0 h) in 
    let s1D = fromDomain #c (as_nat c h0 s1) in 
    let u1D = fromDomain #c (as_nat c h0 u1) in  

    if qxD = 0 && qyD = 0 then 
      x3D == pxD /\ y3D == pyD /\ z3D == pzD
    else if pzD = 0 then 
      x3D == qxD /\  y3D == qyD /\ z3D == fromDomain #c 1
    else 
      x3 == toDomain #c ((rD * rD - hD * hD * hD - 2 * hD * hD * u1D) % prime) /\ 
      y3 == toDomain #c (((hD * hD * u1D - fromDomain #c x3) * rD - s1D * hD * hD * hD) % prime) /\
      z3 == toDomain #c (pzD * fromDomain #c 1 * hD % prime)))

let computeXYZ #c result p q u1 u2 s1 s2 r h uh hCube t5 = 
    let h0 = ST.get() in 
  computex3_point_add #c hCube uh r t5; 
  computeY3_point_add #c s1 hCube uh r t5; 
    let h1 = ST.get() in 
    lemma_coord_eval c h0 h1 p; 
    lemma_coord_affine_eval c h0 h1 q; 
  computeZ3_point_add #c p h t5;
    let h2 = ST.get() in
    lemma_coord_eval c h1 h2 p;
    lemma_coord_affine_eval c h1 h2 q; 
  copy_result_point_add t5 p q result;
    let h3 = ST.get() in 
    lemma_point_add_if #c p q result t5 u1 u2 s1 s2 r h uh hCube h0 h2 h3


inline_for_extraction noextract
val _point_add_if_second_branch_impl: #c: curve -> result: point c 
  -> p: point c -> q: pointAffine c 
  -> x3hCube: lbuffer uint64 (size 12 *! getCoordinateLenU64 c) 
  -> t5 : lbuffer uint64 (size 5 *! getCoordinateLenU64 c) -> 
  Stack unit (requires fun h0 -> 
    let  u1, u2, s1, s2, h, r, uh, hCube = getU1HCube x3hCube in
    live h0 result /\ live h0 p /\ live h0 q /\ live h0 x3hCube /\ live h0 t5 /\ 
    point_eval c h0 p /\ point_aff_eval c h0 q /\
    eq_or_disjoint p result /\ disjoint result t5 /\ disjoint p q /\
    disjoint t5 x3hCube /\  disjoint t5 p /\ disjoint t5 q /\
    felem_eval c h0 r /\ felem_eval c h0 s1 /\ felem_eval c h0 h /\ 
    uhInvariant #c h0 uh h u1 /\ hCubeInvariant #c h0 hCube h)
  (ensures fun h0 _ h1 -> modifies (loc t5 |+| loc result) h0 h1 /\ point_eval c h1 result /\ (
    let prime = getPrime c in 
    let  u1, u2, s1, s2, h, r, uh, hCube = getU1HCube x3hCube in 
  
    let x3, y3, z3 = point_x_as_nat c h1 result, point_y_as_nat c h1 result, point_z_as_nat c h1 result in
    let pX, pY, pZ = point_x_as_nat c h0 p, point_y_as_nat c h0 p, point_z_as_nat c h0 p in 
    let qX, qY, qZ = point_affine_x_as_nat c h0 q, point_affine_y_as_nat c h0 q, 1 in 

    let pxD, pyD, pzD = fromDomain #c pX, fromDomain #c pY, fromDomain #c pZ in 
    let qxD, qyD, qzD = fromDomain #c qX, fromDomain #c qY, fromDomain #c qZ in 
    let x3D, y3D, z3D = fromDomain #c x3, fromDomain #c y3, fromDomain #c z3 in 

    let rD = fromDomain #c (as_nat c h0 r) in  
    let hD = fromDomain #c (as_nat c h0 h) in 
    let s1D = fromDomain #c (as_nat c h0 s1) in 
    let u1D = fromDomain #c (as_nat c h0 u1) in  
    
    if qxD = 0 && qyD = 0 then 
      x3D == pxD /\ y3D == pyD /\ z3D == pzD
    else if pzD = 0 then 
      x3D == qxD /\  y3D == qyD /\ z3D == qzD
    else 
      x3 == toDomain #c ((rD * rD - hD * hD * hD - 2 * hD * hD * u1D) % prime) /\ 
      y3 == toDomain #c (((hD * hD * u1D - fromDomain  #c x3) * rD - s1D * hD * hD * hD) % prime) /\
      z3 == toDomain #c (pzD * qzD * hD % prime)))


let _point_add_if_second_branch_impl #c result p q x3hCube t5 = 
  [@inline_let]
  let len = getCoordinateLenU64 c in 
  let h0 = ST.get() in 

  l0 #c x3hCube h0;

  let h = sub x3hCube (size 8 *! len) len in 
  let r = sub x3hCube (size 9 *! len) len in 
  let uh = sub x3hCube (size 10 *! len) len in 
  let hCube = sub x3hCube (size 11 *! len) len in 

  let u1 = sub x3hCube (size 4 *! len) len in 
  let u2 = sub x3hCube (size 5 *! len) len in 
  let s1 = sub x3hCube (size 6 *! len) len in 
  let s2 = sub x3hCube (size 7 *! len) len in 

  computeXYZ result p q u1 u2 s1 s2 r h uh hCube t5


inline_for_extraction noextract
val _point_add0: #c: curve -> p: point c -> q: pointAffine c 
  -> t12: lbuffer uint64 (size 12 *! getCoordinateLenU64 c) -> 
  Stack unit 
  (requires fun h0 -> live h0 p /\ live h0 q /\ live h0 t12 /\
    LowStar.Monotonic.Buffer.all_disjoint [loc t12; loc p; loc q] /\ 
    point_eval c h0 p /\ point_aff_eval c h0 q)
  (ensures fun h0 _ h1 -> 
    modifies (loc t12) h0 h1 /\ (
    let u1, u2, s1, s2, h, r, uh, hCube = getU1HCube t12 in  
    u1Invariant #c h0 h1 u1 p /\ u2Invariant #c h0 h1 u2 p q /\ 
    s1Invariant #c h0 h1 s1 p /\ s2Invariant #c h0 h1 s2 p q /\ 
    hInvariant #c h1 h u1 u2 /\ rInvariant #c h1 r s1 s2 /\
    uhInvariant #c h1 uh h u1 /\ hCubeInvariant #c h1 hCube h))
      
let _point_add0 #c p q t12 = 
  [@inline_let]
  let len = getCoordinateLenU64 c in 
  let h0 = ST.get() in 
  
  move_from_jacobian_coordinates p q t12;
  compute_common_params_point_add t12;
  let h1 = ST.get() in 
  lemma_coord_eval c h0 h1 p;
  lemma_coord_affine_eval c h0 h1 q 


inline_for_extraction noextract
val point_add_mixed_: #c: curve -> p: point c -> q: pointAffine c -> result: point c 
  -> tempBuffer: lbuffer uint64 (size 17 *! getCoordinateLenU64 c) -> 
  Stack unit (requires fun h -> 
    live h p /\ live h q /\ live h result /\ live h tempBuffer /\ 
    eq_or_disjoint q result /\ disjoint p q /\ disjoint p tempBuffer /\ 
    disjoint q tempBuffer /\ disjoint p result /\ disjoint result tempBuffer /\  
    point_eval c h p /\ point_aff_eval c h q)
  (ensures fun h0 _ h1 -> modifies (loc tempBuffer |+| loc result) h0 h1 /\ point_eval c h1 result /\ (
    let qX, qY, qZ = point_affine_x_as_nat c h0 q, point_affine_y_as_nat c h0 q, 1 in 
    let qD = fromDomainPoint #c #DH (qX, qY, qZ) in 
    fromDomainPoint #c #DH (point_as_nat c h1 result) == 
    _point_add_mixed #c (fromDomainPoint #c #DH (point_as_nat c h0 p)) qD))


let point_add_mixed_ #c p q result tempBuffer = 
  let h0 = ST.get() in 
  let t12 = sub tempBuffer (size 0) (size 12 *! getCoordinateLenU64 c) in 
  let t5 = sub tempBuffer (size 12 *! getCoordinateLenU64 c) (size 5 *! getCoordinateLenU64 c) in 
  
  _point_add0 #c p q t12;
  let h1 = ST.get() in 
    lemma_coord_eval c h0 h1 p;
    lemma_coord_affine_eval c h0 h1 q;
  _point_add_if_second_branch_impl result p q t12 t5;

  let h2 = ST.get() in 

  let prime = getPrime c in 

  let x3, y3, z3 = point_x_as_nat c h2 result, point_y_as_nat c h2 result, point_z_as_nat c h2 result in
  let pX, pY, pZ = point_x_as_nat c h0 p, point_y_as_nat c h0 p, point_z_as_nat c h0 p in 
  let qX, qY, qZ = point_affine_x_as_nat c h0 q, point_affine_y_as_nat c h0 q, 1 in 

  let pxD, pyD, pzD = fromDomain #c pX, fromDomain #c pY, fromDomain #c pZ in 
  let qxD, qyD, qzD = fromDomain #c qX, fromDomain #c qY, fromDomain #c qZ in 
  let x3D, y3D, z3D = fromDomain #c x3, fromDomain #c y3, fromDomain #c z3 in 

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
    (((hD * hD * u1D - fromDomain  #c x3) * rD - s1D * hD * hD * hD) % prime);
    (==) {_ by (canon())}
    (rD * (u1D * (hD * hD) - fromDomain  #c x3) - s1D * (hD * hD * hD)) % prime;
  };

  calc (==)
  {
    (pzD * qzD * hD % prime);
    (==) {_ by (canon())}
    (hD * pzD * qzD) % prime;
  };

  assert( 
    let z1z1 = pzD * pzD in 
    let z2z2 = qzD * qzD in 
    let u1D = pxD * z2z2 % prime in
    let u2D = qxD * z1z1 % prime in    

    let s1D = pyD * qzD * (qzD * qzD) % prime in 
    let s2D = qyD * pzD * (pzD * pzD) % prime in 
      
    let hD = (u2D - u1D) % prime in
    let rD = (s2D - s1D) % prime in
    
    if qxD = 0 && qyD = 0 then 
      x3D == pxD /\ y3D == pyD /\ z3D == pzD
    else if pzD = 0 then 
      x3D == qxD /\  y3D == qyD /\ z3D == qzD
    else 
      x3D == (((rD * rD) - (hD * hD * hD) - (2 * u1D * (hD * hD))) % prime) /\ 
      y3D == ((rD * (u1D * (hD * hD) - fromDomain  #c x3) - s1D * (hD * hD * hD)) % prime) /\
      z3D == (hD * pzD * qzD % prime))

[@CInline]
val point_add_mixed_p256: p: point P256 -> q: pointAffine P256 -> result: point P256
  -> tempBuffer: lbuffer uint64 (size 17 *! getCoordinateLenU64 P256) -> 
  Stack unit (requires fun h -> 
    live h p /\ live h q /\ live h result /\ live h tempBuffer /\ 
    eq_or_disjoint q result /\ disjoint p q /\ disjoint p tempBuffer /\ 
    disjoint q tempBuffer /\ disjoint p result /\ disjoint result tempBuffer /\  
    point_eval P256 h p /\ point_aff_eval P256 h q)
  (ensures fun h0 _ h1 -> modifies (loc tempBuffer |+| loc result) h0 h1 /\ point_eval P256 h1 result /\ (
    let qX, qY, qZ = point_affine_x_as_nat P256 h0 q, point_affine_y_as_nat P256 h0 q, 1 in 
    let qD = fromDomainPoint #P256 #DH (qX, qY, qZ) in 
    fromDomainPoint #P256 #DH (point_as_nat P256 h1 result) == 
    _point_add_mixed #P256 (fromDomainPoint #P256 #DH (point_as_nat P256 h0 p)) qD))


let point_add_mixed_p256 = point_add_mixed_ #P256


[@CInline]
val point_add_mixed_p384: p: point P384 -> q: pointAffine P384 -> result: point P384
  -> tempBuffer: lbuffer uint64 (size 17 *! getCoordinateLenU64 P384) -> 
  Stack unit (requires fun h -> 
    live h p /\ live h q /\ live h result /\ live h tempBuffer /\ 
    eq_or_disjoint q result /\ disjoint p q /\ disjoint p tempBuffer /\ 
    disjoint q tempBuffer /\ disjoint p result /\ disjoint result tempBuffer /\  
    point_eval P384 h p /\ point_aff_eval P384 h q)
  (ensures fun h0 _ h1 -> modifies (loc tempBuffer |+| loc result) h0 h1 /\ point_eval P384 h1 result /\ (
    let qX, qY, qZ = point_affine_x_as_nat P384 h0 q, point_affine_y_as_nat P384 h0 q, 1 in 
    let qD = fromDomainPoint #P384 #DH (qX, qY, qZ) in 
    fromDomainPoint #P384 #DH (point_as_nat P384 h1 result) == 
    _point_add_mixed #P384 (fromDomainPoint #P384 #DH (point_as_nat P384 h0 p)) qD))


let point_add_mixed_p384 = point_add_mixed_ #P384


(* [@CInline]
val point_add_mixed_generic: p: point Default -> q: pointAffine Default -> result: point Default
  -> tempBuffer: lbuffer uint64 (size 17 *! getCoordinateLenU64 Default) -> 
  Stack unit (requires fun h -> 
    live h p /\ live h q /\ live h result /\ live h tempBuffer /\ 
    eq_or_disjoint q result /\ disjoint p q /\ disjoint p tempBuffer /\ 
    disjoint q tempBuffer /\ disjoint p result /\ disjoint result tempBuffer /\  
    point_eval Default h p /\ point_aff_eval Default h q)
  (ensures fun h0 _ h1 -> modifies (loc tempBuffer |+| loc result) h0 h1 /\ point_eval Default h1 result /\ (
    let qX, qY, qZ = point_affine_x_as_nat Default h0 q, point_affine_y_as_nat Default h0 q, 1 in 
    let qD = fromDomainPoint #Default #DH (qX, qY, qZ) in 
    fromDomainPoint #Default #DH (point_as_nat Default h1 result) == 
    _point_add_mixed #Default (fromDomainPoint #Default #DH (point_as_nat Default h0 p)) qD))


let point_add_mixed_generic = point_add_mixed_ #Default
 *)


let point_add_mixed #c p q result tempBuffer = 
  match c with 
  |P256 -> point_add_mixed_p256 p q result tempBuffer
  |P384 -> point_add_mixed_p384 p q result tempBuffer
  (* |Default -> point_add_mixed_generic p q result tempBuffer *)
