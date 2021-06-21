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
open Hacl.Spec.EC.Definition


friend Hacl.Impl.EC.PointAdd
open Hacl.Spec.MontgomeryMultiplication
open FStar.Mul

open Hacl.Impl.P.PointAddMixed.Aux

#set-options "--z3rlimit 300 --fuel 0 --ifuel 0"


(* during the precomputation of points we want to express a point at infinity. We present is as a point such that both coordinates are equal to zero *)

inline_for_extraction noextract 
val pointAffineIsNotZero: #c: curve ->
  #buf_type: buftype -> p: lbuffer_t buf_type uint64 (size 2 *! getCoordinateLenU64 c) -> Stack uint64
  (requires fun h -> live h p)
  (ensures fun h0 r h1 -> modifies0 h0 h1 /\ (
    let len = getCoordinateLenU64 c in 
    let x = lseq_as_nat (as_seq h0 (gsub p (size 0) len)) in 
    let y = lseq_as_nat (as_seq h0 (gsub p len len)) in 
    if isPointAtInfinityAffine (x, y) then uint_v r = pow2 64 - 1 else uint_v r == 0))


let pointAffineIsNotZero #c p = 
  let h0 = ST.get() in 
  
  let len = getCoordinateLenU64 c in 
  let x = sub p (size 0) len in 
  let y = sub p len len in 

  let xZero = isZero_uint64_CT #c x in 
  let yZero = isZero_uint64_CT #c y in 

  logand_lemma xZero yZero;
  logand xZero yZero


val copy_point_conditional: #c: curve -> result: point c -> p: point c -> mask: point c ->
  Stack unit
  (requires fun h -> point_eval c h mask /\ point_eval c h p /\ point_eval c h result /\
    live h result /\ live h p /\ live h mask /\ 
    LowStar.Monotonic.Buffer.all_disjoint [loc result; loc p; loc mask])
  (ensures fun h0 _ h1 -> modifies (loc result) h0 h1 /\ point_eval c h1 result /\ (
    let mask = point_z_as_nat c h0 mask in 
    if mask = 0 then
      point_x_as_nat c h1 result == point_x_as_nat c h0 p /\
      point_y_as_nat c h1 result == point_y_as_nat c h0 p /\ 
      point_z_as_nat c h1 result == point_z_as_nat c h0 p
    else 
      point_x_as_nat c h1 result == point_x_as_nat c h0 result /\ 
      point_y_as_nat c h1 result == point_y_as_nat c h0 result /\ 
      point_z_as_nat c h1 result == point_z_as_nat c h0 result))

let copy_point_conditional #c result p mask = 
  let len = getCoordinateLenU64 c in
  
  let mask = isZero_uint64_CT #c (sub mask (size 2 *! len) len) in 

  let outX = sub result (size 0) len in 
  let outY = sub result len len in 
  let outZ = sub result (size 2 *! len) len in 

  let pX = sub p (size 0) len in 
  let pY = sub p len len in 
  let pZ = sub p (size 2 *! len) len in 

  copy_conditional #c outX pX mask;
  copy_conditional #c outY pY mask;
  copy_conditional #c outZ pZ mask
  

inline_for_extraction noextract 
val _move_from_jacobian_coordinates: #c: curve -> u1: felem c -> u2: felem c -> 
  s1: felem c -> s2: felem c -> p: point c -> q: pointAffine c -> 
  tempBuffer4: lbuffer uint64 (size 4 *! getCoordinateLenU64 c) -> 
  Stack unit (requires fun h ->  
    live h u1 /\ live h u2 /\ live h s1 /\ live h s2 /\ live h tempBuffer4 /\ live h p /\ 
    live h q /\ point_eval c h p /\  point_aff_eval c h q /\
    LowStar.Monotonic.Buffer.all_disjoint [loc tempBuffer4; loc p; loc q; loc u1; loc u2; loc s1; loc s2])
  (ensures fun h0 _ h1 ->  
    modifies (loc u1 |+| loc u2 |+| loc s1 |+| loc s2 |+| loc tempBuffer4) h0 h1 (*/\
    u1Invariant #c h0 h1 u1 p q /\
    u2Invariant #c h0 h1 u2 p q /\ 
    s1Invariant #c h0 h1 s1 p q /\
    s2Invariant #c h0 h1 s2 p q *))


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

   upd z2Square (size 0) (u64 0x000000300000000);
   upd z2Square (size 1) (u64 0x00000001FFFFFFFE);
   upd z2Square (size 2) (u64 0xFFFFFFFD00000002);
   upd z2Square (size 3) (u64 0xFFFFFFFE00000003);

    upd z2Cube (size 0) (u64 0x0000000CFFFFFFF7);
    upd z2Cube (size 1) (u64 0xFFFFFFF800000007); 
    upd z2Cube (size 2) (u64 0xFFFFFFFB0000000F);
    upd z2Cube (size 3) (u64 0x00000005FFFFFFFF);


  (* montgomery_square_buffer_dh #c qZ z2Square;  *)
  montgomery_square_buffer_dh #c pZ z1Square;

  (* montgomery_multiplication_buffer_dh #c z2Square qZ z2Cube; *)
  montgomery_multiplication_buffer_dh #c z1Square pZ z1Cube;

  montgomery_multiplication_buffer_dh #c z2Square pX u1;
  montgomery_multiplication_buffer_dh #c z1Square qX u2;
    
  montgomery_multiplication_buffer_dh #c z2Cube pY s1;
  montgomery_multiplication_buffer_dh #c z1Cube qY s2;

  let prime = getPrime c in 
  
  let fromDomain = fromDomain #c in 
  let toDomain = toDomain #c in   
  let as_nat = as_nat c in 

  let pxD = fromDomain (as_nat h0 pX) in 
  let qxD = fromDomain (as_nat h0 qX) in 

  let pyD = fromDomain (as_nat h0 pY) in 
  let qyD = fromDomain (as_nat h0 qY) in 

  let pzD = fromDomain (as_nat h0 pZ) in 
  let qzD = fromDomain 1 in 


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
val move_from_jacobian_coordinates_mixed: #c: curve -> p: point c -> q: pointAffine c -> 
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


let move_from_jacobian_coordinates_mixed #c p q t12 = 
  [@inline_let]
  let len = getCoordinateLenU64 c in   
  
  let t4 = sub t12 (size 0) (size 4 *! len) in 
   
  let u1 = sub t12 (size 4 *! len) len in 
  let u2 = sub t12 (size 5 *! len) len in 
  let s1 = sub t12 (size 6 *! len) len in 
  let s2 = sub t12 (size 7 *! len) len in 

  _move_from_jacobian_coordinates #c u1 u2 s1 s2 p q t4



inline_for_extraction noextract 
val computeZ3_point_add_mixed: #c: curve -> z3: felem  c -> z1: felem c -> 
  h: felem c -> tempBuffer: felem c -> 
  Stack unit
  (requires fun h0 -> 
    live h0 z3 /\ live h0 z1 /\ live h0 h /\  live h0 tempBuffer /\
    disjoint z3 z1 /\ disjoint z1 tempBuffer /\ disjoint tempBuffer h /\ disjoint h z3 /\
    felem_eval c h0 z1 /\ felem_eval c h0 h)
  (ensures fun h0 _ h1 -> modifies (loc z3 |+| loc tempBuffer) h0 h1 /\ (
    let z1D = fromDomain_ #c #DH (as_nat c h0 z1) in 
    let hD = fromDomain_ #c #DH (as_nat c h0 h) in 
    as_nat c h1 z3 == toDomain_ #c #DH (z1D * hD % getPrime c)))  


let computeZ3_point_add_mixed #c z3 z1 h tempBuffer =    
  let len = getCoordinateLenU64 c in 
  let h0 = ST.get() in 
  let z1z2 = sub tempBuffer (size 0) len in
  montgomery_multiplication_buffer_by_one_dh z1 z1z2;
    let h1 = ST.get() in 
  montgomery_multiplication_buffer_dh z1z2 h z3;
    let h2 = ST.get() in 

  let z1D = fromDomain_ #c #DH (as_nat c h0 z1) in 
  let hD = fromDomain_ #c #DH (as_nat c h0 h) in 
  assert(as_nat c h1 z1z2 = z1D);
  assert(as_nat c h2 z3 = toDomain_ #c #DH (fromDomain_ #c #DH z1D * hD % getPrime c));
  
  admit()


inline_for_extraction noextract
val cmovznz_one_mm: #c: curve -> out: felem c -> mask: uint64 -> tempBuffer: felem c -> Stack unit
  (requires fun h -> live h out /\ live h tempBuffer /\ disjoint out tempBuffer /\
    (uint_v mask == 0 \/ uint_v mask = pow2 64 - 1))
  (ensures fun h0 _ h1 -> modifies (loc out |+| loc tempBuffer) h0 h1 /\ (
    if v mask = 0 then 
      as_nat c h1 out == as_nat c h0 out 
    else 
      as_nat c h1 out == 1))

let cmovznz_one_mm #c out mask tempBuffer = 
  uploadOneImpl tempBuffer;
  copy_conditional out tempBuffer mask


inline_for_extraction noextract 
val copy_point_conditional_affine_to_result: #c: curve -> #buf_type : buftype -> out: point c
  -> q: lbuffer_t buf_type uint64 (size 8)
  -> maskPoint: point c
  -> tempBuffer: felem c 
  -> Stack unit 
  (requires fun h -> live h out /\ live h q /\ live h maskPoint /\ disjoint q out /\ eq_or_disjoint out maskPoint)
  (ensures fun h0 _ h1 -> modifies (loc out) h0 h1)


let copy_point_conditional_affine_to_result #c out q maskPoint tempBuffer = 
  let h0 = ST.get() in 
  
  let pZ = sub maskPoint (size 8) (size 4) in 
  let mask = isZero_uint64_CT #c pZ in

  let xOut = sub out (size 0) (size 4) in 
  let yOut = sub out (size 4) (size 4) in 
  let zOut = sub out (size 8) (size 4) in 
  
  let qX = sub q (size 0) (size 4) in 
  let qY = sub q (size 4) (size 4) in 


   let qX = const_to_lbuffer qX in 
   let qY = const_to_lbuffer qY in 

  copy_conditional #c xOut qX mask;
  copy_conditional #c yOut qY mask;
  cmovznz_one_mm #c zOut mask tempBuffer;
  
(*
  lemma_multiplication_not_mod_prime (as_nat h0 pZ); *)
  lemmaFromDomain #c #DH (as_nat c h0 pZ)


inline_for_extraction noextract
val computeXYZ: #c: curve -> result: point c 
  -> p: point c -> q: point c 
  -> u1: felem c -> u2: felem c -> s1: felem c -> s2: felem c 
  -> r: felem c -> h: felem c -> uh: felem c -> hCube: felem c 
  -> t5 : lbuffer uint64 (size 5 *! getCoordinateLenU64 c) -> 
  Stack unit 
  (requires fun h0 -> 
    live h0 result /\ live h0 t5 /\ live h0 p /\ live h0 q /\ live h0 u1 /\ live h0 u2 /\ live h0 s1 /\ live h0 s2 /\ 
    live h0 r /\ live h0 h /\ live h0 uh /\ live h0 hCube /\
    point_eval c h0 p /\ point_eval c h0 q /\ 
    eq_or_disjoint p q /\ eq_or_disjoint s1 hCube /\ 
    felem_eval c h0 r /\ felem_eval c h0 s1 /\ felem_eval c h0 h /\ 
    uhInvariant #c h0 uh h u1 /\ hCubeInvariant #c h0 hCube h /\
    
    eq_or_disjoint p result /\ disjoint result t5 /\ disjoint p q /\ disjoint hCube t5 /\ disjoint uh t5 /\ disjoint r t5 /\ 
    disjoint t5 s1 /\ disjoint t5 h /\ disjoint t5 p /\ disjoint t5 q)
  (ensures fun h0 _ h1 -> modifies (loc t5 |+| loc result) h0 h1 /\ point_eval c h1 result /\ (
    let prime = getPrime c in 

    let x3, y3, z3 = point_x_as_nat c h1 result, point_y_as_nat c h1 result, point_z_as_nat c h1 result in
    let pX, pY, pZ = point_x_as_nat c h0 p, point_y_as_nat c h0 p, point_z_as_nat c h0 p in 
    let qX, qY, qZ = point_x_as_nat c h0 q, point_y_as_nat c h0 q, point_z_as_nat c h0 q in 

    let pxD, pyD, pzD = fromDomain #c pX, fromDomain #c pY, fromDomain #c pZ in 
    let qxD, qyD, qzD = fromDomain #c qX, fromDomain #c qY, fromDomain #c qZ in 
    let x3D, y3D, z3D = fromDomain #c x3, fromDomain #c y3, fromDomain #c z3 in 

    let rD = fromDomain #c (as_nat c h0 r) in  
    let hD = fromDomain #c (as_nat c h0 h) in 
    let s1D = fromDomain #c (as_nat c h0 s1) in 
    let u1D = fromDomain #c (as_nat c h0 u1) in  

    point_eval c h1 result /\ (
    if qzD = 0 then 
      x3D == pxD /\ y3D == pyD /\ z3D == pzD
    else if pzD = 0 then 
      x3D == qxD /\  y3D == qyD /\ z3D == qzD
    else 
      x3 == toDomain #c ((rD * rD - hD * hD * hD - 2 * hD * hD * u1D) % prime) /\ 
      y3 == toDomain #c (((hD * hD * u1D - fromDomain #c x3) * rD - s1D * hD * hD * hD) % prime) /\
      z3 == toDomain #c (pzD * qzD * hD % prime))))

let computeXYZ #c result p q u1 u2 s1 s2 r h uh hCube t5 = 
    let h0 = ST.get() in
    let h0 = ST.get() in 
  Hacl.Impl.EC.PointAdd.computex3_point_add #c hCube uh r t5; 
  Hacl.Impl.EC.PointAdd.computeY3_point_add #c s1 hCube uh r t5;
    let h1 = ST.get() in 
    lemma_coord_eval c h0 h1 p;
    lemma_coord_eval c h0 h1 q;
  computeZ3_point_add_mixed #c p q h t5;
    let h2 = ST.get() in
    lemma_coord_eval c h1 h2 p;
    lemma_coord_eval c h1 h2 q; 
  copy_point_conditional_affine_to_result result q p t5; 
  copy_point_conditional result p q


inline_for_extraction noextract
val _point_add_if_second_branch_impl: #c: curve -> result: point c 
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
    uhInvariant #c h0 uh h u1 /\ hCubeInvariant #c h0 hCube h)
  (ensures fun h0 _ h1 -> modifies (loc t5 |+| loc result) h0 h1 /\ point_eval c h1 result /\ (
    let prime = getPrime c in 

    let  u1, u2, s1, s2, h, r, uh, hCube = getU1HCube x3hCube in 
  
    let x3, y3, z3 = point_x_as_nat c h1 result, point_y_as_nat c h1 result, point_z_as_nat c h1 result in
    let pX, pY, pZ = point_x_as_nat c h0 p, point_y_as_nat c h0 p, point_z_as_nat c h0 p in 
    let qX, qY, qZ = point_x_as_nat c h0 q, point_y_as_nat c h0 q, point_z_as_nat c h0 q in 

    let pxD, pyD, pzD = fromDomain #c pX, fromDomain #c pY, fromDomain #c pZ in 
    let qxD, qyD, qzD = fromDomain #c qX, fromDomain #c qY, fromDomain #c qZ in 
    let x3D, y3D, z3D = fromDomain #c x3, fromDomain #c y3, fromDomain #c z3 in 

    let rD = fromDomain #c (as_nat c h0 r) in  
    let hD = fromDomain #c (as_nat c h0 h) in 
    let s1D = fromDomain #c (as_nat c h0 s1) in 
    let u1D = fromDomain #c (as_nat c h0 u1) in  

    point_eval c h1 result /\ (
    if qzD = 0 then 
      x3D == pxD /\ y3D == pyD /\ z3D == pzD
    else if pzD = 0 then 
      x3D == qxD /\  y3D == qyD /\ z3D == qzD
    else 
      x3 == toDomain #c ((rD * rD - hD * hD * hD - 2 * hD * hD * u1D) % prime) /\ 
      y3 == toDomain #c (((hD * hD * u1D - fromDomain  #c x3) * rD - s1D * hD * hD * hD) % prime) /\
      z3 == toDomain #c (pzD * qzD * hD % prime))))



let _point_add_if_second_branch_impl #c result p q x3hCube t5 = 
  [@inline_let]
  let len = getCoordinateLenU64 c in 
  let h0 = ST.get() in 

  l0 #c x3hCube h0 p q;

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
val _point_add0: #c: curve -> p: point c -> q: point c -> t12: lbuffer uint64 (size 12 *! getCoordinateLenU64 c) -> 
  Stack unit 
  (requires fun h0 -> live h0 p /\ live h0 q /\ live h0 t12 /\
    LowStar.Monotonic.Buffer.all_disjoint [loc t12; loc p; loc q] /\ 
    point_eval c h0 p /\ point_eval c h0 q)
  (ensures fun h0 _ h1 -> 
    modifies (loc t12) h0 h1 /\ point_eval c h1 p /\ point_eval c h1 q /\  (
    let u1, u2, s1, s2, h, r, uh, hCube = getU1HCube t12 in 
    
    u1Invariant #c h0 h1 u1 p q /\ u2Invariant #c h0 h1 u2 p q /\ 
    s1Invariant #c h0 h1 s1 p q /\ s2Invariant #c h0 h1 s2 p q /\ 
    hInvariant #c h1 h u1 u2 /\ rInvariant #c h1 r s1 s2 /\
    uhInvariant #c h1 uh h u1 /\ hCubeInvariant #c h1 hCube h))
 
let _point_add0 #c p q t12 = 
  [@inline_let]
  let len = getCoordinateLenU64 c in 
  let h0 = ST.get() in 
  
  move_from_jacobian_coordinates_mixed p q t12;
  Hacl.Impl.EC.PointAdd.compute_common_params_point_add t12;
  let h1 = ST.get() in
  lemma_point_eval c h0 h1 p;
  lemma_point_eval c h0 h1 q 


inline_for_extraction noextract
val point_add_mixed_ : #c: curve -> p: point c -> q: pointAffine c -> result: point c 
  -> tempBuffer: lbuffer uint64 (size 17 *! getCoordinateLenU64 c) -> 
  Stack unit (requires fun h -> 
    live h p /\ live h q /\ live h result /\ live h tempBuffer /\ 
    eq_or_disjoint q result /\ disjoint p q /\ disjoint p tempBuffer /\ 
    disjoint q tempBuffer /\ disjoint p result /\ disjoint result tempBuffer /\  
    point_eval c h p /\ 
      (let x, y = getXAff q, getYAff q in 
      felem_eval c h x /\ felem_eval c h y))
  (ensures fun h0 _ h1 -> modifies (loc tempBuffer |+| loc result) h0 h1 /\ point_eval c h1 result /\
    fromDomainPoint #c #DH (point_as_nat c h1 result) == _point_add_mixed #c (fromDomainPoint #c #DH (point_as_nat c h0 p)) (fromDomainPointAffine #c (point_affine_as_nat c h0 q)))


let point_add_mixed_ #c p q result tempBuffer = 
  let h0 = ST.get() in 
  let t12 = sub tempBuffer (size 0) (size 12 *! getCoordinateLenU64 c) in 
  let t5 = sub tempBuffer (size 12 *! getCoordinateLenU64 c) (size 5 *! getCoordinateLenU64 c) in 
  
  _point_add0 #c p q t12;
  let h1 = ST.get() in 
  _point_add_if_second_branch_impl result p q t12 t5;
  
  let h2 = ST.get() in 
  lemma_coord_eval c h0 h1 p;
  lemma_coord_eval c h0 h1 q;

  let prime = getPrime c in 

  let x3, y3, z3 = point_x_as_nat c h2 result, point_y_as_nat c h2 result, point_z_as_nat c h2 result in
  let pX, pY, pZ = point_x_as_nat c h0 p, point_y_as_nat c h0 p, point_z_as_nat c h0 p in 
  let qX, qY, qZ = point_x_as_nat c h0 q, point_y_as_nat c h0 q, point_z_as_nat c h0 q in 

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
  }



let point_add_mixed_p256 = point_add_mixed_ #P256


let point_add_mixed #c p q result tempBuffer = point_add_mixed_p256 p q result tempBuffer
