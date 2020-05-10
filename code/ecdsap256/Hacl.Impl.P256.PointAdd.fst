module Hacl.Impl.P256.PointAdd

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Hacl.Impl.P256.Arithmetics

open Lib.Buffer

open Spec.P256.Lemmas
open Spec.P256.Definitions
open Hacl.Impl.SolinasReduction
open Spec.P256.MontgomeryMultiplication
open Spec.P256.MontgomeryMultiplication.PointDouble
open Spec.P256.MontgomeryMultiplication.PointAdd
open Hacl.Impl.P256.LowLevel 
open Hacl.Impl.P256.LowLevel.PrimeSpecific
open Hacl.Impl.P256.MontgomeryMultiplication
open Spec.P256
open Hacl.Impl.P256.Math 


open FStar.Tactics 
open FStar.Tactics.Canon

open FStar.Math.Lemmas

friend Spec.P256.MontgomeryMultiplication
open FStar.Mul

#reset-options "--z3rlimit 300" 


val copy_point_conditional: x3_out: felem -> y3_out: felem -> z3_out: felem -> p: point -> maskPoint: point -> Stack unit
  (requires fun h -> live h x3_out /\ live h y3_out /\ live h z3_out /\ live h p /\ live h maskPoint /\ 
    LowStar.Monotonic.Buffer.all_disjoint[loc x3_out; loc y3_out; loc z3_out; loc p; loc maskPoint] /\
    as_nat h x3_out < prime /\ as_nat h y3_out < prime /\ as_nat h z3_out < prime /\
    as_nat h (gsub p (size 0) (size 4)) < prime /\ 
    as_nat h (gsub p (size 4) (size 4)) < prime /\ 
    as_nat h (gsub p (size 8) (size 4)) < prime 
  )
  (ensures fun h0 _ h1 -> modifies (loc x3_out |+| loc y3_out |+| loc z3_out) h0 h1 /\ 
    as_nat h1 x3_out < prime /\
    as_nat h1 y3_out < prime /\
    as_nat h1 z3_out < prime /\
    (
      let mask = as_nat h0 (gsub maskPoint (size 8) (size 4)) in 
      let x = gsub p (size 0) (size 4) in 
      let y = gsub p (size 4) (size 4) in 
      let z = gsub p (size 8) (size 4) in 

      if mask = 0 then 
	as_nat h1 x3_out == as_nat h0 x /\ as_nat h1 y3_out == as_nat h0 y /\ as_nat h1 z3_out == as_nat h0 z
      else 
	as_nat h1 x3_out == as_nat h0 x3_out /\ as_nat h1 y3_out == as_nat h0 y3_out /\ as_nat h1 z3_out == as_nat h0 z3_out
    )
)

let copy_point_conditional x3_out y3_out z3_out p maskPoint = 
  let z = sub maskPoint (size 8) (size 4) in 
  let mask = isZero_uint64_CT z in 

  let p_x = sub p (size 0) (size 4) in 
  let p_y = sub p (size 4) (size 4) in 
  let p_z = sub p (size 8) (size 4) in 

  copy_conditional x3_out p_x mask;
  copy_conditional y3_out p_y mask;
  copy_conditional z3_out p_z mask

    
inline_for_extraction noextract 
val move_from_jacobian_coordinates: u1: felem -> u2: felem -> s1: felem -> s2: felem ->  p: point -> q: point -> 
  tempBuffer16: lbuffer uint64 (size 16) -> 
  Stack unit (requires fun h -> live h u1 /\ live h u2 /\ live h s1 /\ live h s2 /\ live h p /\ live h q /\ live h tempBuffer16 /\
   LowStar.Monotonic.Buffer.all_disjoint [loc tempBuffer16; loc p; loc q; loc u1; loc u2; loc s1; loc s2] /\
    as_nat h (gsub p (size 8) (size 4)) < prime /\ 
    as_nat h (gsub p (size 0) (size 4)) < prime /\ 
    as_nat h (gsub p (size 4) (size 4)) < prime /\
    as_nat h (gsub q (size 8) (size 4)) < prime /\ 
    as_nat h (gsub q (size 0) (size 4)) < prime /\ 
    as_nat h (gsub q (size 4) (size 4)) < prime
    )
  (ensures fun h0 _ h1 ->  
    modifies (loc u1 |+| loc u2 |+| loc s1 |+| loc s2 |+| loc tempBuffer16) h0 h1 /\
    as_nat h1 u1 < prime /\ as_nat h1 u2 < prime /\ as_nat h1 s1 < prime /\ as_nat h1 s2 < prime  /\
    (
      let pX, pY, pZ = as_nat h0 (gsub p (size 0) (size 4)), as_nat h0 (gsub p (size 4) (size 4)), as_nat h0 (gsub p (size 8) (size 4)) in 
      let qX, qY, qZ = as_nat h0 (gsub q (size 0) (size 4)), as_nat h0 (gsub q (size 4) (size 4)), as_nat h0 (gsub q (size 8) (size 4)) in 
      
      let pxD, pyD, pzD = fromDomain_ pX, fromDomain_ pY, fromDomain_ pZ in 
      let qxD, qyD, qzD = fromDomain_ qX, fromDomain_ qY, fromDomain_ qZ in 

      as_nat h1 u1 == toDomain_ (qzD * qzD * pxD % prime256) /\
      as_nat h1 u2 == toDomain_ (pzD * pzD * qxD % prime256) /\
      as_nat h1 s1 == toDomain_ (qzD * qzD * qzD * pyD % prime256) /\
      as_nat h1 s2 == toDomain_ (pzD * pzD * pzD * qyD % prime256)
)
)

let move_from_jacobian_coordinates u1 u2 s1 s2 p q tempBuffer = 
    let h0 = ST.get() in 
   let pX = sub p (size 0) (size 4) in 
   let pY = sub p (size 4) (size 4) in 
   let pZ = sub p (size 8) (size 4) in 

   let qX = sub q (size 0) (size 4) in 
   let qY = sub q (size 4) (size 4) in 
   let qZ = sub q (size 8) (size 4) in 

   let z2Square = sub tempBuffer (size 0) (size 4) in 
   let z1Square = sub tempBuffer (size 4) (size 4) in 
   let z2Cube = sub tempBuffer (size 8) (size 4) in 
   let z1Cube = sub tempBuffer (size 12) (size 4) in  

   montgomery_square_buffer qZ z2Square;
   montgomery_square_buffer pZ z1Square;
   montgomery_multiplication_buffer z2Square qZ z2Cube;
   
   montgomery_multiplication_buffer z1Square pZ z1Cube;
   montgomery_multiplication_buffer z2Square pX u1;
   montgomery_multiplication_buffer z1Square qX u2;
   
   montgomery_multiplication_buffer z2Cube pY s1;
   montgomery_multiplication_buffer z1Cube qY s2;
   

     lemma_mod_mul_distr_l (fromDomain_ (as_nat h0 qZ) * fromDomain_ (as_nat h0 qZ)) (fromDomain_ (as_nat h0 qZ)) prime256;
     lemma_mod_mul_distr_l (fromDomain_ (as_nat h0 pZ) * fromDomain_ (as_nat h0 pZ)) (fromDomain_ (as_nat h0 pZ)) prime256;
     lemma_mod_mul_distr_l (fromDomain_ (as_nat h0 qZ) * fromDomain_ (as_nat h0 qZ)) (fromDomain_ (as_nat h0 pX)) prime256;   
     
     lemma_mod_mul_distr_l (fromDomain_ (as_nat h0 pZ) * fromDomain_ (as_nat h0 pZ)) (fromDomain_ (as_nat h0 qX)) prime256;
     lemma_mod_mul_distr_l (fromDomain_ (as_nat h0 qZ) * fromDomain_ (as_nat h0 qZ) * fromDomain_ (as_nat h0 qZ)) (fromDomain_ (as_nat h0 pY)) prime256;
     lemma_mod_mul_distr_l (fromDomain_ (as_nat h0 pZ) * fromDomain_ (as_nat h0 pZ) * fromDomain_ (as_nat h0 pZ)) (fromDomain_ (as_nat h0 qY)) prime256



inline_for_extraction noextract 
val compute_common_params_point_add: h: felem -> r: felem -> uh: felem -> hCube: felem -> 
  u1: felem -> u2: felem -> s1: felem -> s2: felem -> tempBuffer: lbuffer uint64 (size 16) -> 
  Stack unit 
    (requires fun h0 -> live h0 h /\ live h0 r /\ live h0 uh /\ live h0 hCube /\ live h0 u1 /\ live h0 u2 /\ live h0 s1 /\ live h0 s2 /\ live h0 tempBuffer /\  
      LowStar.Monotonic.Buffer.all_disjoint [loc u1; loc u2; loc s1; loc s2; loc h; loc r; loc uh; loc hCube; loc tempBuffer] /\ as_nat h0 u1 < prime /\ as_nat h0 u2 < prime /\ as_nat h0 s1 < prime /\ as_nat h0 s2 < prime)
    (ensures fun h0 _ h1 ->  
      modifies (loc h |+| loc r |+| loc uh |+| loc hCube |+| loc tempBuffer) h0 h1 /\ 
      as_nat h1 h < prime /\ as_nat h1 r < prime /\ as_nat h1 uh < prime /\ as_nat h1 hCube < prime /\
      (
	let u1D = fromDomain_ (as_nat h0 u1) in 
	let u2D = fromDomain_ (as_nat h0 u2) in 
	let s1D = fromDomain_ (as_nat h0 s1) in 
	let s2D = fromDomain_ (as_nat h0 s2) in 
	
	let hD = fromDomain_ (as_nat h1 h) in 

	as_nat h1 h == toDomain_ ((u2D - u1D) % prime256) /\
	as_nat h1 r == toDomain_ ((s2D - s1D) % prime256) /\
	as_nat h1 uh == toDomain_ (hD * hD * u1D % prime256) /\
	as_nat h1 hCube == toDomain_ (hD * hD * hD % prime256)
  )
)


let compute_common_params_point_add h r uh hCube u1 u2 s1 s2 tempBuffer =  
    let h0 = ST.get() in 
  let temp = sub tempBuffer (size 0) (size 4) in 
  p256_sub u2 u1 h; 
    let h1 = ST.get() in 
  p256_sub s2 s1 r; 
    let h2 = ST.get() in   
  montgomery_square_buffer h temp;
    let h3 = ST.get() in   
  montgomery_multiplication_buffer temp u1 uh;
  montgomery_multiplication_buffer temp h hCube;

    lemma_mod_mul_distr_l (fromDomain_ (as_nat h2 h) * fromDomain_ (as_nat h2 h)) (fromDomain_ (as_nat h3 u1)) prime256;
    lemma_mod_mul_distr_l (fromDomain_ (as_nat h2 h) * fromDomain_ (as_nat h2 h)) (fromDomain_ (as_nat h1 h)) prime256


inline_for_extraction noextract 
val computeX3_point_add: x3: felem -> hCube: felem -> uh: felem -> r: felem -> tempBuffer: lbuffer uint64 (size 16)->  Stack unit 
  (requires fun h0 -> live h0 x3 /\ live h0 hCube /\ live h0 uh /\ live h0 r /\ live h0 tempBuffer /\
    LowStar.Monotonic.Buffer.all_disjoint [loc x3; loc hCube; loc uh; loc r; loc tempBuffer] /\
    as_nat h0 hCube < prime /\as_nat h0 uh < prime /\ as_nat h0 r < prime
  )
  (ensures fun h0 _ h1 -> modifies (loc x3 |+| loc tempBuffer) h0 h1 /\ as_nat h1 x3 < prime /\ 
    (
      let hCubeD = fromDomain_ (as_nat h0 hCube) in 
      let uhD = fromDomain_ (as_nat h0 uh) in 
      let rD = fromDomain_ (as_nat h0 r) in 
      as_nat h1 x3 == toDomain_ ((rD * rD - hCubeD - 2 * uhD) % prime256)
    )  
  )

let computeX3_point_add x3 hCube uh r tempBuffer = 
    let h0 = ST.get() in 
  let rSquare = sub tempBuffer (size 0) (size 4) in 
  let rH = sub tempBuffer (size 4) (size 4) in 
  let twoUh = sub tempBuffer (size 8) (size 4) in 
  montgomery_square_buffer r rSquare; 
    let h1 = ST.get() in 
  p256_sub rSquare hCube rH;
    let h2 = ST.get() in 
  multByTwo uh twoUh;
    let h3 = ST.get() in 
  p256_sub rH twoUh x3;  
  
    lemma_mod_add_distr (-fromDomain_ (as_nat h1 hCube)) (fromDomain_ (as_nat h0 r) * fromDomain_ (as_nat h0 r)) prime256;
    lemma_mod_add_distr (-fromDomain_ (as_nat h3 twoUh)) (fromDomain_ (as_nat h0 r) * fromDomain_ (as_nat h0 r) - fromDomain_ (as_nat h1 hCube)) prime256;
    lemma_mod_sub_distr (fromDomain_ (as_nat h0 r) * fromDomain_ (as_nat h0 r) - fromDomain_ (as_nat h1 hCube)) (2 * fromDomain_ (as_nat h2 uh)) prime256


inline_for_extraction noextract 
val computeY3_point_add:y3: felem -> s1: felem -> hCube: felem -> uh: felem -> x3_out: felem -> r: felem -> tempBuffer: lbuffer uint64 (size 16) -> 
  Stack unit 
    (requires fun h -> live h y3 /\ live h s1 /\ live h hCube /\ live h uh /\ live h x3_out /\ live h r /\ live h tempBuffer /\
      LowStar.Monotonic.Buffer.all_disjoint [loc y3; loc s1; loc hCube; loc uh; loc x3_out; loc r; loc tempBuffer] /\
      as_nat h s1 < prime /\ as_nat h hCube < prime /\ as_nat h uh < prime /\ as_nat h x3_out <prime /\ as_nat h r < prime)
    (ensures fun h0 _ h1 -> 
      modifies (loc y3 |+| loc tempBuffer) h0 h1 /\ as_nat h1 y3 < prime /\ 
      (
	let s1D = fromDomain_ (as_nat h0 s1) in 
	let hCubeD = fromDomain_ (as_nat h0 hCube) in 
	let uhD = fromDomain_ (as_nat h0 uh) in 
	let x3D = fromDomain_ (as_nat h0 x3_out) in 
	let rD = fromDomain_ (as_nat h0 r) in 
	as_nat h1 y3 = toDomain_ (((uhD - x3D) * rD - s1D * hCubeD) % prime256)
    )
)

    
let computeY3_point_add y3 s1 hCube uh x3 r tempBuffer = 
    let h0 = ST.get() in
  let s1hCube = sub tempBuffer (size 0) (size 4) in 
  let u1hx3 = sub tempBuffer (size 4) (size 4) in 
  let ru1hx3 = sub tempBuffer (size 8) (size 4) in 

  montgomery_multiplication_buffer s1 hCube s1hCube;
  p256_sub uh x3 u1hx3;
  montgomery_multiplication_buffer u1hx3 r ru1hx3;
  
    let h3 = ST.get() in 
    lemma_mod_mul_distr_l (fromDomain_ (as_nat h0 uh) - fromDomain_ (as_nat h0 x3)) (fromDomain_ (as_nat h0 r)) prime256;
  p256_sub ru1hx3 s1hCube y3;
    lemma_mod_add_distr (-(fromDomain_ (as_nat h3 s1hCube)))  ((fromDomain_ (as_nat h0 uh) - fromDomain_ (as_nat h0 x3)) * fromDomain_ (as_nat h0 r))  prime256;
    lemma_mod_sub_distr ((fromDomain_ (as_nat h0 uh) - fromDomain_ (as_nat h0 x3)) * fromDomain_ (as_nat h0 r)) (fromDomain_ (as_nat h0 s1) * fromDomain_ (as_nat h0 hCube)) prime256



inline_for_extraction noextract 
val computeZ3_point_add: z3: felem ->  z1: felem -> z2: felem -> h: felem -> tempBuffer: lbuffer uint64 (size 16) -> 
  Stack unit (requires fun h0 -> live h0 z3 /\ live h0 z1 /\ live h0 z2 /\ live h0 h /\ live h0 tempBuffer /\ live h0 z3 /\
  LowStar.Monotonic.Buffer.all_disjoint [loc z1; loc z2; loc h; loc tempBuffer; loc z3] /\
  as_nat h0 z1 < prime /\ as_nat h0 z2 < prime /\ as_nat h0 h < prime)
  (ensures fun h0 _ h1 -> modifies (loc z3 |+| loc tempBuffer) h0 h1 /\ as_nat h1 z3 < prime /\ 
    (
      let z1D = fromDomain_ (as_nat h0 z1) in 
      let z2D = fromDomain_ (as_nat h0 z2) in 
      let hD = fromDomain_ (as_nat h0 h) in 
      as_nat h1 z3 == toDomain_ (z1D * z2D * hD % prime256)
    )  
  )  

let computeZ3_point_add z3 z1 z2 h tempBuffer = 
    let h0 = ST.get() in 
  let z1z2 = sub tempBuffer (size 0) (size 4) in
  montgomery_multiplication_buffer z1 z2 z1z2;
  montgomery_multiplication_buffer z1z2 h z3;
    lemma_mod_mul_distr_l (fromDomain_ (as_nat h0 z1) * fromDomain_ (as_nat h0 z2)) (fromDomain_ (as_nat h0 h)) prime256


inline_for_extraction noextract 
val point_add_if_second_branch_impl: result: point -> p: point -> q: point -> u1: felem -> u2: felem -> s1: felem -> 
  s2: felem -> r: felem -> h: felem -> uh: felem -> hCube: felem -> tempBuffer28 : lbuffer uint64 (size 28) -> 
  Stack unit 
    (requires fun h0 -> live h0 result /\ live h0 p /\ live h0 q /\ live h0 u1 /\ live h0 u2 /\ live h0 s1 /\ live h0 s2 /\ live h0 r /\ live h0 h /\ live h0 uh /\ live h0 hCube /\ live h0 tempBuffer28 /\
    
    as_nat h0 u1 < prime  /\ as_nat h0 u2 < prime  /\ as_nat h0 s1 < prime /\ as_nat h0 s2 < prime /\ as_nat h0 r < prime /\
    as_nat h0 h < prime /\ as_nat h0 uh < prime /\ as_nat h0 hCube < prime /\
    
    eq_or_disjoint p result /\
    LowStar.Monotonic.Buffer.all_disjoint [loc p; loc q; loc u1; loc u2; loc s1; loc s2; loc r; loc h; loc uh; loc hCube; loc tempBuffer28] /\ 
    disjoint result tempBuffer28 /\
    
    as_nat h0 (gsub p (size 8) (size 4)) < prime /\ 
    as_nat h0 (gsub p (size 0) (size 4)) < prime /\ 
    as_nat h0 (gsub p (size 4) (size 4)) < prime /\
    as_nat h0 (gsub q (size 8) (size 4)) < prime /\ 
    as_nat h0 (gsub q (size 0) (size 4)) < prime /\  
    as_nat h0 (gsub q (size 4) (size 4)) < prime /\
    
    (
      let pX, pY, pZ = as_nat h0 (gsub p (size 0) (size 4)), as_nat h0 (gsub p (size 4) (size 4)), as_nat h0 (gsub p (size 8) (size 4)) in 
      let qX, qY, qZ = as_nat h0 (gsub q (size 0) (size 4)), as_nat h0 (gsub q (size 4) (size 4)), as_nat h0 (gsub q (size 8) (size 4)) in 
      let pxD, pyD, pzD = fromDomain_ pX, fromDomain_ pY, fromDomain_ pZ in 
      let qxD, qyD, qzD = fromDomain_ qX, fromDomain_ qY, fromDomain_ qZ in 

      let u1D = fromDomain_ (as_nat h0 u1) in 
      let u2D = fromDomain_ (as_nat h0 u2) in 
      let s1D = fromDomain_ (as_nat h0 s1) in 
      let s2D = fromDomain_ (as_nat h0 s2) in 

      let hD = fromDomain_ (as_nat h0 h) in 
      
      as_nat h0 u1 == toDomain_ (qzD * qzD * pxD % prime256) /\
      as_nat h0 u2 == toDomain_ (pzD * pzD * qxD % prime256) /\
      as_nat h0 s1 == toDomain_ (qzD * qzD * qzD * pyD % prime256) /\
      as_nat h0 s2 == toDomain_ (pzD * pzD * pzD * qyD % prime256) /\
      
      as_nat h0 h == toDomain_ ((u2D - u1D) % prime256) /\
      as_nat h0 r == toDomain_ ((s2D - s1D) % prime256) /\
      as_nat h0 uh == toDomain_ (hD * hD * u1D % prime256) /\
      as_nat h0 hCube == toDomain_ (hD * hD * hD % prime256) 
  )
)
  (ensures fun h0 _ h1 -> modifies (loc tempBuffer28 |+| loc result) h0 h1 /\
    as_nat h1 (gsub result (size 8) (size 4)) < prime /\ 
    as_nat h1 (gsub result (size 0) (size 4)) < prime /\  
    as_nat h1 (gsub result (size 4) (size 4)) < prime /\
    (
      let pX, pY, pZ = as_nat h0 (gsub p (size 0) (size 4)), as_nat h0 (gsub p (size 4) (size 4)), as_nat h0 (gsub p (size 8) (size 4)) in 
      let qX, qY, qZ = as_nat h0 (gsub q (size 0) (size 4)), as_nat h0 (gsub q (size 4) (size 4)), as_nat h0 (gsub q (size 8) (size 4)) in 
      let x3, y3, z3 = as_nat h1 (gsub result (size 0) (size 4)), as_nat h1 (gsub result (size 4) (size 4)), as_nat h1 (gsub result (size 8) (size 4)) in  

      let pxD, pyD, pzD = fromDomain_ pX, fromDomain_ pY, fromDomain_ pZ in 
      let qxD, qyD, qzD = fromDomain_ qX, fromDomain_ qY, fromDomain_ qZ in 
      let x3D, y3D, z3D = fromDomain_ x3, fromDomain_ y3, fromDomain_ z3 in 

      let rD = fromDomain_ (as_nat h0 r) in 
      let hD = fromDomain_ (as_nat h0 h) in 
      let s1D = fromDomain_ (as_nat h0 s1) in 
      let u1D = fromDomain_ (as_nat h0 u1) in 

  if qzD = 0 then 
    x3D == pxD /\ y3D == pyD /\ z3D == pzD
   else if pzD = 0 then 
    x3D == qxD /\  y3D == qyD /\ z3D == qzD
   else 
    x3 == toDomain_ ((rD * rD - hD * hD * hD - 2 * hD * hD * u1D) % prime256) /\ 
    y3 == toDomain_(((hD * hD * u1D - fromDomain_ (x3)) * rD - s1D * hD * hD * hD) % prime256) /\
    z3 == toDomain_ (pzD * qzD * hD % prime256) 
  )
)


let point_add_if_second_branch_impl result p q u1 u2 s1 s2 r h uh hCube tempBuffer28 = 
    let h0 = ST.get() in 
  let pZ = sub p (size 8) (size 4) in 
  let qZ = sub q (size 8) (size 4) in 

  let tempBuffer16 = sub tempBuffer28 (size 0) (size 16) in 
  
  let x3_out = Lib.Buffer.sub tempBuffer28 (size 16) (size 4) in 
  let y3_out = Lib.Buffer.sub tempBuffer28 (size 20) (size 4) in 
  let z3_out = Lib.Buffer.sub tempBuffer28 (size 24) (size 4) in 

  computeX3_point_add x3_out hCube uh r tempBuffer16; 
    let h1 = ST.get() in 
  computeY3_point_add y3_out s1 hCube uh x3_out r tempBuffer16; 
  computeZ3_point_add z3_out pZ qZ h tempBuffer16;
  copy_point_conditional x3_out y3_out z3_out q p;

  copy_point_conditional x3_out y3_out z3_out p q;
  concat3 (size 4) x3_out (size 4) y3_out (size 4) z3_out result; 

    let hEnd = ST.get() in 

  let rD = fromDomain_ (as_nat h0 r) in 
  let hD = fromDomain_ (as_nat h0 h) in
  let u1D = fromDomain_ (as_nat h0 u1) in 
  let uhD = fromDomain_ (as_nat h0 uh) in 

  let s1D = fromDomain_ (as_nat h0 s1) in 
  let x3D = fromDomain_ (as_nat h1 x3_out) in 

  lemma_point_add_0 (rD * rD) (hD * hD * hD) (hD * hD * u1D);
  lemma_mod_sub_distr (rD * rD - 2 * uhD) (hD * hD * hD) prime256;
  assert_by_tactic (2 * (hD * hD * u1D) == 2 * hD * hD * u1D) canon;

  lemma_point_add_1 (hD * hD * u1D) x3D rD s1D (hD * hD * hD);
  assert_by_tactic (s1D * (hD * hD * hD) == s1D * hD * hD * hD) canon;

  assert_norm (modp_inv2 (pow2 256) > 0);
  assert_norm (modp_inv2 (pow2 256) % prime <> 0); 

  lemma_multiplication_not_mod_prime (as_nat h0 pZ);
  lemma_multiplication_not_mod_prime (as_nat h0 qZ);
  lemmaFromDomain (as_nat h0 pZ);
  lemmaFromDomain (as_nat h0 qZ)


let point_add p q result tempBuffer = 
    let h0 = ST.get() in 
  
  let z1 = sub p (size 8) (size 4) in 
  let z2 = sub q (size 8) (size 4) in 

  let tempBuffer16 = sub tempBuffer (size 0) (size 16) in 
   
  let u1 = sub tempBuffer (size 16) (size 4) in 
  let u2 = sub tempBuffer (size 20) (size 4) in 
  let s1 = sub tempBuffer (size 24) (size 4) in 
  let s2 = sub tempBuffer (size 28) (size 4) in 

  let h = sub tempBuffer (size 32) (size 4) in 
  let r = sub tempBuffer (size 36) (size 4) in 
  let uh = sub tempBuffer (size 40) (size 4) in 

  let hCube = sub tempBuffer (size 44) (size 4) in 

  let x3_out = sub tempBuffer (size 48) (size 4) in 
  let y3_out = sub tempBuffer (size 52) (size 4) in 
  let z3_out = sub tempBuffer (size 56) (size 4) in 

  let tempBuffer28 = sub tempBuffer (size 60) (size 28) in 

  move_from_jacobian_coordinates u1 u2 s1 s2 p q tempBuffer16;
  compute_common_params_point_add h r uh hCube u1 u2 s1 s2 tempBuffer16;
  point_add_if_second_branch_impl result p q u1 u2 s1 s2 r h uh hCube tempBuffer28;
    let h1 = ST.get() in 
      let pxD = fromDomain_ (as_nat h0 (gsub p (size 0) (size 4))) in 
      let pyD = fromDomain_ (as_nat h0 (gsub p (size 4) (size 4))) in 
      let pzD = fromDomain_ (as_nat h0 (gsub p (size 8) (size 4))) in 
      let qxD = fromDomain_ (as_nat h0 (gsub q (size 0) (size 4))) in 
      let qyD = fromDomain_ (as_nat h0 (gsub q (size 4) (size 4))) in 
      let qzD = fromDomain_ (as_nat h0 (gsub q (size 8) (size 4))) in 
      let x3 = as_nat h1 (gsub result (size 0) (size 4)) in 
      let y3 = as_nat h1 (gsub result (size 4) (size 4)) in 
      let z3 = as_nat h1 (gsub result (size 8) (size 4)) in 
      lemma_pointAddToSpecification pxD pyD pzD qxD qyD qzD x3 y3 z3 (as_nat h1 u1) (as_nat h1 u2) (as_nat h1 s1) (as_nat h1 s2) (as_nat h1 h) (as_nat h1 r)
