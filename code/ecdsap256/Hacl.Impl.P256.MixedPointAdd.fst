module Hacl.Impl.P256.MixedPointAdd

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
open Spec.P256.MontgomeryMultiplication.PointAdd
open Hacl.Impl.P256.LowLevel 
open Hacl.Impl.P256.LowLevel.PrimeSpecific
open Hacl.Impl.P256.MontgomeryMultiplication
open Spec.P256
open Hacl.Impl.P256.Math 

open FStar.Tactics 
open FStar.Tactics.Canon

open FStar.Math.Lemmas

open FStar.Mul

friend Hacl.Impl.P256.PointAdd


open Hacl.Impl.P256.Q.Comparision
open Hacl.Impl.P256.Q.PrimitivesMasking


#set-options "--z3rlimit 300 --fuel 0 --ifuel 0"

inline_for_extraction noextract 
val pointAffineIsNotZero: #buf_type : buftype ->  p: lbuffer_t buf_type uint64 (size 8) -> Stack uint64
  (requires fun h -> live h p /\ (
    let x = as_nat_il h (gsub p (size 0) (size 4)) in 
    let y = as_nat_il h (gsub p (size 4) (size 4)) in 
    x < prime256 /\ y < prime256))
  (ensures fun h0 r h1 -> modifies0 h0 h1 /\ (
    let x = as_nat_il h0 (gsub p (size 0) (size 4)) in 
    let y = as_nat_il h0 (gsub p (size 4) (size 4)) in 
    if isPointAtInfinityAffine (x, y) then uint_v r = pow2 64 - 1 else uint_v r == 0))

let pointAffineIsNotZero p = 
  let x = sub p (size 0) (size 4) in 
  let y = sub p (size 4) (size 4) in 

(*   let xZero = isZero_uint64_CT_global x in 
  let yZero = isZero_uint64_CT_global y in  *)

  let xZero = eq_felem_0_u64 #Private (global_to_comparable x) in 
  let yZero = eq_felem_0_u64 #Private (global_to_comparable y) in 

  logand_lemma xZero yZero;
  logand xZero yZero


inline_for_extraction noextract 
val move_from_jacobian_coordinates_mixed:  #buf_type : buftype -> 
  u1: felem -> u2: felem -> s1: felem -> s2: felem 
  ->  p: point -> q: lbuffer_t buf_type uint64 (size 8) -> tempBuffer16: lbuffer uint64 (size 16) -> 
  Stack unit (requires fun h -> live h u1 /\ live h u2 /\ live h s1 /\ live h s2 /\ live h p /\ live h q /\ live h tempBuffer16 /\
   LowStar.Monotonic.Buffer.all_disjoint [loc tempBuffer16; loc p; loc q; loc u1; loc u2; loc s1; loc s2] /\
    as_nat h (gsub p (size 8) (size 4)) < prime /\ 
    as_nat h (gsub p (size 0) (size 4)) < prime /\ 
    as_nat h (gsub p (size 4) (size 4)) < prime /\ 
    as_nat_il h (gsub q (size 0) (size 4)) < prime /\ 
    as_nat_il h (gsub q (size 4) (size 4)) < prime
    )
  (ensures fun h0 _ h1 ->  
    modifies (loc u1 |+| loc u2 |+| loc s1 |+| loc s2 |+| loc tempBuffer16) h0 h1  /\
    as_nat h1 u1 < prime /\ as_nat h1 u2 < prime /\ as_nat h1 s1 < prime /\ as_nat h1 s2 < prime  /\
    (
      let pX, pY, pZ = as_nat h0 (gsub p (size 0) (size 4)), as_nat h0 (gsub p (size 4) (size 4)), as_nat h0 (gsub p (size 8) (size 4)) in 
      let qX, qY = as_nat_il h0 (gsub q (size 0) (size 4)), as_nat_il h0 (gsub q (size 4) (size 4)) in 
      
      let pxD, pyD, pzD = fromDomain_ pX, fromDomain_ pY, fromDomain_ pZ in 
      let qxD, qyD = fromDomain_ qX, fromDomain_ qY in 
  
      as_nat h1 u1 == toDomain_ (pxD % prime256) /\
      as_nat h1 u2 == toDomain_ (pzD * pzD * qxD % prime256) /\ 
      as_nat h1 s1 == toDomain_ (pyD % prime256) /\
      as_nat h1 s2 == toDomain_ (pzD * pzD * pzD * qyD % prime256)
))


let move_from_jacobian_coordinates_mixed u1 u2 s1 s2 p q tempBuffer = 
    let h0 = ST.get() in 
   let pX = sub p (size 0) (size 4) in 
   let pY = sub p (size 4) (size 4) in 
   let pZ = sub p (size 8) (size 4) in 

   let qX = sub q (size 0) (size 4) in 
   let qY = sub q (size 4) (size 4) in 

   let z2Square = sub tempBuffer (size 0) (size 4) in 
   let z1Square = sub tempBuffer (size 4) (size 4) in 
   let z2Cube = sub tempBuffer (size 8) (size 4) in 
   let z1Cube = sub tempBuffer (size 12) (size 4) in  

    let qX = const_to_lbuffer qX in 
   let qY = const_to_lbuffer qY in 

   upd z2Square (size 0) (u64 0x000000300000000);
   upd z2Square (size 1) (u64 0x00000001FFFFFFFE);
   upd z2Square (size 2) (u64 0xFFFFFFFD00000002);
   upd z2Square (size 3) (u64 0xFFFFFFFE00000003);

    upd z2Cube (size 0) (u64 0x0000000CFFFFFFF7);
    upd z2Cube (size 1) (u64 0xFFFFFFF800000007); 
    upd z2Cube (size 2) (u64 0xFFFFFFFB0000000F);
    upd z2Cube (size 3) (u64 0x00000005FFFFFFFF);


(*    000000300000000 00000001FFFFFFFE FFFFFFFD00000002 FFFFFFFE00000003 

 *)

   (* montgomery_square_buffer qZ z2Square; *)
   montgomery_square_buffer pZ z1Square;
   (* montgomery_multiplication_buffer z2Square qZ z2Cube; *)
   
   montgomery_multiplication_buffer z1Square pZ z1Cube;
   montgomery_multiplication_buffer z2Square pX u1;
   montgomery_multiplication_buffer z1Square qX u2;
   
   montgomery_multiplication_buffer z2Cube pY s1;
   montgomery_multiplication_buffer z1Cube qY s2






inline_for_extraction noextract 
val computeZ3_point_add_mixed: z3: felem -> z1: felem -> h: felem -> tempBuffer: lbuffer uint64 (size 16) -> 
  Stack unit (requires fun h0 -> live h0 z3 /\ live h0 z1 /\ live h0 h /\
  as_nat h0 z1 < prime  /\ as_nat h0 h < prime)
  (ensures fun h0 _ h1 -> modifies (loc z3) h0 h1 /\ as_nat h1 z3 < prime /\ 
    (
      let z1D = fromDomain_ (as_nat h0 z1) in 
      let hD = fromDomain_ (as_nat h0 h) in 
      as_nat h1 z3 == toDomain_ (z1D * 1 * hD % prime256)
    )  
  )  

let computeZ3_point_add_mixed z3 z1 h tempBuffer =     
  let h0 = ST.get() in 
  let z1z2 = sub tempBuffer (size 0) (size 4) in
  montgomery_multiplication_buffer_by_one z1 z1z2;
  montgomery_multiplication_buffer z1z2 h z3

(* inline_for_extraction noextract
val cmovznz: out: felem -> x: felem -> y: felem -> mask: uint64 -> Stack unit
  (requires fun h -> as_nat h x < prime256 /\ as_nat h y < prime256 /\
    live h out /\ live h x /\ live h y /\ (uint_v mask == 0 \/ uint_v mask = pow2 64 - 1))
  (ensures fun h0 _ h1 -> modifies (loc out) h0 h1 /\ as_nat h1 out < prime256 /\ (
    if v mask = 0
      then as_nat h1 out == as_nat h0 x
      else 
	as_nat h1 out == as_nat h0 y))

let cmovznz out x y mask = 
  let h0 = ST.get() in 
  
  let out_0 = index out (size 0) in 
  let out_1 = index out (size 1) in 
  let out_2 = index out (size 2) in 
  let out_3 = index out (size 3) in  

  let mask = eq_mask mask (u64 0) in 
  
  let r0 = logor (logand x.(size 0) mask) (logand y.(size 0) (lognot mask)) in 
  let r1 = logor (logand x.(size 1) mask) (logand y.(size 1) (lognot mask)) in 
  let r2 = logor (logand x.(size 2) mask) (logand y.(size 2) (lognot mask)) in 
  let r3 = logor (logand x.(size 3) mask) (logand y.(size 3) (lognot mask)) in 

  upd out (size 0) r0;
  upd out (size 1) r1;
  upd out (size 2) r2;
  upd out (size 3) r3;

  let x = as_seq h0 x in 
  let y = as_seq h0 y in 
  cmovznz4_lemma mask (Seq.index y 0) (Seq.index x 0);
  cmovznz4_lemma mask (Seq.index y 1) (Seq.index x 1);
  cmovznz4_lemma mask (Seq.index y 2) (Seq.index x 2);
  cmovznz4_lemma mask (Seq.index y 3) (Seq.index x 3)
 *)

inline_for_extraction noextract
val cmovznz_one_mm: out: felem -> mask: uint64 -> Stack unit
  (requires fun h ->
    as_nat h out < prime256 /\
    live h out /\ (uint_v mask == 0 \/ uint_v mask = pow2 64 - 1))
  (ensures fun h0 _ h1 -> modifies (loc out) h0 h1 /\ 
    as_nat h1 out < prime256 /\ (
    if v mask = 0 then 
      as_nat h1 out == as_nat h0 out 
    else 
      as_nat h1 out ==  Spec.P256.MontgomeryMultiplication.toDomain_ 1))

let cmovznz_one_mm out mask = 

  let out_0 = index out (size 0) in 
  let out_1 = index out (size 1) in 
  let out_2 = index out (size 2) in 
  let out_3 = index out (size 3) in 

  let x_0 = u64 1 in 
  let x_1 = u64 0 in 
  let x_2 = u64 0 in 
  let x_3 = u64 0 in 
  
  let r_0 = logxor out_0 (logand mask (logxor out_0 x_0)) in 
  let r_1 = logxor out_1 (logand mask (logxor out_1 x_1)) in 
  let r_2 = logxor out_2 (logand mask (logxor out_2 x_2)) in 
  let r_3 = logxor out_3 (logand mask (logxor out_3 x_3)) in 

  lemma_xor_copy_cond out_0 x_0 mask;
  lemma_xor_copy_cond out_1 x_1 mask;
  lemma_xor_copy_cond out_2 x_2 mask;
  lemma_xor_copy_cond out_3 x_3 mask;

  upd out (size 0) r_0;
  upd out (size 1) r_1;
  upd out (size 2) r_2;
  upd out (size 3) r_3;


  Spec.P256.MontgomeryMultiplication.lemmaToDomain 1;
  assert_norm(pow2 256 % prime256 = uint_v x_0 + uint_v x_1 * pow2 64 + uint_v x_2 * pow2 128 + uint_v x_3 * pow2 192);
  assert_norm (pow2 64 * pow2 64 = pow2 128);
  assert_norm (pow2 64 * pow2 64 * pow2 64 = pow2 192)

inline_for_extraction noextract 
val copy_point_conditional_affine_to_result: #buf_type : buftype ->  out: point 
  -> q: lbuffer_t buf_type uint64 (size 8)
  -> maskPoint: point
  -> Stack unit 
  (requires fun h -> live h out /\ live h q /\ live h maskPoint /\ disjoint q out /\ eq_or_disjoint out maskPoint /\
    (
      as_nat_il h (gsub q (size 0) (size 4)) < prime256 /\ 
      as_nat_il h (gsub q (size 4) (size 4)) < prime256 /\
    
      as_nat h (gsub out (size 0) (size 4)) < prime256 /\ 
      as_nat h (gsub out (size 4) (size 4)) < prime256 /\
      as_nat h (gsub out (size 8) (size 4)) < prime256 /\

      as_nat h (gsub maskPoint (size 8) (size 4)) < prime256
    )
  )
  (ensures fun h0 _ h1 -> modifies (loc out) h0 h1 /\ (
    let xOut = gsub out (size 0) (size 4) in 
    let yOut = gsub out (size 4) (size 4) in 
    let zOut = gsub out (size 8) (size 4) in 
    as_nat h1 xOut < prime256 /\
    as_nat h1 yOut < prime256 /\
    as_nat h1 zOut < prime256  /\ (


    let maskX = fromDomain_ (as_nat h0 (gsub maskPoint (size 0) (size 4))) in 
    let maskY = fromDomain_ (as_nat h0 (gsub maskPoint (size 4) (size 4))) in 
    let maskZ = fromDomain_ (as_nat h0 (gsub maskPoint (size 8) (size 4))) in 

    let xQ = gsub q (size 0) (size 4) in 
    let yQ = gsub q (size 4) (size 4) in 

    if isPointAtInfinity (maskX, maskY, maskZ)  then 
      as_nat h1 xOut == as_nat_il h0 xQ /\ 
      as_nat h1 yOut == as_nat_il h0 yQ /\ 
      as_nat h1 zOut == Spec.P256.MontgomeryMultiplication.toDomain_ 1 
    else
      as_nat h1 xOut == as_nat h0 xOut /\ 
      as_nat h1 yOut == as_nat h0 yOut /\ 
      as_nat h1 zOut == as_nat h0 zOut)))


let copy_point_conditional_affine_to_result out q maskPoint = 
  let h0 = ST.get() in 
  
  let pZ = sub maskPoint (size 8) (size 4) in 
  (* let mask = isZero_uint64_CT pZ in  *)
  let mask = eq_felem_0_u64 #Private pZ in 

  let xOut = sub out (size 0) (size 4) in 
  let yOut = sub out (size 4) (size 4) in 
  let zOut = sub out (size 8) (size 4) in 
  
  let qX = sub q (size 0) (size 4) in 
  let qY = sub q (size 4) (size 4) in 


   let qX = const_to_lbuffer qX in 
   let qY = const_to_lbuffer qY in 


  Hacl.Impl.P256.Q.PrimitivesMasking.copy_conditional xOut qX mask;
  Hacl.Impl.P256.Q.PrimitivesMasking.copy_conditional yOut qY mask;
  cmovznz_one_mm zOut mask;


  lemma_multiplication_not_mod_prime (as_nat h0 pZ);
  lemmaFromDomain (as_nat h0 pZ)

inline_for_extraction noextract 
val copy_point_conditional_jac_to_result: #buf_type : buftype ->  out: point 
  -> q: point 
  -> maskPoint: lbuffer_t buf_type uint64 (size 8)
  -> Stack unit 
  (requires fun h -> live h out /\ live h q /\  eq_or_disjoint q out /\    
    live h maskPoint /\ 
    as_nat h (gsub q (size 0) (size 4)) < prime256 /\ 
    as_nat h (gsub q (size 4) (size 4)) < prime256 /\
    as_nat h (gsub q (size 8) (size 4)) < prime256 /\

    as_nat_il h (gsub maskPoint (size 0) (size 4)) < prime256 /\
    as_nat_il h (gsub maskPoint (size 4) (size 4)) < prime256 /\
    
    as_nat h (gsub out (size 0) (size 4)) < prime256 /\
    as_nat h (gsub out (size 4) (size 4)) < prime256 /\
    as_nat h (gsub out (size 8) (size 4)) < prime256)
    
  (ensures fun h0 _ h1 -> modifies (loc out) h0 h1 /\ (
    let xOut = gsub out (size 0) (size 4) in 
    let yOut = gsub out (size 4) (size 4) in 
    let zOut = gsub out (size 8) (size 4) in 
    as_nat h1 xOut < prime256 /\
    as_nat h1 yOut < prime256 /\
    as_nat h1 zOut < prime256 /\ (

    let xQ = gsub q (size 0) (size 4) in 
    let yQ = gsub q (size 4) (size 4) in 
    let zQ = gsub q (size 8) (size 4) in 

    if isPointAtInfinityAffine (
      as_nat_il h0 (gsub maskPoint (size 0) (size 4)), 
      as_nat_il h0 (gsub maskPoint (size 4) (size 4)))
    then    
          as_nat h1 xOut == as_nat h0 xQ /\ 
      as_nat h1 yOut == as_nat h0 yQ /\ 
      as_nat h1 zOut == as_nat h0 zQ
    else

      as_nat h1 xOut == as_nat h0 xOut /\ 
      as_nat h1 yOut == as_nat h0 yOut /\ 
      as_nat h1 zOut == as_nat h0 zOut
      
      )))


let copy_point_conditional_jac_to_result out q maskPoint = 
  
  let mask = pointAffineIsNotZero maskPoint in 

  let xOut = sub out (size 0) (size 4) in 
  let yOut = sub out (size 4) (size 4) in 
  let zOut = sub out (size 8) (size 4) in 

  let qX = sub q (size 0) (size 4) in 
  let qY = sub q (size 4) (size 4) in 
  let qZ = sub q (size 8) (size 4) in 

  Hacl.Impl.P256.Q.PrimitivesMasking.copy_conditional xOut qX mask;
  Hacl.Impl.P256.Q.PrimitivesMasking.copy_conditional yOut qY mask;
  Hacl.Impl.P256.Q.PrimitivesMasking.copy_conditional zOut qZ mask






(*TODO: Move away *)
(*TODO: to check *)


inline_for_extraction noextract
val copy_point_conditional: #buf_type : buftype -> result: point -> x: point -> p: point -> maskPoint: lbuffer_t buf_type uint64 (size 8) -> Stack unit
  (requires fun h -> live h result /\ live h p /\ live h maskPoint /\ live h x /\
    disjoint x result /\ eq_or_disjoint p result /\
    as_nat h (gsub p (size 0) (size 4)) < prime /\ 
    as_nat h (gsub p (size 4) (size 4)) < prime /\ 
    as_nat h (gsub p (size 8) (size 4)) < prime /\

    as_nat h (gsub x (size 0) (size 4)) < prime /\ 
    as_nat h (gsub x (size 4) (size 4)) < prime /\ 
    as_nat h (gsub x (size 8) (size 4)) < prime /\

    as_nat_il h (gsub maskPoint (size 0) (size 4)) < prime /\
    as_nat_il h (gsub maskPoint (size 4) (size 4)) < prime)
  (ensures fun h0 _ h1 -> modifies (loc result) h0 h1 /\
  
  as_nat h1 (gsub result (size 0) (size 4)) < prime /\ 
  as_nat h1 (gsub result (size 4) (size 4)) < prime /\ 
  as_nat h1 (gsub result (size 8) (size 4)) < prime /\ (
  
  if isPointAtInfinityAffine 
    (fromDomain_ (as_nat_il h0 (gsub maskPoint (size 0) (size 4))), 
    fromDomain_ (as_nat_il h0 (gsub maskPoint (size 4) (size 4))))
  then 
    as_nat h1 (gsub result (size 0) (size 4)) == as_nat h0 (gsub p (size 0) (size 4)) /\
    as_nat h1 (gsub result (size 4) (size 4)) == as_nat h0 (gsub p (size 4) (size 4)) /\
    as_nat h1 (gsub result (size 8) (size 4)) == as_nat h0 (gsub p (size 8) (size 4)) 
  else
    as_nat h1 (gsub result (size 0) (size 4)) == as_nat h0 (gsub x (size 0) (size 4)) /\
    as_nat h1 (gsub result (size 4) (size 4)) == as_nat h0 (gsub x (size 4) (size 4)) /\
    as_nat h1 (gsub result (size 8) (size 4)) == as_nat h0 (gsub x (size 8) (size 4))))

let copy_point_conditional result x p maskPoint = 
  let h0 = ST.get() in 

  let mask = pointAffineIsNotZero maskPoint in 

  let p_x = sub p (size 0) (size 4) in 
  let p_y = sub p (size 4) (size 4) in 
  let p_z = sub p (size 8) (size 4) in 

  let x_x = sub x (size 0) (size 4) in 
  let x_y = sub x (size 4) (size 4) in 
  let x_z = sub x (size 8) (size 4) in 

  let result_x = sub result (size 0) (size 4) in 
  let result_y = sub result (size 4) (size 4) in 
  let result_z = sub result (size 8) (size 4) in 

  cmovznz4 p_x x_x result_x mask;
  cmovznz4 p_y x_y result_y mask;
  cmovznz4 p_z x_z result_z mask;

  let mX = as_nat_il h0 (gsub maskPoint (size 0) (size 4)) in 
  let mY = as_nat_il h0 (gsub maskPoint (size 4) (size 4)) in 

  lemma_multiplication_not_mod_prime mX;
  lemmaFromDomain mX;

  lemma_multiplication_not_mod_prime mY;
  lemmaFromDomain mY


inline_for_extraction noextract 
val point_add_if_second_branch_impl_mixed: #buf_type : buftype ->   result: point -> p: point -> q:  lbuffer_t buf_type uint64 (size 8)  
  -> u1: felem -> u2: felem -> s1: felem -> s2: felem -> r: felem -> h: felem -> uh: felem 
  -> hCube: felem -> tempBuffer28 : lbuffer uint64 (size 28) -> 
  Stack unit 
    (requires fun h0 -> live h0 result /\ live h0 p /\ live h0 q /\ live h0 u1 /\ live h0 u2 /\ live h0 s1 /\ live h0 s2 /\ live h0 r /\ live h0 h /\ live h0 uh /\ live h0 hCube /\ live h0 tempBuffer28 /\
    
    as_nat h0 u1 < prime /\ as_nat h0 u2 < prime /\ as_nat h0 s1 < prime /\ as_nat h0 s2 < prime /\
    as_nat h0 r < prime /\ as_nat h0 h < prime /\ as_nat h0 uh < prime /\ as_nat h0 hCube < prime /\
    
    eq_or_disjoint result p /\
    LowStar.Monotonic.Buffer.all_disjoint [loc result; loc q; loc hCube; loc uh; loc r; loc tempBuffer28; loc s1; loc h] /\
    disjoint p tempBuffer28 /\

    as_nat h0 (gsub p (size 8) (size 4)) < prime /\ 
    as_nat h0 (gsub p (size 0) (size 4)) < prime /\ 
    as_nat h0 (gsub p (size 4) (size 4)) < prime /\
    as_nat_il h0 (gsub q (size 0) (size 4)) < prime /\  
    as_nat_il h0 (gsub q (size 4) (size 4)) < prime /\ (

    let pX, pY, pZ = as_nat h0 (gsub p (size 0) (size 4)), as_nat h0 (gsub p (size 4) (size 4)), as_nat h0 (gsub p (size 8) (size 4)) in 
    let qX, qY = as_nat_il h0 (gsub q (size 0) (size 4)), as_nat_il h0 (gsub q (size 4) (size 4)) in 
    let pxD, pyD, pzD = fromDomain_ pX, fromDomain_ pY, fromDomain_ pZ in 
    let qxD, qyD = fromDomain_ qX, fromDomain_ qY in 

    let u1D = fromDomain_ (as_nat h0 u1) in 
    let u2D = fromDomain_ (as_nat h0 u2) in 
    let s1D = fromDomain_ (as_nat h0 s1) in 
    let s2D = fromDomain_ (as_nat h0 s2) in 

    let hD = fromDomain_ (as_nat h0 h) in 
      
    as_nat h0 u1 == toDomain_ (pxD % prime256) /\
    as_nat h0 u2 == toDomain_ (pzD * pzD * qxD % prime256) /\
    as_nat h0 s1 == toDomain_ (pyD % prime256) /\
    as_nat h0 s2 == toDomain_ (pzD * pzD * pzD * qyD % prime256) /\
      
    as_nat h0 h == toDomain_ ((u2D - u1D) % prime256) /\
    as_nat h0 r == toDomain_ ((s2D - s1D) % prime256) /\
    as_nat h0 uh == toDomain_ (hD * hD * u1D % prime256) /\
    as_nat h0 hCube == toDomain_ (hD * hD * hD % prime256)))
  (ensures fun h0 _ h1 -> modifies (loc tempBuffer28 |+| loc result) h0 h1 /\
    as_nat h1 (gsub result (size 8) (size 4)) < prime /\ 
    as_nat h1 (gsub result (size 0) (size 4)) < prime /\  
    as_nat h1 (gsub result (size 4) (size 4)) < prime /\ (
    
    let pX, pY, pZ = as_nat h0 (gsub p (size 0) (size 4)), as_nat h0 (gsub p (size 4) (size 4)), as_nat h0 (gsub p (size 8) (size 4)) in 
    let qX, qY = as_nat_il h0 (gsub q (size 0) (size 4)), as_nat_il h0 (gsub q (size 4) (size 4)) in 
    let x3, y3, z3 = as_nat h1 (gsub result (size 0) (size 4)), as_nat h1 (gsub result (size 4) (size 4)), as_nat h1 (gsub result (size 8) (size 4)) in  

    let pxD, pyD, pzD = fromDomain_ pX, fromDomain_ pY, fromDomain_ pZ in 
    let qxD, qyD = fromDomain_ qX, fromDomain_ qY in 
    let x3D, y3D, z3D = fromDomain_ x3, fromDomain_ y3, fromDomain_ z3 in 

    let rD = fromDomain_ (as_nat h0 r) in 
    let hD = fromDomain_ (as_nat h0 h) in 
    let s1D = fromDomain_ (as_nat h0 s1) in 
    let u1D = fromDomain_ (as_nat h0 u1) in 
    
    if isPointAtInfinityAffine  (qxD, qyD) then 
      x3D == pxD /\ y3D == pyD /\ z3D == pzD
    else if isPointAtInfinity (pxD, pyD, pzD) then 
      x3D == qxD /\  y3D == qyD /\ z3D == 1 
    else 
      x3 == toDomain_ ((rD * rD - hD * hD * hD - 2 * hD * hD * u1D) % prime256) /\ 
      y3 == toDomain_(((hD * hD * u1D - fromDomain_ x3) * rD - s1D * hD * hD * hD) % prime256) /\
      z3 == toDomain_ (pzD * hD % prime256)))


let point_add_if_second_branch_impl_mixed result p q u1 u2 s1 s2 r h uh hCube tempBuffer28 = 
    let h0 = ST.get() in 
  let pZ = sub p (size 8) (size 4) in

  let tempBuffer16 = sub tempBuffer28 (size 0) (size 16) in 


  let pointOut = Lib.Buffer.sub tempBuffer28 (size 16) (size 12) in 
  let xOut = Lib.Buffer.sub tempBuffer28 (size 16) (size 4) in 
  let yOut = Lib.Buffer.sub tempBuffer28 (size 20) (size 4) in 
  let zOut = Lib.Buffer.sub tempBuffer28 (size 24) (size 4) in 


  Hacl.Impl.P256.PointAdd.computeX3_point_add xOut hCube uh r tempBuffer16; 
  Hacl.Impl.P256.PointAdd.computeY3_point_add yOut s1 hCube uh xOut r tempBuffer16;

    let h1 = ST.get() in 

  computeZ3_point_add_mixed zOut pZ h tempBuffer16;
  copy_point_conditional_affine_to_result pointOut q p; 
  copy_point_conditional result pointOut p q; 

  let rD = fromDomain_ (as_nat h0 r) in 
  let hD = fromDomain_ (as_nat h0 h) in
  let u1D = fromDomain_ (as_nat h0 u1) in 
  let uhD = fromDomain_ (as_nat h0 uh) in 

  let s1D = fromDomain_ (as_nat h0 s1) in 
  let x3D = fromDomain_ (as_nat h1 xOut) in 


  lemma_point_add_0 (rD * rD) (hD * hD * hD) (hD * hD * u1D);
  lemma_mod_sub_distr (rD * rD - 2 * uhD) (hD * hD * hD) prime256;
  assert_by_tactic (2 * (hD * hD * u1D) == 2 * hD * hD * u1D) canon;

  lemma_point_add_1 (hD * hD * u1D) x3D rD s1D (hD * hD * hD);
  assert_by_tactic (s1D * (hD * hD * hD) == s1D * hD * hD * hD) canon;

  assert_norm (modp_inv2 (pow2 256) > 0);
  assert_norm (modp_inv2 (pow2 256) % prime <> 0)


let point_add_mixed #buftype p q result tempBuffer = 
    let h0 = ST.get() in 
  
  let tempBuffer28 = sub tempBuffer (size 0) (size 28) in 
  let tempBuffer16 = sub tempBuffer (size 0) (size 16) in 
   
  let u1 = sub tempBuffer (size 28) (size 4) in 
  let u2 = sub tempBuffer (size 32) (size 4) in 
  let s1 = sub tempBuffer (size 36) (size 4) in 
  let s2 = sub tempBuffer (size 40) (size 4) in 

  let h = sub tempBuffer (size 44) (size 4) in 
  let r = sub tempBuffer (size 48) (size 4) in 
  let uh = sub tempBuffer (size 52) (size 4) in 

  let hCube = sub tempBuffer (size 56) (size 4) in 

  move_from_jacobian_coordinates_mixed u1 u2 s1 s2 p q tempBuffer16;
  Hacl.Impl.P256.PointAdd.compute_common_params_point_add h r uh hCube u1 u2 s1 s2 tempBuffer16; 
  point_add_if_second_branch_impl_mixed result p q u1 u2 s1 s2 r h uh hCube tempBuffer28;

    let h1 = ST.get() in 
      let pxD = fromDomain_ (as_nat h0 (gsub p (size 0) (size 4))) in 
      let pyD = fromDomain_ (as_nat h0 (gsub p (size 4) (size 4))) in 
      let pzD = fromDomain_ (as_nat h0 (gsub p (size 8) (size 4))) in 
      let qxD = fromDomain_ (as_nat_il h0 (gsub q (size 0) (size 4))) in 
      let qyD = fromDomain_ (as_nat_il h0 (gsub q (size 4) (size 4))) in 
      let x3 = as_nat h1 (gsub result (size 0) (size 4)) in 
      let y3 = as_nat h1 (gsub result (size 4) (size 4)) in 
      let z3 = as_nat h1 (gsub result (size 8) (size 4)) in 

  lemma_pointAdd_Mixed_ToSpecification pxD pyD pzD qxD qyD x3 y3 z3 (as_nat h1 u1) (as_nat h1 u2) (as_nat h1 s1) (as_nat h1 s2) (as_nat h1 h) (as_nat h1 r)
