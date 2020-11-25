module Hacl.Impl.P256.MixedPointAdd

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer

open Spec.P256.Definitions
open Spec.P256.Lemmas

open FStar.Math
open FStar.Math.Lemmas
open FStar.Mul

open Hacl.Impl.P256.LowLevel
open Hacl.Impl.P256.PointAdd

open Hacl.Impl.P256.MontgomeryMultiplication
open Hacl.Impl.P256.LowLevel.PrimeSpecific

open Spec.P256.MontgomeryMultiplication

#set-options "--z3rlimit 100 --fuel 0 --ifuel 0"

(* just changing argument order *)
inline_for_extraction noextract
val montgomery_multiplication_buffer: result: felem -> a: felem -> b: felem ->  Stack unit
  (requires (fun h -> live h a /\  as_nat h a < prime256 /\ live h b /\ live h result /\ as_nat h b < prime256)) 
  (ensures (fun h0 _ h1 -> 
    modifies (loc result) h0 h1 /\  
    as_nat h1 result < prime256 /\
    as_nat h1 result = (as_nat h0 a * as_nat h0 b * modp_inv2_prime (pow2 256) prime256) % prime256 /\
    as_nat h1 result = toDomain_ (fromDomain_ (as_nat h0 a) * fromDomain_ (as_nat h0 b) % prime256) /\
    as_nat h1 result = toDomain_ (fromDomain_ (as_nat h0 a) * fromDomain_ (as_nat h0 b)))
  )

let montgomery_multiplication_buffer result a b = 
  Hacl.Impl.P256.MontgomeryMultiplication.montgomery_multiplication_buffer a b result


inline_for_extraction noextract
val p256_add: out: felem -> arg1: felem -> arg2: felem -> Stack unit 
  (requires (fun h0 ->  
    live h0 arg1 /\ live h0 arg2 /\ live h0 out /\ 
    eq_or_disjoint arg1 out /\ eq_or_disjoint arg2 out /\
    as_nat h0 arg1 < prime256 /\ as_nat h0 arg2 < prime256))
  (ensures (fun h0 _ h1 -> modifies (loc out) h0 h1 /\ 
      as_nat h1 out == (as_nat h0 arg1 + as_nat h0 arg2) % prime256 /\
      as_nat h1 out == toDomain_ ((fromDomain_ (as_nat h0 arg1) + fromDomain_ (as_nat h0 arg2)) % prime256)))

let p256_add result a b = Hacl.Impl.P256.LowLevel.PrimeSpecific.p256_add a b result


inline_for_extraction noextract
val p256_double: out: felem -> arg1: felem -> Stack unit 
  (requires (fun h0 ->  live h0 arg1 /\ live h0 out /\ eq_or_disjoint arg1 out /\ as_nat h0 arg1 < prime256))
  (ensures (fun h0 _ h1 -> modifies (loc out) h0 h1 /\ 
    as_nat h1 out == (2 * as_nat h0 arg1) % prime256 /\ as_nat h1 out < prime256 /\
    as_nat h1 out == toDomain_ (2 * fromDomain_ (as_nat h0 arg1) % prime256)
  )
)

let p256_double result a =  Hacl.Impl.P256.LowLevel.PrimeSpecific.p256_double a result


inline_for_extraction noextract
val p256_sub: out: felem -> arg1: felem -> arg2: felem -> Stack unit 
  (requires 
    (fun h0 -> live h0 out /\ live h0 arg1 /\ live h0 arg2 /\ 
      eq_or_disjoint arg1 out /\ eq_or_disjoint arg2 out /\
      as_nat h0 arg1 < prime256 /\ as_nat h0 arg2 < prime256))
    (ensures (fun h0 _ h1 -> modifies (loc out) h0 h1 /\ 
	as_nat h1 out == (as_nat h0 arg1 - as_nat h0 arg2) % prime256 /\
	as_nat h1 out == toDomain_ ((fromDomain_ (as_nat h0 arg1) - fromDomain_ (as_nat h0 arg2)) % prime256)
    )
)    

let p256_sub result a b = Hacl.Impl.P256.LowLevel.PrimeSpecific.p256_sub a b result




inline_for_extraction
type pointAffine = lbuffer uint64 (size 8)

val pointAffineIsNotZero: p: pointAffine -> Stack uint64
  (requires fun h -> live h p)
  (ensures fun h0 r h1 -> modifies0 h0 h1 /\ (
    let x = gsub p (size 0) (size 4) in 
    let y = gsub p (size 4) (size 4) in 
    if as_nat h0 x = 0 || as_nat h0 y = 0 then uint_v r = pow2 64 - 1 else uint_v r == 0))

let pointAffineIsNotZero p = 
  let x = sub p (size 0) (size 4) in 
  let y = sub p (size 4) (size 4) in 
  let xZero = isZero_uint64_CT x in 
  let yZero = isZero_uint64_CT y in 
  logor_lemma xZero yZero;
  logor xZero yZero


val copy_conditional_one_mm: out: felem -> mask: uint64 -> Stack unit
  (requires fun h -> as_nat h out < prime256 /\ live h out /\ (uint_v mask == 0 \/ uint_v mask = pow2 64 - 1))
  (ensures fun h0 _ h1 -> modifies (loc out) h0 h1 /\
    as_nat h1 out < prime256 /\ (
    if v mask = 0
      then as_nat h1 out == as_nat h0 out
      else 
	as_nat h1 out == Spec.P256.MontgomeryMultiplication.toDomain_ 1  ))

let copy_conditional_one_mm out mask = 
  let out_0 = index out (size 0) in 
  let out_1 = index out (size 1) in 
  let out_2 = index out (size 2) in 
  let out_3 = index out (size 3) in 

  let x_0 = u64 1 in 
  let x_1 = u64 18446744069414584320 in 
  let x_2 = u64 18446744073709551615 in 
  let x_3 = u64 4294967294 in 

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


val copy_point_conditional: out: point -> p: pointAffine -> maskPoint: point -> Stack unit 
  (requires fun h -> live h out /\ live h p /\ live h maskPoint /\ 
    disjoint p out /\ disjoint p maskPoint /\ disjoint out maskPoint /\
    (
      let xOut = as_nat h (gsub out (size 0) (size 4)) in 
      let yOut = as_nat h (gsub out (size 4) (size 4)) in 
      let zOut = as_nat h (gsub out (size 8) (size 4)) in 
      xOut < prime256 /\ yOut < prime256 /\ zOut < prime256 /\
      as_nat h (gsub p (size 0) (size 4)) < prime256 /\ 
      as_nat h (gsub p (size 4) (size 4)) < prime256
    )
  )
  (ensures fun h0 _ h1 -> modifies (loc out) h0 h1 /\ (
    let xOut = gsub out (size 0) (size 4) in 
    let yOut = gsub out (size 4) (size 4) in 
    let zOut = gsub out (size 8) (size 4) in 
    as_nat h1 xOut < prime256 /\
    as_nat h1 yOut < prime256 /\
    as_nat h1 zOut < prime256 /\ (
    
    let mask = as_nat h0 (gsub maskPoint (size 8) (size 4)) in 
    let x = gsub p (size 0) (size 4) in 
    let y = gsub p (size 4) (size 4) in 

    if mask = 0 then 
      as_nat h1 xOut == as_nat h0 x /\ 
      as_nat h1 yOut == as_nat h0 y /\ 
      as_nat h1 zOut == Spec.P256.MontgomeryMultiplication.toDomain_ 1 
    else 
      as_nat h1 xOut == as_nat h0 xOut /\ 
      as_nat h1 yOut == as_nat h0 yOut /\ 
      as_nat h1 zOut == as_nat h0 zOut 
    )))

let copy_point_conditional out p maskPoint = 
  let z = sub maskPoint (size 8) (size 4) in 
  let mask = isZero_uint64_CT z in 

  let xOut = sub out (size 0) (size 4) in 
  let yOut = sub out (size 4) (size 4) in 
  let zOut = sub out (size 8) (size 4) in 

  let p_x = sub p (size 0) (size 4) in 
  let p_y = sub p (size 4) (size 4) in 

  copy_conditional xOut p_x mask;
  copy_conditional yOut p_y mask;
  copy_conditional_one_mm zOut mask


let prime = prime256 

val point_add_step0: result: point -> p: point -> q: pointAffine -> tempBuffer: lbuffer uint64 (size 20) -> Stack unit
  (requires fun h -> live h result /\ live h p /\ live h q /\ live h tempBuffer /\
    disjoint p tempBuffer /\ disjoint q tempBuffer /\ (
    let x1 = gsub p (size 0) (size 4) in 
    let y1 = gsub p (size 4) (size 4) in 
    let z1 = gsub p (size 8) (size 4) in 

    let x2 = gsub q (size 0) (size 4) in 
    let y2 = gsub q (size 4) (size 4) in 

    as_nat h x1 < prime256 /\
    as_nat h y1 < prime256 /\
    as_nat h z1 < prime256 /\

    as_nat h x2 < prime256 /\
    as_nat h y2 < prime256 ))
  (ensures fun h0 _ h1 -> modifies (loc tempBuffer) h0 h1 /\ (
    let x1D = fromDomain_ (as_nat h0 (gsub p (size 0) (size 4))) in 
    let x2D = fromDomain_ (as_nat h0 (gsub q (size 0) (size 4))) in 
    let y1D = fromDomain_ (as_nat h0 (gsub p (size 4) (size 4))) in 
    let y2D = fromDomain_ (as_nat h0 (gsub q (size 4) (size 4))) in 
    let z1D = fromDomain_ (as_nat h0 (gsub p (size 8) (size 4))) in 

    let t0 = gsub tempBuffer (size 0) (size 4) in 
    let t1 = gsub tempBuffer (size 4) (size 4) in 
    let t3 = gsub tempBuffer (size 12) (size 4) in 
    let t4 = gsub tempBuffer (size 16) (size 4) in 

    let t0_ = (x1D * x2D) % prime in 
    let t1_ = (y1D * y2D) % prime in 
    let t3_ = (x2D + y2D) % prime in 
    let t4_ = (x1D + y1D) % prime in 

    let t3_ = (t3_ * t4_) % prime in 
    let t4_ = (t0_ + t1_) % prime in 
    let t3_ = (t3_ - t4_) % prime in 
    let t4_ = (y2D - z1D) % prime in 
    
    as_nat h1 t0 = toDomain_ t0_ /\
    as_nat h1 t1 = toDomain_ t1_ /\
    as_nat h1 t3 = toDomain_ t3_ /\
    as_nat h1 t4 = toDomain_ t4_ /\
    
    as_nat h1 t0 < prime /\
    as_nat h1 t1 < prime /\
    as_nat h1 t3 < prime /\
    as_nat h1 t4 < prime))


let point_add_step0 result p q tempBuffer = 
  let x1 = sub p (size 0) (size 4) in 
  let y1 = sub p (size 4) (size 4) in 
  let z1 = sub p (size 8) (size 4) in 

  let x2 = sub q (size 0) (size 4) in 
  let y2 = sub q (size 4) (size 4) in 

  let t0 = sub tempBuffer (size 0) (size 4) in 
  let t1 = sub tempBuffer (size 4) (size 4) in 
  let t3 = sub tempBuffer (size 12) (size 4) in 
  let t4 = sub tempBuffer (size 16) (size 4) in 

  montgomery_multiplication_buffer t0 x1 x2;
  montgomery_multiplication_buffer t1 y1 y2;
  p256_add t3 x2 y2;  
  p256_add t4 x1 y1;
  
  montgomery_multiplication_buffer t3 t3 t4;
  p256_add t4 t0 t1;
  p256_sub t3 t3 t4;
  p256_sub t4 y2 z1


val point_add_step1: result: point -> p: point -> q: pointAffine -> tempBuffer: lbuffer uint64 (size 20) -> Stack unit
  (requires fun h -> live h result /\ live h p /\ live h q /\ live h tempBuffer /\
    disjoint p tempBuffer /\ disjoint q tempBuffer /\ eq_or_disjoint result p /\ disjoint result tempBuffer /\ (
    let t1 = gsub tempBuffer (size 4) (size 4) in 
    let t4 = gsub tempBuffer (size 16) (size 4) in  

    let x1 = gsub p (size 0) (size 4) in 
    let y1 = gsub p (size 4) (size 4) in 
    let z1 = gsub p (size 8) (size 4) in 

    let x2 = gsub q (size 0) (size 4) in 
    let y2 = gsub q (size 4) (size 4) in 

    as_nat h x1 < prime256 /\
    as_nat h y1 < prime256 /\
    as_nat h z1 < prime256 /\

    as_nat h x2 < prime256 /\
    as_nat h y2 < prime256 /\

    as_nat h t1 < prime /\ 
    as_nat h t4 < prime 
  
  ))
  (ensures fun h0 _ h1 -> modifies (loc result |+| loc tempBuffer) h0 h1 /\ (
    let x1D = fromDomain_ (as_nat h0 (gsub p (size 0) (size 4))) in 
    let x2D = fromDomain_ (as_nat h0 (gsub q (size 0) (size 4))) in 
    let y1D = fromDomain_ (as_nat h0 (gsub p (size 4) (size 4))) in 
    let y2D = fromDomain_ (as_nat h0 (gsub q (size 4) (size 4))) in 
    let z1D = fromDomain_ (as_nat h0 (gsub p (size 8) (size 4))) in 

    let x3 = gsub result (size 0) (size 4) in 
    let y3 = gsub result (size 4) (size 4) in 
    let z3 = gsub result (size 8) (size 4) in 

    let t0 = gsub tempBuffer (size 0) (size 4) in 
    let t1 = gsub tempBuffer (size 4) (size 4) in 
    let t3 = gsub tempBuffer (size 12) (size 4) in 
    let t4 = gsub tempBuffer (size 16) (size 4) in 

    let t1D = fromDomain_ (as_nat h0 t1) in 
    let t4D = fromDomain_ (as_nat h0 t4) in 

    let t4_ = (t4D + y1D) % prime in 
    let y3_ = (x2D * z1D) % prime in
    let y3_ = (y3_ + x1D) % prime in 
    let z3_ = (Spec.P256.bCoordinateP256 * z1D) % prime in 

    let x3_ = (y3_ - z3_) % prime in 
    let z3_ = (x3_ + x3_) % prime in 
    let x3_ = (x3_ + z3_)  % prime in 
    let z3_ = (t1D - x3_) % prime in 
    let x3_ = (t1D + x3_) % prime in 
    let y3_ = (Spec.P256.bCoordinateP256 * y3_) % prime in 

    as_nat h1 x3 = toDomain_ x3_ /\ 
    as_nat h1 y3 = toDomain_ y3_ /\
    as_nat h1 z3 = toDomain_ z3_ /\

    as_nat h0 t0 = as_nat h1 t0 /\
    as_nat h0 t1 = as_nat h1 t1 /\
    as_nat h0 t3 = as_nat h1 t3 /\
    as_nat h1 t4 = toDomain_ t4_ /\

    as_nat h1 x3 < prime /\
    as_nat h1 y3 < prime /\
    as_nat h1 z3 < prime /\
    as_nat h1 t4 < prime ))

let point_add_step1 result p q tempBuffer = 
  let x1 = sub p (size 0) (size 4) in 
  let y1 = sub p (size 4) (size 4) in 
  let z1 = sub p (size 8) (size 4) in 

  let x2 = sub q (size 0) (size 4) in 
  let y2 = sub q (size 4) (size 4) in 

  let t0 = sub tempBuffer (size 0) (size 4) in 
  let t1 = sub tempBuffer (size 4) (size 4) in 
  let t2 = sub tempBuffer (size 8) (size 4) in 
  let t3 = sub tempBuffer (size 12) (size 4) in 
  let t4 = sub tempBuffer (size 16) (size 4) in 

  let x3 = sub result (size 0) (size 4) in 
  let y3 = sub result (size 4) (size 4) in 
  let z3 = sub result (size 8) (size 4) in 
  Hacl.Impl.P256.LowLevel.PrimeSpecific.upload_p256_point_on_curve_constant t2;

  p256_add t4 t4 y1; 
  montgomery_multiplication_buffer y3 x2 z1; 
  p256_add y3 y3 x1;
  montgomery_multiplication_buffer z3 t2 z1; 

  
  p256_sub x3 y3 z3;
  p256_add z3 x3 x3;
  p256_add x3 x3 z3; 
  p256_sub z3 t1 x3; 
  p256_add x3 t1 x3; 
  montgomery_multiplication_buffer y3 t2 y3


val point_add_step2: result: point -> p: point -> q: pointAffine -> tempBuffer: lbuffer uint64 (size 20) -> Stack unit
  (requires fun h -> live h result /\ live h p /\ live h q /\ live h tempBuffer /\
    disjoint p tempBuffer /\ disjoint q tempBuffer /\ eq_or_disjoint result p /\ disjoint result tempBuffer /\ (
    let t0 = gsub tempBuffer (size 0) (size 4) in 
    let t1 = gsub tempBuffer (size 4) (size 4) in 
    let t2 = gsub tempBuffer (size 8) (size 4) in 
    let t4 = gsub tempBuffer (size 16) (size 4) in  

    let x1 = gsub p (size 0) (size 4) in 
    let y1 = gsub p (size 4) (size 4) in 
    let z1 = gsub p (size 8) (size 4) in 

    let x2 = gsub q (size 0) (size 4) in 
    let y2 = gsub q (size 4) (size 4) in 

    let x3 = gsub result (size 0) (size 4) in 
    let y3 = gsub result (size 4) (size 4) in 
    let z3 = gsub result (size 8) (size 4) in 

    as_nat h x1 < prime256 /\
    as_nat h y1 < prime256 /\
    as_nat h z1 < prime256 /\

    as_nat h x2 < prime256 /\
    as_nat h y2 < prime256 /\

    as_nat h x3 < prime256 /\
    as_nat h y3 < prime256 /\
    as_nat h z3 < prime256 /\

    as_nat h t0 < prime /\
    as_nat h t1 < prime /\ 
    as_nat h t2 < prime /\
    as_nat h t4 < prime))
  (ensures fun h0 _ h1 -> modifies (loc result |+| loc tempBuffer) h0 h1 /\ (
    let z1D = fromDomain_ (as_nat h0 (gsub p (size 8) (size 4))) in 
    let y3D = fromDomain_ (as_nat h0 (gsub result (size 4) (size 4))) in 

    let x3 = gsub result (size 0) (size 4) in 
    let y3 = gsub result (size 4) (size 4) in 
    let z3 = gsub result (size 8) (size 4) in 

    let t0 = gsub tempBuffer (size 0) (size 4) in 
    let t1 = gsub tempBuffer (size 4) (size 4) in 
    let t2 = gsub tempBuffer (size 8) (size 4) in 
    let t3 = gsub tempBuffer (size 12) (size 4) in 
    let t4 = gsub tempBuffer (size 16) (size 4) in 

    let t0D = fromDomain_ (as_nat h0 t0) in 
    let t4D = fromDomain_ (as_nat h0 t4) in 

    let t1_ = (z1D + z1D) % prime in 
    let t2_ = (t1_ + z1D) % prime in 
    let y3_ = (y3D - t2_) % prime in 
    let y3_ = (y3_ - t0D) % prime in 
    let t1_ = (y3_ + y3_) % prime in 

    let y3_ = (t1_ + y3_) % prime in 
    let t1_ = (t0D + t0D) % prime in 
    let t0_ = (t1_ + t0D) % prime in 
    let t0_ = (t0_ - t2_) % prime in 
    let t1_ = (t4D * y3_) % prime in 

    as_nat h1 t0 = toDomain_ t0_ /\
    as_nat h1 t1 = toDomain_ t1_ /\
    as_nat h1 t2 = toDomain_ t2_ /\
    as_nat h1 t3 = as_nat h0 t3 /\
    as_nat h1 t4 = as_nat h0 t4 /\

    as_nat h1 x3 = as_nat h0 x3 /\
    as_nat h1 y3 = toDomain_ y3_ /\
    as_nat h1 z3 = as_nat h0 z3 /\

    as_nat h1 t0 < prime /\
    as_nat h1 t1 < prime /\
    as_nat h1 t2 < prime /\

    as_nat h1 y3 < prime))


let point_add_step2 result p q tempBuffer = 
  let x1 = sub p (size 0) (size 4) in 
  let y1 = sub p (size 4) (size 4) in 
  let z1 = sub p (size 8) (size 4) in 

  let x2 = sub q (size 0) (size 4) in 
  let y2 = sub q (size 4) (size 4) in 

  let t0 = sub tempBuffer (size 0) (size 4) in 
  let t1 = sub tempBuffer (size 4) (size 4) in 
  let t2 = sub tempBuffer (size 8) (size 4) in 
  let t3 = sub tempBuffer (size 12) (size 4) in 
  let t4 = sub tempBuffer (size 16) (size 4) in 

  let x3 = sub result (size 0) (size 4) in 
  let y3 = sub result (size 4) (size 4) in 
  let z3 = sub result (size 8) (size 4) in 

  p256_add t1 z1 z1;
  p256_add t2 t1 z1;
  p256_sub y3 y3 t2;
  p256_sub y3 y3 t0;
  p256_add t1 y3 y3;

  p256_add y3 t1 y3;
  p256_add t1 t0 t0;
  p256_add t0 t1 t0;
  p256_sub t0 t0 t2;
  montgomery_multiplication_buffer t1 t4 y3


val point_add_step3: result: point -> p: point -> q: pointAffine -> tempBuffer: lbuffer uint64 (size 20) -> Stack unit
  (requires fun h -> live h result /\ live h p /\ live h q /\ live h tempBuffer /\
    disjoint p tempBuffer /\ disjoint q tempBuffer /\ eq_or_disjoint result p /\ disjoint result tempBuffer /\ (
    let t0 = gsub tempBuffer (size 0) (size 4) in 
    let t1 = gsub tempBuffer (size 4) (size 4) in 
    let t2 = gsub tempBuffer (size 8) (size 4) in 
    let t3 = gsub tempBuffer (size 12) (size 4) in 
    let t4 = gsub tempBuffer (size 16) (size 4) in  

    let x1 = gsub p (size 0) (size 4) in 
    let y1 = gsub p (size 4) (size 4) in 
    let z1 = gsub p (size 8) (size 4) in 

    let x2 = gsub q (size 0) (size 4) in 
    let y2 = gsub q (size 4) (size 4) in 

    let x3 = gsub result (size 0) (size 4) in 
    let y3 = gsub result (size 4) (size 4) in 
    let z3 = gsub result (size 8) (size 4) in 

    as_nat h x1 < prime256 /\
    as_nat h y1 < prime256 /\
    as_nat h z1 < prime256 /\

    as_nat h x2 < prime256 /\
    as_nat h y2 < prime256 /\

    as_nat h x3 < prime256 /\
    as_nat h y3 < prime256 /\
    as_nat h z3 < prime256 /\

    as_nat h t0 < prime /\
    as_nat h t1 < prime /\ 
    as_nat h t2 < prime /\
    as_nat h t3 < prime /\
    as_nat h t4 < prime))
  (ensures fun h0 _ h1 -> modifies (loc result |+| loc tempBuffer) h0 h1 /\ (
    let x3 = gsub result (size 0) (size 4) in 
    let y3 = gsub result (size 4) (size 4) in 
    let z3 = gsub result (size 8) (size 4) in 

    let x3D = fromDomain_ (as_nat h0 x3) in 
    let y3D = fromDomain_ (as_nat h0 y3) in 
    let z3D = fromDomain_ (as_nat h0 z3) in 

    let t0 = gsub tempBuffer (size 0) (size 4) in 
    let t1 = gsub tempBuffer (size 4) (size 4) in 
    let t2 = gsub tempBuffer (size 8) (size 4) in 
    let t3 = gsub tempBuffer (size 12) (size 4) in 
    let t4 = gsub tempBuffer (size 16) (size 4) in   

    let t0D = fromDomain_ (as_nat h0 t0) in 
    let t1D = fromDomain_ (as_nat h0 t1) in 
    let t3D = fromDomain_ (as_nat h0 t3) in 
    let t4D = fromDomain_ (as_nat h0 t4) in 
    

    let t2_ = (t0D * y3D) % prime in
    let y3_ = (x3D * z3D) % prime in 
    let y3_ = (y3_ + t2_) % prime in 
    let x3_ = (t3D * x3D) % prime in 

    let x3_ = (x3_ - t1D) % prime in 
    let z3_ = (t4D * z3D) % prime in 
    let t1_ = (t3D * t0D) % prime in 
    let z3_ = (z3_ * t1_) % prime in 

    as_nat h1 t1 = toDomain_ t1_ /\
    as_nat h1 t2 = toDomain_ t2_ /\
   
    as_nat h1 x3 = toDomain_ x3_ /\ 
    as_nat h1 y3 = toDomain_ y3_ /\
    as_nat h1 z3 = toDomain_ z3_ /\

    as_nat h1 x3 < prime /\
    as_nat h1 y3 < prime /\
    as_nat h1 z3 < prime ))


let point_add_step3 result p q tempBuffer = 
  let x1 = sub p (size 0) (size 4) in 
  let y1 = sub p (size 4) (size 4) in 
  let z1 = sub p (size 8) (size 4) in 

  let x2 = sub q (size 0) (size 4) in 
  let y2 = sub q (size 4) (size 4) in 

  let t0 = sub tempBuffer (size 0) (size 4) in 
  let t1 = sub tempBuffer (size 4) (size 4) in 
  let t2 = sub tempBuffer (size 8) (size 4) in 
  let t3 = sub tempBuffer (size 12) (size 4) in 
  let t4 = sub tempBuffer (size 16) (size 4) in 

  let x3 = sub result (size 0) (size 4) in 
  let y3 = sub result (size 4) (size 4) in 
  let z3 = sub result (size 8) (size 4) in 

  montgomery_multiplication_buffer t2 t0 y3;
  montgomery_multiplication_buffer y3 x3 z3;
  p256_add y3 y3 t2;
  montgomery_multiplication_buffer x3 t3 x3;

  p256_sub x3 x3 t1;
  montgomery_multiplication_buffer z3 t4 z3;
  montgomery_multiplication_buffer t1 t3 t0;
  montgomery_multiplication_buffer z3 z3 t1




(* we expect that we already know the q point *)
val pointAddMixed: result: point -> p: point -> q: pointAffine -> Stack unit 
  (requires fun h -> live h result /\ live h p /\ live h q /\ eq_or_disjoint result p
  )
  (ensures fun h0 _ h1 -> True)


let pointAddMixed result p q = 
  push_frame();
    let tempBuffer = create (size 20) (u64 0) in 
    point_add_step0 result p q tempBuffer;
    point_add_step1 result p q tempBuffer;
    point_add_step2 result p q tempBuffer;
    point_add_step3 result p q tempBuffer;
    copy_point_conditional result q p;
  pop_frame()
