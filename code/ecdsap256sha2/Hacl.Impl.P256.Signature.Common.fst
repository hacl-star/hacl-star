module Hacl.Impl.P256.Signature.Common

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.ByteBuffer 
open Lib.ByteSequence
open Lib.Buffer 

open Hacl.Spec.P256 
open Hacl.Spec.P256.Definitions

open Hacl.Spec.ECDSA
open Hacl.Spec.ECDSAP256.Definition

open Hacl.Impl.LowLevel
open Hacl.Impl.P256.MontgomeryMultiplication
open Hacl.Impl.ECDSA.MontgomeryMultiplication

open Hacl.Impl.P256.LowLevel
open Hacl.Impl.P256

open Hacl.Math
open FStar.Math.Lemmas
open FStar.Mul

open Hacl.Impl.P256.Arithmetics


#set-options "--z3rlimit 100"

(* This code is not side channel resistant *)
(* inline_for_extraction noextract *)
val eq_u64_nCT:a:uint64 -> b:uint64 -> Tot (r: bool {if uint_v a = uint_v b then r == true else r == false})

(* This code is not side channel resistant *)
let eq_u64_nCT a b =
  let open Lib.RawIntTypes in
  FStar.UInt64.(u64_to_UInt64 a =^ u64_to_UInt64 b)


(* This code is not side channel resistant *)
(* inline_for_extraction noextract *)
val eq_0_u64: a: uint64 -> Tot (r: bool {if uint_v a = 0 then r == true else r == false})

(* This code is not side channel resistant *)
let eq_0_u64 a = eq_u64_nCT a (u64 0)


val changeEndian: i: felem -> Stack unit 
  (requires fun h -> live h i)
  (ensures fun h0 _ h1 -> modifies1 i h0 h1 /\ as_seq h1 i == Hacl.Spec.ECDSA.changeEndian (as_seq h0 i)) 

let changeEndian i = 
  let zero = index i (size 0) in 
  let one = index i (size 1) in 
  let two = index i (size 2) in 
  let three = index i (size 3) in 
  upd i (size 0) three;
  upd i (size 1) two; 
  upd i (size 2) one;
  upd i (size 3) zero


val toUint64ChangeEndian: i: lbuffer uint8 (32ul) -> o: felem ->  Stack unit
  (requires fun h -> live h i /\ live h o /\ disjoint i o)
  (ensures fun h0 _ h1 -> 
    modifies (loc o) h0 h1 /\ 
    as_seq h1 o == Hacl.Spec.ECDSA.changeEndian(Lib.ByteSequence.uints_from_bytes_be #_ #_ #4 (as_seq h0 i))
  )

let toUint64ChangeEndian i o = 
  Lib.ByteBuffer.uints_from_bytes_be o i;
  changeEndian o


val lemma_core_0: a: lbuffer uint64 (size 4) -> h: mem -> Lemma (nat_from_intseq_le (as_seq h a) == as_nat h a)

let lemma_core_0 a h = 
  let k = as_seq h a in 
  let z = nat_from_intseq_le k in 
    nat_from_intseq_le_slice_lemma k 1;
    nat_from_intseq_le_lemma0 (Seq.slice k 0 1);
  let k1 = Seq.slice k 1 4 in 
    nat_from_intseq_le_slice_lemma #_ #_ #3 k1 1;
    nat_from_intseq_le_lemma0 (Seq.slice k1 0 1);
  let k2 = Seq.slice k1 1 3 in 
    nat_from_intseq_le_slice_lemma #_ #_ #2 k2 1;
    nat_from_intseq_le_lemma0 (Seq.slice k2 0 1);
    nat_from_intseq_le_lemma0 (Seq.slice k2 1 2)


val lemma_core_1: a: lbuffer uint64 (size 4) -> h: mem -> 
  Lemma (nat_from_bytes_le (Lib.ByteSequence.uints_to_bytes_le (as_seq h a)) == as_nat h a)

let lemma_core_1 a h= 
  let open Lib.ByteSequence in 
  lemma_core_0 a h;
  lemma_nat_from_to_intseq_le_preserves_value #U64 #SEC 4 (as_seq h a);
  let n = nat_from_intseq_le (as_seq h a) in 
  uints_to_bytes_le_nat_lemma #U64 #SEC 4 n;
  lemma_nat_to_from_bytes_le_preserves_value #SEC (uints_to_bytes_le #U64 #SEC #4 (as_seq h a)) 32 (as_nat h a)


val bufferToJac: p: lbuffer uint64 (size 8) -> result: point -> Stack unit 
  (requires fun h -> live h p /\ live h result /\ disjoint p result)
  (ensures fun h0 _ h1 -> 
    modifies (loc result) h0 h1 /\ as_nat h1 (gsub result (size 8) (size 4)) == 1 /\ 
    (
      let x = as_nat h0 (gsub p (size 0) (size 4)) in 
      let y = as_nat h0 (gsub p (size 4) (size 4)) in 
      let x3, y3, z3 = point_x_as_nat h1 result,  point_y_as_nat h1 result, point_z_as_nat h1 result in 
      let pointJacX, pointJacY, pointJacZ = toJacobianCoordinates (x, y) in 
      x3 == pointJacX /\ y3 == pointJacY /\ z3 == pointJacZ
    )
  )    
    
let bufferToJac p result = 
  let partPoint = sub result (size 0) (size 8) in 
  copy partPoint p;
  upd result (size 8) (u64 1);
  upd result (size 9) (u64 0);
  upd result (size 10) (u64 0);
  upd result (size 11) (u64 0)



inline_for_extraction noextract
val y_2: y: felem -> r: felem -> Stack unit
  (requires fun h -> as_nat h y < prime /\  live h y /\ live h r /\ eq_or_disjoint y r)
  (ensures fun h0 _ h1 -> modifies (loc r) h0 h1 /\ as_nat h1 r == toDomain_ ((as_nat h0 y) * (as_nat h0 y) % prime))

let y_2 y r = 
  toDomain y r;
  montgomery_multiplication_buffer r r r


inline_for_extraction noextract
val upload_p256_point_on_curve_constant: x: felem -> Stack unit
  (requires fun h -> live h x)
  (ensures fun h0 _ h1 -> modifies (loc x) h0 h1 /\ 
    as_nat h1 x == toDomain_ (41058363725152142129326129780047268409114441015993725554835256314039467401291) /\
    as_nat h1 x < prime
 )

let upload_p256_point_on_curve_constant x = 
  upd x (size 0) (u64 15608596021259845087);
  upd x (size 1) (u64 12461466548982526096);
  upd x (size 2) (u64 16546823903870267094);
  upd x (size 3) (u64 15866188208926050356);
    let h1 = ST.get() in 
  assert_norm (
    15608596021259845087 + 12461466548982526096 * pow2 64 + 
    16546823903870267094 * pow2 64 * pow2 64 + 
    15866188208926050356 * pow2 64 * pow2 64 * pow2 64 == (41058363725152142129326129780047268409114441015993725554835256314039467401291 * pow2 256) % prime)


val lemma_xcube: x_: nat {x_ < prime} -> Lemma 
  (((x_ * x_ * x_ % prime) - (3 * x_ % prime)) % prime == (x_ * x_ * x_ - 3* x_) % prime)

let lemma_xcube x_ = 
  lemma_mod_add_distr (- (3 * x_ % prime)) (x_ * x_ * x_) prime;
  lemma_mod_sub_distr (x_ * x_ * x_ ) (3 * x_) prime


val lemma_xcube2: x_ : nat {x_ < prime} -> Lemma 
  (toDomain_ ((((((x_ * x_ * x_) - (3 * x_)) % prime)) + 41058363725152142129326129780047268409114441015993725554835256314039467401291) % prime) == 
    toDomain_ ((x_ * x_ * x_ - 3 * x_ + 41058363725152142129326129780047268409114441015993725554835256314039467401291) % prime))

let lemma_xcube2 x_ = 
  lemma_mod_add_distr 41058363725152142129326129780047268409114441015993725554835256314039467401291 ((x_ * x_ * x_) - (3 * x_)) prime;
  assert(((((x_ * x_ * x_) - (3 * x_)) % prime) + 41058363725152142129326129780047268409114441015993725554835256314039467401291) % prime == (x_ * x_ * x_ - 3 * x_ + 41058363725152142129326129780047268409114441015993725554835256314039467401291) % prime)


inline_for_extraction noextract
val xcube_minus_x: x: felem ->r: felem -> Stack unit 
  (requires fun h -> as_nat h x < prime /\ live h x  /\ live h r /\ eq_or_disjoint x r)
  (ensures fun h0 _ h1 -> 
    modifies (loc r) h0 h1 /\
    (
      let x_ = as_nat h0 x in 
      as_nat h1 r =  toDomain_((x_ * x_ * x_ - 3 * x_ + 41058363725152142129326129780047268409114441015993725554835256314039467401291) % prime))
  )


let xcube_minus_x x r = 
  push_frame();
      let h0 = ST.get() in 
    let xToDomainBuffer = create (size 4) (u64 0) in 
    let minusThreeXBuffer = create (size 4) (u64 0) in 
    let p256_constant = create (size 4) (u64 0) in 
  toDomain x xToDomainBuffer;
  montgomery_multiplication_buffer xToDomainBuffer xToDomainBuffer r;
  montgomery_multiplication_buffer r xToDomainBuffer r;
    lemma_mod_mul_distr_l ((as_nat h0 x) * (as_nat h0 x)) (as_nat h0 x) prime;
  multByThree xToDomainBuffer minusThreeXBuffer;
  p256_sub r minusThreeXBuffer r;
    upload_p256_point_on_curve_constant p256_constant;
  p256_add r p256_constant r;
  pop_frame(); 
  
    let x_ = as_nat h0 x in 
    assert_norm (41058363725152142129326129780047268409114441015993725554835256314039467401291 < prime);
    lemma_xcube x_;
    lemma_mod_add_distr 41058363725152142129326129780047268409114441015993725554835256314039467401291 ((x_ * x_ * x_) - (3 * x_)) prime;
    lemma_xcube2 x_



val isPointAtInfinityPublic: p: point -> Stack bool
  (requires fun h -> live h p)
  (ensures fun h0 r h1 -> modifies0 h0 h1 /\ 
    (
      let x, y, z = point_prime_to_coordinates (as_seq h0 p) in 
      r == Hacl.Spec.P256.isPointAtInfinity (x, y, z)
    )
  ) 


let isPointAtInfinityPublic p =  
  let z0 = index p (size 8) in 
  let z1 = index p (size 9) in 
  let z2 = index p (size 10) in 
  let z3 = index p (size 11) in 
  let z0_zero = eq_0_u64 z0 in 
  let z1_zero = eq_0_u64 z1 in 
  let z2_zero = eq_0_u64 z2 in 
  let z3_zero = eq_0_u64 z3 in 
  z0_zero && z1_zero && z2_zero && z3_zero


val lemma_modular_multiplication_p256_2_d: a: nat{a < prime256} -> b: nat {b < prime256} -> 
  Lemma 
    (toDomain_ a = toDomain_ b <==> a == b)

let lemma_modular_multiplication_p256_2_d a b = 
   lemmaToDomain a;
     assert(toDomain_ a = a * pow2 256 % prime);
   lemmaToDomain b;
     assert(toDomain_ b = b * pow2 256 % prime);
   lemma_modular_multiplication_p256_2 a b;
     assert(toDomain_ a = toDomain_ b ==> a == b)


val isPointOnCurvePublic: p: point -> Stack bool
  (requires fun h -> live h p /\    
    as_nat h (gsub p (size 0) (size 4)) < prime /\ 
    as_nat h (gsub p (size 4) (size 4)) < prime /\
    as_nat h (gsub p (size 8) (size 4)) == 1)

  (ensures fun h0 r h1 ->      
    modifies0 h0 h1 /\ 
    (
      let x = gsub p (size 0) (size 4) in 
      let y = gsub p (size 4) (size 4) in 
      let x_ = as_nat h0 x in  
      if r = false 
  then (as_nat h0 y) * (as_nat h0 y) % prime <>  (x_ * x_ * x_ - 3 * x_ + 41058363725152142129326129780047268409114441015993725554835256314039467401291) % prime
       else (as_nat h0 y) * (as_nat h0 y) % prime == (x_ * x_ * x_ - 3 * x_ + 41058363725152142129326129780047268409114441015993725554835256314039467401291) % prime) /\
      r == isPointOnCurve (
      as_nat h1 (gsub p (size 0) (size 4)), as_nat h1 (gsub p (size 4) (size 4)), as_nat h1 (gsub p (size 8) (size 4))
  ) 
)

let isPointOnCurvePublic p = 
   push_frame(); 
     let y2Buffer = create (size 4) (u64 0) in 
     let xBuffer = create (size 4) (u64 0) in 
       let h0 = ST.get() in 
     let x = sub p (size 0) (size 4) in 
     let y = sub p (size 4) (size 4) in 
     y_2 y y2Buffer;
     xcube_minus_x x xBuffer;
       let h1 = ST.get() in 
     let r = compare_felem y2Buffer xBuffer in 
     let z = eq_0_u64 r in 
     assert(if uint_v r = pow2 64 -1 then as_nat h1 y2Buffer == as_nat h1 xBuffer else as_nat h1 y2Buffer <> as_nat h1 xBuffer);
     lemma_modular_multiplication_p256_2_d ((as_nat h0 y) * (as_nat h0 y) % prime) 
       (let x_ = as_nat h0 x in (x_ * x_ * x_ - 3 * x_ + 41058363725152142129326129780047268409114441015993725554835256314039467401291) % prime);
     assert(let x_ = as_nat h0 x in 
       if uint_v r = pow2 64 - 1 then   
    (as_nat h0 y) * (as_nat h0 y) % prime ==  (x_ * x_ * x_ - 3 * x_ + 41058363725152142129326129780047268409114441015993725554835256314039467401291) % prime else    
    (as_nat h0 y) * (as_nat h0 y) % prime <>  (x_ * x_ * x_ - 3 * x_ + 41058363725152142129326129780047268409114441015993725554835256314039467401291) % prime);
     let z = not(eq_0_u64 r) in 
     pop_frame();
     z



(* 
  checks whether the coordinates are valid = 
  all of them are less than prime 
*) 

(* checks whether the intefer f is between 1 and (n- 1) (incl).  *)
(* [1, n - 1] <==> a > 0 /\ a < n) *)

(* This code is not side channel resistant *)
(* we require the coordinate to be in affine representation of jac coordinate *)
val isCoordinateValid: p: point -> Stack bool 
  (requires fun h -> live h p /\ point_z_as_nat h p == 1)
  (ensures fun h0 r h1 -> 
    modifies0 h0 h1  /\ 
    (
      if (point_x_as_nat h0 p < prime256 && point_y_as_nat h0 p < prime256 && point_z_as_nat h0 p < prime256) then r == true else r == false
    )  
  )

let isCoordinateValid p = 
  push_frame();
    let tempBuffer = create (size 4) (u64 0) in 
      recall_contents prime256_buffer (Lib.Sequence.of_list p256_prime_list);
    let x = sub p (size 0) (size 4) in 
    let y = sub p (size 4) (size 4) in 
    
    let carryX = sub4_il x prime256_buffer tempBuffer in
    let carryY = sub4_il y prime256_buffer tempBuffer in 
    
    let lessX = eq_u64_nCT carryX (u64 1) in   
    let lessY = eq_u64_nCT carryY (u64 1) in 

    let r = lessX && lessY in 
  pop_frame();
    r  


inline_for_extraction noextract
val multByOrder: result: point ->  p: point -> tempBuffer: lbuffer uint64 (size 100) -> Stack unit 
  (requires fun h -> 
    live h result /\ live h p /\ live h tempBuffer /\
    LowStar.Monotonic.Buffer.all_disjoint [loc result; loc p; loc tempBuffer] /\
    point_x_as_nat h p < prime256 /\ 
    point_y_as_nat h p < prime256 /\
    point_z_as_nat h p < prime256
  )
  (ensures fun h0 _ h1 ->
    modifies (loc result |+| loc p |+| loc tempBuffer) h0 h1 /\
    (
      let xN, yN, zN = scalar_multiplication prime_p256_order_seq (point_prime_to_coordinates (as_seq h0 p)) in 
      let x3, y3, z3 = point_x_as_nat h1 result, point_y_as_nat h1 result, point_z_as_nat h1 result in 
      x3 == xN /\ y3 == yN /\ z3 == zN 
    ) 
  )

let multByOrder result p tempBuffer =
  push_frame();
      recall_contents order_buffer prime_p256_order_seq;
    scalarMultiplication p result order_buffer tempBuffer;
  pop_frame()


inline_for_extraction noextract
val multByOrder2: result: point ->  p: point -> tempBuffer: lbuffer uint64 (size 100) -> Stack unit 
  (requires fun h -> 
    live h result /\ live h p /\ live h tempBuffer /\
    LowStar.Monotonic.Buffer.all_disjoint [loc result; loc p; loc tempBuffer] /\
    point_x_as_nat h p < prime256 /\ 
    point_y_as_nat h p < prime256 /\
    point_z_as_nat h p < prime256
  )
  (ensures fun h0 _ h1  -> modifies (loc result |+| loc tempBuffer) h0 h1 /\
    (
      let xN, yN, zN = scalar_multiplication prime_p256_order_seq (point_prime_to_coordinates (as_seq h0 p)) in 
      let x3, y3, z3 = point_x_as_nat h1 result, point_y_as_nat h1 result, point_z_as_nat h1 result in 
      x3 == xN /\ y3 == yN /\ z3 == zN 
    )
  )

let multByOrder2 result p tempBuffer = 
  push_frame();
    let pBuffer = create (size 12) (u64 0) in 
    copy pBuffer p;
    multByOrder result pBuffer tempBuffer;
  pop_frame()  
    

(*checks whether the base point * order is point at infinity *)
val isOrderCorrect: p: point -> tempBuffer: lbuffer uint64 (size 100) -> Stack bool
  (requires fun h -> 
    live h p /\ live h tempBuffer /\ 
    disjoint p tempBuffer /\
    point_x_as_nat h p < prime256 /\ 
    point_y_as_nat h p < prime256 /\
    point_z_as_nat h p < prime256
  )
  (ensures fun h0 r h1 -> 
    modifies(loc tempBuffer) h0 h1 /\ 
    (
      let (xN, yN, zN) = scalar_multiplication prime_p256_order_seq (point_prime_to_coordinates (as_seq h0 p)) in 
      if Hacl.Spec.P256.isPointAtInfinity (xN, yN, zN) then r == true else r == false
    )
  )

let isOrderCorrect p tempBuffer = 
  push_frame(); 
    let multResult = create (size 12) (u64 0) in 
    multByOrder2 multResult p tempBuffer;
    let result = isPointAtInfinityPublic multResult in  
   pop_frame();
     result


(*
For Bob to authenticate Alice's signature, he must have a copy of her public-key curve point {\displaystyle Q_{A}} Q_{A}. Bob can verify {\displaystyle Q_{A}} Q_{A} is a valid curve point as follows:

Check that {\displaystyle Q_{A}} Q_{A} is not equal to the identity element {\displaystyle O} O, and its coordinates are otherwise valid
Check that {\displaystyle Q_{A}} Q_{A} lies on the curve
Check that {\displaystyle n\times Q_{A}=O} n\times Q_{A}=O
*)

(* This code is not side channel resistant *) 
val verifyQValidCurvePoint: pubKeyAsPoint: point -> tempBuffer: lbuffer uint64 (size 100) -> Stack bool
  (requires fun h -> 
    live h pubKeyAsPoint /\ live h tempBuffer /\
    LowStar.Monotonic.Buffer.all_disjoint [loc pubKeyAsPoint; loc tempBuffer] /\
    point_z_as_nat h pubKeyAsPoint == 1
  )
  (ensures fun h0 r h1 -> 
    modifies (loc tempBuffer) h0 h1 /\ 
    r == verifyQValidCurvePointSpec (point_prime_to_coordinates (as_seq h0 pubKeyAsPoint))
  ) 

let verifyQValidCurvePoint pubKeyAsPoint tempBuffer = 
    let coordinatesValid = isCoordinateValid pubKeyAsPoint in 
      if not coordinatesValid then false else
    let belongsToCurve = isPointOnCurvePublic pubKeyAsPoint in 
    let orderCorrect = isOrderCorrect pubKeyAsPoint tempBuffer in 
    if coordinatesValid && belongsToCurve && orderCorrect 
      then true 
    else false  


