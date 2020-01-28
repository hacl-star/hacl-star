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
open Hacl.Impl.ECDSA.MontgomeryMultiplication

open Hacl.Impl.P256.LowLevel
open Hacl.Impl.P256


#set-options "--z3rlimit 100"

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


(* 
  checks whether the coordinates are valid = 
  all of them are less than prime 
*) 


(* checks whether the intefer f is between 1 and (n- 1) (incl).  *)
(* [1, n - 1] <==> a > 0 /\ a < n) *)

val isMoreThanZeroLessThanOrderMinusOne: f: felem -> Stack bool
  (requires fun h -> live h f)
  (ensures fun h0 result h1 -> modifies0 h0 h1 /\
    (
      if as_nat h0 f > 0 && as_nat h0 f < prime_p256_order then result == true else result == false
    )  
  )

let isMoreThanZeroLessThanOrderMinusOne f = 
  push_frame();
    let tempBuffer = create (size 4) (u64 0) in 
        recall_contents prime256order_buffer (Lib.Sequence.of_list p256_order_prime_list);
    let carry = sub4_il f prime256order_buffer tempBuffer in  
    let less = eq_u64_nCT carry (u64 1) in
    let more = isZero_uint64_nCT f in 
    let result = less && not more in 
  pop_frame();  
    result


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
    let result = Hacl.Impl.P256.isPointAtInfinityPublic multResult in  
   pop_frame();
     result


(*
For Bob to authenticate Alice's signature, he must have a copy of her public-key curve point {\displaystyle Q_{A}} Q_{A}. Bob can verify {\displaystyle Q_{A}} Q_{A} is a valid curve point as follows:

Check that {\displaystyle Q_{A}} Q_{A} is not equal to the identity element {\displaystyle O} O, and its coordinates are otherwise valid
Check that {\displaystyle Q_{A}} Q_{A} lies on the curve
Check that {\displaystyle n\times Q_{A}=O} n\times Q_{A}=O
 *)
 
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
    let belongsToCurve =  Hacl.Impl.P256.isPointOnCurvePublic pubKeyAsPoint in 
    let orderCorrect = isOrderCorrect pubKeyAsPoint tempBuffer in 
    if coordinatesValid && belongsToCurve && orderCorrect 
      then true 
    else false  
