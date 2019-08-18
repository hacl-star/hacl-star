module Hacl.Impl.ECDSA.P256SHA256.Verification

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer

open Hacl.Spec.P256.Definitions
open Hacl.Impl.LowLevel
open Hacl.Impl.P256
open Hacl.Impl.MontgomeryMultiplication
open Hacl.Spec.P256.MontgomeryMultiplication
open Hacl.Impl.MM.Exponent
open Hacl.Spec.P256.Core
open Hacl.Spec.ECDSAP256.Definition
open Hacl.Spec.ECDSA
open Hacl.Spec.P256 
open Hacl.Spec.P256.Ladder

open Hacl.Hash.SHA2

val bufferToJac: p: lbuffer uint64 (size 8) -> result: point -> Stack unit 
  (requires fun h -> live h p /\ live h result /\ disjoint p result)
  (ensures fun h0 _ h1 -> modifies (loc result) h0 h1 /\ as_nat h1 (gsub result (size 8) (size 4)) == 1 /\ 
    as_seq h0 (gsub p (size 0) (size 8)) == as_seq h1 (gsub result (size 0) (size 8)) /\
    (
      let x = as_nat h0 (gsub p (size 0) (size 4)) in 
      let y = as_nat h0 (gsub p (size 4) (size 4)) in 

      let xJ, yJ, zJ = toJacobianCoordinates (x, y) in 
      xJ == as_nat h1 (gsub result (size 0) (size 4)) /\ 
      yJ == as_nat h1 (gsub result (size 4) (size 4)) /\ 
      zJ == as_nat h1 (gsub result (size 8) (size 4)) 
    )
)    
    
let bufferToJac p result = 
  let partPoint = sub result (size 0) (size 8) in 
  copy partPoint p;
  upd result (size 8) (u64 1);
  upd result (size 9) (u64 0);
  upd result (size 10) (u64 0);
  upd result (size 11) (u64 0)


(* checks whether the coordinates are valid = 
   all of them are less than prime 
*) 

(* we require the coordinate to be in affine representation of jac coordinate *)
val isCoordinateValid: p: lbuffer uint64 (size 12) -> Stack bool 
  (requires fun h -> live h p /\
    (
      let z = gsub p (size 8) (size 4) in 
      as_nat h z == 1
    )
  )
  (ensures fun h0 r h1 -> modifies0 h0 h1  /\ 
    (
      let x = gsub p (size 0) (size 4) in 
      let y = gsub p (size 4) (size 4) in 
      let z = gsub p (size 8) (size 4) in 
      if (as_nat h0 x < prime256 &&  as_nat h0 y < prime256 && as_nat h0 z < prime256) then r == true else r == false
  )  
)

#reset-options "--z3refresh --z3rlimit 300"

open FStar.Mul 

  let isCoordinateValid p = 
  push_frame();
    let tempBuffer = create (size 4) (u64 0) in 
    recall_contents prime256_buffer (Lib.Sequence.of_list p256_prime_list);
    let x = sub p (size 0) (size 4) in 
    let y = sub p (size 4) (size 4) in 
    let z = sub p (size 8) (size 4) in 
      let h0 = ST.get() in 
      assert(felem_seq_as_nat (as_seq h0 prime256_buffer) == prime256);
    let carryX = sub4_il x prime256_buffer tempBuffer in
    let carryY = sub4_il y prime256_buffer tempBuffer in 
    let carryZ = sub4_il z prime256_buffer tempBuffer in 
      
      let h1 = ST.get() in 
      assert(modifies1 tempBuffer h0 h1);
      assert(if uint_v carryX = 1 then as_nat h0 x < prime256 else True); 
      assert(if uint_v carryY = 1 then as_nat h0 y < prime256 else True); 
      assert(if uint_v carryZ = 1 then as_nat h0 z < prime256 else True);

    let lessX = eq_u64 carryX (u64 1) in   
    let lessY = eq_u64 carryY (u64 1) in 
    let lessZ = eq_u64 carryZ (u64 1) in 

    let r = lessX && lessY && lessZ in 
      assert(r = true ==> as_nat h0 x < prime256 /\ as_nat h0 y < prime256 /\ as_nat h0 z < prime256);
    pop_frame();
    r  


inline_for_extraction noextract
val equalZeroBuffer: f: felem -> Stack bool
  (requires fun h -> live h f)
  (ensures fun h0 r h1 -> modifies0 h0 h1 /\ (if as_nat h0 f = 0 then r == true else r == false ))

let equalZeroBuffer f =        
    let f0 = index f (size 0) in  
    let f1 = index f (size 1) in 
    let f2 = index f (size 2) in 
    let f3 = index f (size 3) in 

    let z0_zero = eq_0_u64 f0 in 
    let z1_zero = eq_0_u64 f1 in 
    let z2_zero = eq_0_u64 f2 in 
    let z3_zero = eq_0_u64 f3 in 
  
    z0_zero && z1_zero && z2_zero && z3_zero
  

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
    let h0 = ST.get() in 
    let tempBuffer = create (size 4) (u64 0) in 
        recall_contents prime256order_buffer (Lib.Sequence.of_list p256_order_prime_list);
	let h0 = ST.get() in 
    let carry = sub4_il f prime256order_buffer tempBuffer in  
      assert(if uint_v carry = 1 then as_nat h0 f < prime_p256_order else True);
	let h1 = ST.get() in 
	assert(modifies1 tempBuffer h0 h1);
    let less = eq_u64 carry (u64 1) in
      assert(less == true ==> as_nat h0 f < prime_p256_order);
	let h2 = ST.get() in 
    let more = equalZeroBuffer f in 
      assert(not more == true ==> as_nat h0 f > 0);
    let result = less &&  not more in 
      assert(less && not more ==> as_nat h0 f > 0 && as_nat h0 f < prime_p256_order);
  pop_frame();  
    result


inline_for_extraction noextract
val multByOrder: p: point -> result: point ->  tempBuffer: lbuffer uint64 (size 100) -> Stack unit 
  (requires fun h -> live h p /\ live h result /\ live h tempBuffer /\
     as_nat h (gsub p (size 0) (size 4)) < prime256 /\ 
    as_nat h (gsub p (size 4) (size 4)) < prime256 /\
    as_nat h (gsub p (size 8) (size 4)) < prime256 /\
   LowStar.Monotonic.Buffer.all_disjoint [loc p; loc tempBuffer;loc result]
  )
  (ensures fun h0 _ h1 -> modifies (loc p |+| loc result |+| loc tempBuffer) h0 h1 /\
    (
      let xN, yN, zN = scalar_multiplication prime_p256_order_seq (point_prime_to_coordinates (as_seq h0 p)) in 
      let x3, y3, z3 = point_x_as_nat h1 result, point_y_as_nat h1 result, point_z_as_nat h1 result in 
      x3 == xN /\ y3 == yN /\ z3 == zN 
) 
)


let multByOrder p result tempBuffer =
  push_frame();
    let h0 = ST.get() in 
    recall_contents order_buffer prime_p256_order_seq;
  scalarMultiplication #IMMUT p result order_buffer tempBuffer;
    let h2 = ST.get() in 
    assert(
    let xN, yN, zN = scalar_multiplication  prime_p256_order_seq (point_prime_to_coordinates (as_seq h0 p)) in 
    let x3, y3, z3 = point_x_as_nat h2 result, point_y_as_nat h2 result, point_z_as_nat h2 result in 
    x3 == xN /\ y3 == yN /\ z3 == zN);
  pop_frame()


inline_for_extraction noextract
val multByOrder2: p: point -> result: point -> tempBuffer: lbuffer uint64 (size 100) -> Stack unit 
  (requires fun h -> 
    live h p /\ live h result /\ live h tempBuffer /\
    as_nat h (gsub p (size 0) (size 4)) < prime256 /\ 
    as_nat h (gsub p (size 4) (size 4)) < prime256 /\
    as_nat h (gsub p (size 8) (size 4)) < prime256 /\
   LowStar.Monotonic.Buffer.all_disjoint [loc p; loc tempBuffer;loc result]
  )
  (ensures fun h0 _ h1  -> modifies (loc result |+| loc tempBuffer) h0 h1 /\
    (
      let xN, yN, zN = scalar_multiplication prime_p256_order_seq (point_prime_to_coordinates (as_seq h0 p)) in 
      let x3, y3, z3 = point_x_as_nat h1 result, point_y_as_nat h1 result, point_z_as_nat h1 result in 
      x3 == xN /\ y3 == yN /\ z3 == zN 
))

let multByOrder2 p result tempBuffer = 
  push_frame();
    let pBuffer = create (size 12) (u64 0) in 
    copy pBuffer p;
    multByOrder pBuffer result tempBuffer;
  pop_frame()  
    

#reset-options "--z3refresh --z3rlimit 100"
(*checks whether the base point * order is point at infinity *)
val isOrderCorrect: p: point -> tempBuffer: lbuffer uint64 (size 100) ->  Stack bool
  (requires fun h -> live h p /\ live h tempBuffer /\ 
    as_nat h (gsub p (size 0) (size 4)) < prime256 /\ 
    as_nat h (gsub p (size 4) (size 4)) < prime256 /\
    as_nat h (gsub p (size 8) (size 4)) < prime256 /\
    disjoint p tempBuffer)
  (ensures fun h0 r h1 -> modifies(loc tempBuffer) h0 h1 /\ (
      let (xN, yN, zN) = scalar_multiplication prime_p256_order_seq (point_prime_to_coordinates (as_seq h0 p)) in 
      if Hacl.Spec.P256.isPointAtInfinity (xN, yN, zN) then 
	r == true else r == false
  )
)

let isOrderCorrect p tempBuffer = 
  push_frame(); 
    let multResult = create (size 12) (u64 0) in 
    multByOrder2 p multResult tempBuffer;
    let result = Hacl.Impl.P256.isPointAtInfinity multResult in  
   pop_frame();
   result


open Lib.ByteBuffer 


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

val toUint64: i: lbuffer uint8 (32ul) -> o: felem ->  Stack unit
  (requires fun h -> live h i /\ live h o /\ disjoint i o)
  (ensures fun h0 _ h1 -> modifies (loc o) h0 h1 
    /\ as_seq h1 o == Hacl.Spec.ECDSA.changeEndian(Lib.ByteSequence.uints_from_bytes_be #_ #_ #4 (as_seq h0 i))
   )

let toUint64 i o = 
  uints_from_bytes_be o i;
  changeEndian o


val toUint8: i: felem ->  o: lbuffer uint8 (32ul) -> Stack unit
  (requires fun h -> live h i /\ live h o /\ disjoint i o)
  (ensures fun h0 _ h1 -> modifies (loc o) h0 h1 /\ 
    as_seq h1 o == Lib.ByteSequence.uints_to_bytes_le #_ #_ #4 (as_seq h0 i))

let toUint8 i o = 
  uints_to_bytes_le (size 4) o i


(*
For Bob to authenticate Alice's signature, he must have a copy of her public-key curve point {\displaystyle Q_{A}} Q_{A}. Bob can verify {\displaystyle Q_{A}} Q_{A} is a valid curve point as follows:

Check that {\displaystyle Q_{A}} Q_{A} is not equal to the identity element {\displaystyle O} O, and its coordinates are otherwise valid
Check that {\displaystyle Q_{A}} Q_{A} lies on the curve
Check that {\displaystyle n\times Q_{A}=O} n\times Q_{A}=O
 *)
val verifyQValidCurvePoint: pubKey: lbuffer uint64 (size 8) -> pubKeyAsPoint: point -> tempBuffer: lbuffer uint64 (size 100) ->  Stack bool
  (requires fun h -> live h pubKey /\ live h tempBuffer /\ live h pubKeyAsPoint /\
    LowStar.Monotonic.Buffer.all_disjoint [loc pubKey; loc tempBuffer; loc pubKeyAsPoint]
  )
  (ensures fun h0 r h1 -> modifies (loc pubKeyAsPoint |+| loc tempBuffer) h0 h1 /\ 
    ( 
      let xA = gsub pubKeyAsPoint (size 0) (size 4) in 
      let yA = gsub pubKeyAsPoint (size 4) (size 4) in 
      let zA = gsub pubKeyAsPoint (size 8) (size 4) in 

      let x = gsub pubKey (size 0) (size 4) in 
      let y = gsub pubKey (size 4) (size 4) in 
 
      as_seq h0 pubKey == as_seq h1 (gsub pubKeyAsPoint (size 0) (size 8)) /\
      as_nat h1 zA == 1 /\ 
(
      if (as_nat h1 xA < prime256 && as_nat h1 yA < prime256 &&  as_nat h1 zA < prime256 &&
	  Hacl.Spec.P256.isPointOnCurve (as_nat h1 xA, as_nat h1 yA, as_nat h1 zA) &&
	  Hacl.Spec.P256.isPointOnCurve (as_nat h0 x, as_nat h0 y, 1) &&
	  Hacl.Spec.P256.isPointAtInfinity (scalar_multiplication prime_p256_order_seq (point_prime_to_coordinates (as_seq h1 pubKeyAsPoint))))
	  then r == true else r == false)
     /\ 
	r == verifyQValidCurvePointSpec (as_nat h1 xA, as_nat h1 yA, as_nat h1 zA) /\
	(
	  let xJ, yJ, zJ = toJacobianCoordinates (as_nat h0 x, as_nat h0 y) in 
	  as_nat h1 xA == xJ /\ as_nat h1 yA == yJ /\ as_nat h1 zA == zJ
	)
     )
) 

let verifyQValidCurvePoint pubKey pubKeyAsPoint tempBuffer = 
    bufferToJac pubKey pubKeyAsPoint;
    let coordinatesValid = isCoordinateValid pubKeyAsPoint in 
      if not coordinatesValid then false else
    let belongsToCurve =  Hacl.Impl.P256.isPointOnCurve pubKeyAsPoint in 
    let orderCorrect = isOrderCorrect pubKeyAsPoint tempBuffer in 
    if coordinatesValid && belongsToCurve && orderCorrect 
      then true 
    else false  


#reset-options "--z3refresh --z3rlimit 100"
(* Verify that {\displaystyle r} r and {\displaystyle s} s are integers in {\displaystyle [1,n-1]} [1,n-1]. If not, the signature is invalid. *)
inline_for_extraction noextract
val ecdsa_verification_step1: r: lbuffer uint64 (size 4) -> s: lbuffer uint64 (size 4) -> Stack bool
  (requires fun h -> live h r /\ live h s /\ disjoint r s )
  (ensures fun h0 result h1 -> modifies0 h0 h1 
   /\ 
     (
       if  as_nat h0 r > 0 && as_nat h0 r < prime_p256_order && as_nat h0 s > 0 && as_nat h0 s < prime_p256_order 
	 then result == true else result == false /\
	 result == checkCoordinates (as_nat h0 r) (as_nat h0 s)
      
     )
  )

let ecdsa_verification_step1 r s = 
  let isRCorrect = isMoreThanZeroLessThanOrderMinusOne r in 
  let isSCorrect = isMoreThanZeroLessThanOrderMinusOne s in 
  isRCorrect && isSCorrect


inline_for_extraction noextract
val ecdsa_verification_step23: mLen: size_t -> m: lbuffer uint8 mLen{uint_v mLen < pow2 61} -> hashAsFelem : felem ->  Stack unit
  (requires fun h -> live h m /\ live h hashAsFelem)
  (ensures fun h0 _ h1 -> modifies (loc hashAsFelem) h0 h1 /\ as_nat h1 hashAsFelem < prime_p256_order /\
    (
      as_nat h1 hashAsFelem = (felem_seq_as_nat (Hacl.Spec.ECDSA.changeEndian(Lib.ByteSequence.uints_from_bytes_be (Spec.Hash.hash Spec.Hash.Definitions.SHA2_256 (as_seq h0 m))))) % prime_p256_order
 ) 
)

let ecdsa_verification_step23 mLen m hashAsFelem = 
  push_frame(); 
    let mHash = create (size 32) (u8 0) in  
      let h0 = ST.get() in 
    hash_256 m mLen mHash;
      let h1 = ST.get() in 
      assert(Seq.equal (as_seq h1 mHash) (Spec.Hash.hash Spec.Hash.Definitions.SHA2_256 (as_seq h0 m)));
    toUint64 mHash hashAsFelem;
    reduction_prime_2prime_order hashAsFelem hashAsFelem;
  pop_frame()


#reset-options "--z3refresh --z3rlimit 300"
inline_for_extraction noextract
val ecdsa_verification_step4: r: felem -> s: felem -> hash: felem -> bufferU1: lbuffer uint8 (size 32) -> 
  bufferU2: lbuffer uint8 (size 32) ->
  Stack unit 
  (requires fun h -> live h r /\ live h s /\ live h hash /\ live h bufferU1 /\ live h bufferU2 /\
    as_nat h s < prime_p256_order /\ as_nat h hash < prime_p256_order /\ as_nat h r < prime_p256_order /\
    LowStar.Monotonic.Buffer.all_disjoint [loc r; loc s; loc hash; loc bufferU1; loc bufferU2] 
  )
  (ensures fun h0 _ h1 -> modifies (loc bufferU1 |+| loc  bufferU2) h0 h1 /\
    as_seq h1 bufferU1 == Lib.ByteSequence.uints_to_bytes_le (nat_as_seq((Hacl.Spec.P256.Definitions.pow (as_nat h0 s) (prime_p256_order - 2)  * (as_nat h0 hash)) % prime_p256_order)) /\ 
    as_seq h1 bufferU2 == Lib.ByteSequence.uints_to_bytes_le (nat_as_seq((Hacl.Spec.P256.Definitions.pow (as_nat h0 s) (prime_p256_order - 2)  * (as_nat h0 r)) % prime_p256_order))  
  )

let ecdsa_verification_step4 r s hash bufferU1 bufferU2 = 
  push_frame();
    let tempBuffer = create (size 12) (u64 0) in 
      let inverseS = sub tempBuffer (size 0) (size 4) in 
      let u1 = sub tempBuffer (size 4) (size 4) in 
      let u2 = sub tempBuffer (size 8) (size 4) in 
    let h0 = ST.get() in 
  fromDomainImpl s inverseS;
  montgomery_ladder_exponent inverseS; 
    let h2 = ST.get() in 
    assert(
      let a_ = fromDomain_  (fromDomain_ (as_nat h0 s)) in 
      let r0D = exponent_spec a_ in 
      fromDomain_ (as_nat h2 inverseS) == r0D);

  multPowerPartial s inverseS hash u1; 
  multPowerPartial s inverseS r u2; 
    
    let h3 = ST.get() in 
    assert(as_nat h3 u1 = (Hacl.Spec.P256.Definitions.pow (as_nat h0 s) (prime_p256_order - 2)  * (as_nat h0 hash)) % prime_p256_order);
    lemmaSeq2Nat (as_seq h3 u1);
    lemmaSeq2Nat (as_seq h3 u2);

    assert(as_seq h3 u1 == nat_as_seq((Hacl.Spec.P256.Definitions.pow (as_nat h0 s) (prime_p256_order - 2)  * (as_nat h0 hash)) % prime_p256_order));
    assert(as_seq h3 u2 == nat_as_seq((Hacl.Spec.P256.Definitions.pow (as_nat h0 s) (prime_p256_order - 2)  * (as_nat h0 r)) % prime_p256_order));

  toUint8 u1 bufferU1;
  toUint8 u2 bufferU2;
    let h4 = ST.get() in 
    assert(as_seq h4 bufferU1 == Lib.ByteSequence.uints_to_bytes_le (nat_as_seq((Hacl.Spec.P256.Definitions.pow (as_nat h0 s) (prime_p256_order - 2)  * (as_nat h0 hash)) % prime_p256_order)));
    assert(as_seq h4 bufferU2 == Lib.ByteSequence.uints_to_bytes_le (nat_as_seq((Hacl.Spec.P256.Definitions.pow (as_nat h0 s) (prime_p256_order - 2)  * (as_nat h0 r)) % prime_p256_order)));
  pop_frame()


#reset-options "--z3refresh --z3rlimit 300" 

inline_for_extraction noextract
val ecdsa_verification_step5_0: pubKeyAsPoint: point -> u1: lbuffer uint8 (size 32) -> u2: lbuffer uint8 (size 32) -> 
  tempBuffer: lbuffer uint64 (size 100) -> points: lbuffer uint64 (size 24) ->
    Stack unit 
      (requires fun h -> live h pubKeyAsPoint /\ live h u1 /\ live h u2 /\ live h tempBuffer /\ live h points /\
	LowStar.Monotonic.Buffer.all_disjoint [loc pubKeyAsPoint; loc u1; loc u2; loc points; loc tempBuffer] /\
	as_nat h (gsub pubKeyAsPoint (size 0) (size 4)) < prime256 /\
	as_nat h (gsub pubKeyAsPoint (size 4) (size 4)) < prime256 /\
	as_nat h (gsub pubKeyAsPoint (size 8) (size 4)) < prime256 
)
  (ensures fun h0 _ h1 -> modifies (loc pubKeyAsPoint |+| loc  tempBuffer |+| loc points) h0 h1 /\ 
  
    	as_nat h1 (gsub points (size 0) (size 4)) < prime256 /\
	as_nat h1 (gsub points (size 4) (size 4)) < prime256 /\
	as_nat h1 (gsub points (size 8) (size 4)) < prime256 /\
	as_nat h1 (gsub points (size 12) (size 4)) < prime256 /\
	as_nat h1 (gsub points (size 16) (size 4)) < prime256 /\
	as_nat h1 (gsub points (size 20) (size 4)) < prime256 /\ 
  (
    let pointU1 = gsub points (size 0) (size 12) in 
    let pointU2 = gsub points (size 12) (size 12) in  
  
    let fromDomainPointU1 = fromDomainPoint (point_prime_to_coordinates (as_seq h1 pointU1)) in 
    let fromDomainPointU2 = fromDomainPoint (point_prime_to_coordinates (as_seq h1 pointU2)) in 
    
    let basePoint = (0x6B17D1F2E12C4247F8BCE6E563A440F277037D812DEB33A0F4A13945D898C296, 0x4FE342E2FE1A7F9B8EE7EB4A7C0F9E162BCE33576B315ECECBB6406837BF51F5, 1) in 
    let pointAtInfinity = (0, 0, 0) in 
    let u1D, _ = montgomery_ladder_spec (as_seq h0 u1) (pointAtInfinity, basePoint) in 
    let u2D, _ = montgomery_ladder_spec (as_seq h0 u2) (pointAtInfinity, point_prime_to_coordinates (as_seq h0 pubKeyAsPoint)) in 
    fromDomainPointU1 == u1D /\ fromDomainPointU2 == u2D
  )
)


let ecdsa_verification_step5_0 pubKeyAsPoint u1 u2 tempBuffer points  = 
    let pointU1G = sub points (size 0) (size 12) in  
    let pointU2Q = sub points (size 12) (size 12) in
    secretToPublicWithoutNorm pointU1G u1 tempBuffer; 
    scalarMultiplicationWithoutNorm pubKeyAsPoint pointU2Q u2 tempBuffer



inline_for_extraction noextract
val ecdsa_verification_step5_1: pubKeyAsPoint: point ->  
  u1: lbuffer uint8 (size 32) ->  
  u2: lbuffer uint8 (size 32) -> 
  pointSum: point -> 
  tempBuffer: lbuffer uint64 (size 100) ->
  Stack unit
    (requires fun h -> live h pubKeyAsPoint /\ live h u1 /\ live h u2 /\ live h pointSum /\ live h tempBuffer /\
    LowStar.Monotonic.Buffer.all_disjoint [loc pubKeyAsPoint; loc u1; loc u2; loc pointSum; loc tempBuffer] /\
    as_nat h (gsub pubKeyAsPoint (size 0) (size 4)) < prime256 /\
    as_nat h (gsub pubKeyAsPoint (size 4) (size 4)) < prime256 /\
    as_nat h (gsub pubKeyAsPoint (size 8) (size 4)) < prime256 )
    (ensures fun h0 _ h1 -> modifies (loc pointSum |+| loc tempBuffer |+| loc pubKeyAsPoint) h0 h1 /\ 
      as_nat h1 (gsub pointSum (size 0) (size 4)) < prime256 /\
      	(
	  let basePoint = (0x6B17D1F2E12C4247F8BCE6E563A440F277037D812DEB33A0F4A13945D898C296, 0x4FE342E2FE1A7F9B8EE7EB4A7C0F9E162BCE33576B315ECECBB6406837BF51F5, 1) in 
	  let pointAtInfinity = (0, 0, 0) in 
	
	  let u1D, _ = montgomery_ladder_spec (as_seq h0 u1) (pointAtInfinity, basePoint) in 
	  let u2D, _ = montgomery_ladder_spec (as_seq h0 u2) (pointAtInfinity, point_prime_to_coordinates (as_seq h0 pubKeyAsPoint)) in 

	  let sumD = _point_add u1D u2D in 
	
	  let pointNorm = _norm sumD in 
	  let resultPoint =  point_prime_to_coordinates (as_seq h1 pointSum) in 
	  pointNorm == resultPoint    
      )
   )   


let ecdsa_verification_step5_1 pubKeyAsPoint u1 u2 pointSum tempBuffer = 
  push_frame();
    let points = create (size 24) (u64 0) in
    let buff = sub tempBuffer (size 12) (size 88) in 
	let h0 = ST.get() in 
    ecdsa_verification_step5_0 pubKeyAsPoint u1 u2 tempBuffer points; 
      let h1 = ST.get() in 
      assert(modifies3 pubKeyAsPoint tempBuffer points h0 h1);
      modifies3_is_modifies4 pointSum pubKeyAsPoint tempBuffer points h0 h1;
      assert(modifies4 pointSum pubKeyAsPoint tempBuffer points h0 h1); 
  
    let pointU1G = sub points (size 0) (size 12) in 
    let pointU2Q = sub points (size 12) (size 12) in 
    point_add pointU1G pointU2Q pointSum buff; 
    norm pointSum pointSum buff;
      let h2 = ST.get() in 
      assert(      
	let basePoint = (0x6B17D1F2E12C4247F8BCE6E563A440F277037D812DEB33A0F4A13945D898C296, 0x4FE342E2FE1A7F9B8EE7EB4A7C0F9E162BCE33576B315ECECBB6406837BF51F5, 1) in 
	let pointAtInfinity = (0, 0, 0) in 
	
	let u1D, _ = montgomery_ladder_spec (as_seq h0 u1) (pointAtInfinity, basePoint) in 
	let u2D, _ = montgomery_ladder_spec (as_seq h0 u2) (pointAtInfinity, point_prime_to_coordinates (as_seq h0 pubKeyAsPoint)) in 

	let sumD = _point_add u1D u2D in 
	
	let pointNorm = _norm sumD in 
	let resultPoint =  point_prime_to_coordinates (as_seq h2 pointSum) in 
	pointNorm == resultPoint);

      assert(modifies2 pointSum tempBuffer h1 h2);
      modifies2_is_modifies4 pubKeyAsPoint points pointSum tempBuffer h1 h2;
      assert(modifies4 pubKeyAsPoint points pointSum tempBuffer h1 h2);
      assert(modifies4 pubKeyAsPoint points pointSum tempBuffer h0 h2); 
  pop_frame()



inline_for_extraction noextract
val ecdsa_verification_step5: pubKeyAsPoint: point -> 
  u1: lbuffer uint8 (size 32) ->  
  u2: lbuffer uint8 (size 32) -> 
  tempBuffer: lbuffer uint64 (size 100) -> 
  x: felem ->  Stack bool
  (requires fun h -> live h pubKeyAsPoint /\ live h u1 /\ live h u2 /\ live h tempBuffer /\ live h x
    /\ LowStar.Monotonic.Buffer.all_disjoint [loc pubKeyAsPoint; loc u1; loc u2; loc tempBuffer; loc x] /\
    as_nat h (gsub pubKeyAsPoint (size 0) (size 4)) < prime256 /\
    as_nat h (gsub pubKeyAsPoint (size 4) (size 4)) < prime256 /\
    as_nat h (gsub pubKeyAsPoint (size 8) (size 4)) < prime256 
  )
  (ensures fun h0 result h1 -> modifies (loc x |+| loc pubKeyAsPoint |+| loc tempBuffer) h0 h1 /\ as_nat h1 x < prime256 /\
    (
      let basePoint = (0x6B17D1F2E12C4247F8BCE6E563A440F277037D812DEB33A0F4A13945D898C296, 0x4FE342E2FE1A7F9B8EE7EB4A7C0F9E162BCE33576B315ECECBB6406837BF51F5, 1) in 
      let pointAtInfinity = (0, 0, 0) in 
	
      let u1D, _ = montgomery_ladder_spec (as_seq h0 u1) (pointAtInfinity, basePoint) in 
      let u2D, _ = montgomery_ladder_spec (as_seq h0 u2) (pointAtInfinity, point_prime_to_coordinates (as_seq h0 pubKeyAsPoint)) in 
      let sumD = _point_add u1D u2D in 
      let pointNorm = _norm sumD in 
      let (xResult, yResult, zResult) = pointNorm in 
      if Hacl.Spec.P256.isPointAtInfinity pointNorm then result = false else result = true  /\
      as_nat h1 x == xResult
  )
)

let ecdsa_verification_step5 pubKeyAsPoint u1 u2 tempBuffer x = 
  push_frame();
    let pointSum = create (size 12) (u64 0) in
      let h0 = ST.get() in 
    ecdsa_verification_step5_1 pubKeyAsPoint u1 u2 pointSum tempBuffer;
    let resultIsPAI = Hacl.Impl.P256.isPointAtInfinity pointSum in 
    let xCoordinateSum = sub pointSum (size 0) (size 4) in 
    copy x xCoordinateSum;
    pop_frame(); 
    not resultIsPAI



val ecdsa_verification: 
  pubKey: lbuffer uint64 (size 8)-> 
  r: lbuffer uint64 (size 4) ->
  s: lbuffer uint64 (size 4) ->
  mLen: size_t{uint_v mLen < pow2 61} ->
  m: lbuffer uint8 mLen -> 
  Stack bool
    (requires fun h -> live h pubKey /\ live h r /\ live h s /\ live h m /\
      LowStar.Monotonic.Buffer.all_disjoint [loc pubKey; loc r; loc s; loc m] )  
    (ensures fun h0 result h1 -> modifies0 h0 h1 /\
	(
	  let pubKeyX = as_nat h0 (gsub pubKey (size 0) (size 4)) in 
	  let pubKeyY = as_nat h0 (gsub pubKey (size 4) (size 4)) in 
	  result == ecdsa_verification (pubKeyX, pubKeyY) (as_nat h0 r) (as_nat h0 s) (v mLen) (as_seq h0 m)
    )
)


let ecdsa_verification pubKey r s mLen m = 
  push_frame();
    let tempBufferU64 = create (size 120) (u64 0) in 
    let tempBufferU8 = create (size 64) (u8 0) in 

    let publicKeyBuffer = sub tempBufferU64 (size 0) (size 12) in 
    let hashAsFelem = sub tempBufferU64 (size 12) (size 4) in 
    let tempBuffer = sub tempBufferU64 (size 16) (size 100) in 

    let bufferU1 =  sub tempBufferU8 (size 0) (size 32) in 
    let bufferU2 = sub tempBufferU8 (size 32) (size 32) in 
    let xBuffer =  sub tempBufferU64 (size 116) (size 4) in 

    let publicKeyCorrect = verifyQValidCurvePoint pubKey publicKeyBuffer tempBuffer in 
      let h1 = ST.get() in 
    (*assert(as_seq h1 publicKeyBuffer == *)


    if publicKeyCorrect = false then  
      begin pop_frame(); false end
    else 

    let step1 = ecdsa_verification_step1 r s in 
    if step1 = false then 
      begin
	pop_frame(); false 
      end 
      else 
	begin 
	  ecdsa_verification_step23 mLen m hashAsFelem;
	  ecdsa_verification_step4 r s hashAsFelem bufferU1 bufferU2;
	  let state = ecdsa_verification_step5 publicKeyBuffer bufferU1 bufferU2 tempBuffer xBuffer in 
	    if state = false then begin pop_frame(); false end else begin
	  let r = compare_felem xBuffer r in 
	  pop_frame();
	  r
	  end
	end   
   
   
