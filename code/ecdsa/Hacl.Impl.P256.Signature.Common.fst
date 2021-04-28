module Hacl.Impl.P256.Signature.Common

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.ByteBuffer 
open Lib.Buffer 

open Spec.ECC 
open Hacl.Spec.EC.Definition
open Spec.ECDSA

open Hacl.Impl.EC.LowLevel
open Hacl.Impl.EC.MontgomeryMultiplication

open Hacl.Impl.EC.Setup
open Hacl.Impl.EC.Math 
open FStar.Math.Lemmas
open FStar.Mul

open Hacl.Impl.EC.Arithmetics
open Hacl.Impl.P256.LowLevel .RawCmp
open Hacl.Spec.MontgomeryMultiplication
friend Hacl.Spec.MontgomeryMultiplication

open Hacl.Impl.EC.Core
open Hacl.Impl.EC.Masking


#set-options "--fuel 0 --ifuel 0 --z3rlimit 100"

let bufferToJac #c p result = 
    let h0 = ST.get() in 
  let len = getCoordinateLenU64 c in 
  let lengthXY = len *. 2ul in 
  let partPoint = sub result (size 0) lengthXY in 
  let zCoordinate = sub result lengthXY len in 
  copy partPoint p;
  uploadOneImpl #c zCoordinate;
    let h1 = ST.get() in 
    assert(felem_eval c h1 (gsub result (2ul *! getCoordinateLenU64 c) (getCoordinateLenU64 c)))


inline_for_extraction noextract
val y_2: #c: curve -> y: felem c -> r: felem c -> Stack unit
  (requires fun h -> as_nat c h y < getPrime c /\ live h y /\ live h r /\ eq_or_disjoint y r)
  (ensures fun h0 _ h1 -> modifies (loc r) h0 h1 /\ 
    as_nat c h1 r == toDomain_ #c #DH ((as_nat c h0 y) * (as_nat c h0 y) % getPrime c))

let y_2 #c y r = 
  toDomain #c y r;
  montgomery_square_buffer_dh #c r r


val lemma_xcube: #c: curve -> x_: nat {x_ < getPrime c} -> Lemma (
  let prime = getPrime c in 
  ((x_ * x_ * x_ % prime) - (3 * x_ % prime)) % prime == (x_ * x_ * x_ - 3 * x_) % prime)

let lemma_xcube #c x_ = 
  let prime = getPrime c in 
  lemma_mod_add_distr (- (3 * x_ % prime)) (x_ * x_ * x_) prime;
  lemma_mod_sub_distr (x_ * x_ * x_ ) (3 * x_) prime


val lemma_xcube2: #c: curve -> x_ : nat {x_ < getPrime c} -> Lemma (
  let prime = getPrime c in 
  toDomain_ #c #DH (((((x_ * x_ * x_) - (3 * x_)) % prime) + bCoordinate #P256) % prime) == 
  toDomain_ #c #DH ((x_ * x_ * x_  + aCoordinate #P256 * x_ + bCoordinate #P256) % prime))

let lemma_xcube2 #c x_ = 
  let prime = getPrime c in 
  lemma_mod_add_distr (bCoordinate #P256) ((x_ * x_ * x_) - (3 * x_)) prime


inline_for_extraction noextract
val xcube_minus_x: #c: curve -> x: felem c -> r: felem c -> Stack unit 
  (requires fun h -> as_nat c h x < getPrime c /\ live h x  /\ live h r /\ eq_or_disjoint x r)
  (ensures fun h0 _ h1 -> modifies (loc r) h0 h1 /\ (
    let x_ = as_nat c h0 x in 
    as_nat c h1 r = toDomain_ #c #DH ((x_ * x_ * x_ - 3 * x_ + bCoordinate #c) % getPrime c)))

let xcube_minus_x #c x r = 
  push_frame();
  let h0 = ST.get() in 
  let sz: FStar.UInt32.t = getCoordinateLenU64 c in 
  let xToDomainBuffer = create sz (u64 0) in 
  let minusThreeXBuffer = create sz (u64 0) in 
  let b_constant = create sz (u64 0) in 

  toDomain #c x xToDomainBuffer; 
  montgomery_square_buffer_dh #c xToDomainBuffer r;
  montgomery_multiplication_buffer_dh #c r xToDomainBuffer r;
    lemma_mod_mul_distr_l ((as_nat c h0 x) * (as_nat c h0 x)) (as_nat c h0 x) (getPrime c);
  multByThree #c xToDomainBuffer minusThreeXBuffer;
  felem_sub #c r minusThreeXBuffer r;
  upload_b_constant #c b_constant;
  Hacl.Impl.EC.LowLevel.felem_add #c r b_constant r;
  pop_frame(); 

    let x_ = as_nat c h0 x in 
    lemma_xcube #c x_;
    lemma_mod_add_distr (bCoordinate #c) (x_ * x_ * x_ - 3 * x_) (getPrime c);
    lemma_xcube2 #c x_


let isPointAtInfinityPublic #c p =  
  let len = getCoordinateLenU64 c in 
  let zCoordinate = sub p (size 2 *! len) len in 
  isZero_uint64_nCT #c zCoordinate 
    

assume val lemma_modular_multiplication_2_d: #c: curve -> 
  a:nat {a < getPrime c} -> b:nat {b < getPrime c } -> 
  Lemma (toDomain_ #c #DH a = toDomain_ #c #DH b <==> a == b)


let isPointOnCurvePublic #c p = 
  push_frame(); 
  let sz: FStar.UInt32.t = getCoordinateLenU64 c in 
  let y2Buffer = create sz (u64 0) in 
  let xBuffer = create sz (u64 0) in 
  let h0 = ST.get() in 
  let x = sub p (size 0) sz in 
  let y = sub p sz sz in
  
  y_2 #c y y2Buffer;
  xcube_minus_x #c x xBuffer;

  lemma_modular_multiplication_2_d #c ((as_nat c h0 y) * (as_nat c h0 y) % (getPrime c)) 
    (let x_ = as_nat c h0 x in (x_ * x_ * x_ - 3 * x_ + bCoordinate #c) % (getPrime c));
    
  let r = compare_felem #c y2Buffer xBuffer in 
  let z = not (eq_0_u64 r) in 
  
  pop_frame();
  z


val isCoordinateValid: #c: curve -> p: point c -> Stack bool 
  (requires fun h -> live h p /\ point_z_as_nat c h p == 1)
  (ensures fun h0 r h1 -> 
    let prime = getPrime c in 
    modifies0 h0 h1 /\ 
    r == (point_x_as_nat c h0 p < prime && point_y_as_nat c h0 p < prime && point_z_as_nat c h0 p < prime)
  )


let isCoordinateValid #c p = 
  push_frame();

  let len = getCoordinateLenU64 c in 
  let tempBuffer = create len (u64 0) in 
  recall_contents #_ #(getCoordinateLenU64 c) (prime_buffer #c) (Lib.Sequence.of_list (prime_list c));
  
  let x = sub p (size 0) len in 
  let y = sub p len len in 
  
  let carryX = sub_bn_prime #c x tempBuffer in
  let carryY = sub_bn_prime #c y tempBuffer in 
  
  let lessX = eq_u64_nCT carryX (u64 1) in   
  let lessY = eq_u64_nCT carryY (u64 1) in 

  let r = lessX && lessY in admit();
  pop_frame();
  r  


val multByOrder: #c: curve -> result: point c ->  p: point c -> 
  tempBuffer: lbuffer uint64 (size 25 *! getCoordinateLenU64 c) -> Stack unit 
  (requires fun h -> 
    let prime = getPrime c in 
    
    live h result /\ live h p /\ live h tempBuffer /\
    LowStar.Monotonic.Buffer.all_disjoint [loc result; loc p; loc tempBuffer] /\
    point_x_as_nat c h p < prime /\ 
    point_y_as_nat c h p < prime /\
    point_z_as_nat c h p < prime
  )
  (ensures fun h0 _ h1 ->
    let prime = getPrime c in 
    modifies (loc result |+| loc p |+| loc tempBuffer) h0 h1 /\
    (
      let xN, yN, zN = scalar_multiplication #c (prime_order_seq #c) (point_prime_to_coordinates c (as_seq h0 p)) in 
      let x3, y3, z3 = point_x_as_nat c h1 result, point_y_as_nat c h1 result, point_z_as_nat c h1 result in 
      x3 == xN /\ y3 == yN /\ z3 == zN 
    ) 
  ) 


#push-options "--z3rlimit 100"

let multByOrder #c result p tempBuffer =
  admit() (*);
  recall_contents order_buffer (prime_order_seq #c)
  assert (disjoint p order_buffer);
  assert (disjoint result order_buffer);
  assert (disjoint tempBuffer order_buffer)
  scalarMultiplication #c p result (order_buffer #c) tempBuffer *)

#pop-options


val multByOrder2: #c: curve -> result: point c ->  p: point c -> tempBuffer: lbuffer uint64 (size 100) -> Stack unit 
  (requires fun h -> 
    live h result /\ live h p /\ live h tempBuffer /\
    LowStar.Monotonic.Buffer.all_disjoint [loc result; loc p; loc tempBuffer] /\
    point_x_as_nat c h p < prime256 /\ 
    point_y_as_nat c h p < prime256 /\
    point_z_as_nat c h p < prime256
  )
  (ensures fun h0 _ h1  -> modifies (loc result |+| loc tempBuffer) h0 h1 /\
    (
      let xN, yN, zN = scalar_multiplication #c (prime_order_seq #P256) (point_prime_to_coordinates c (as_seq h0 p)) in 
      let x3, y3, z3 = point_x_as_nat c h1 result, point_y_as_nat c h1 result, point_z_as_nat c h1 result in 
      x3 == xN /\ y3 == yN /\ z3 == zN 
    )
  )

let multByOrder2 #c result p tempBuffer = 
  push_frame();
    let len = getCoordinateLenU64 c in 
  let pBuffer = create (size 3 *! len) (u64 0) in 
  copy pBuffer p;
  multByOrder result pBuffer tempBuffer;
  pop_frame()  
    
(*
[@ (Comment "  This code is not side channel resistant")]
 *)


val isOrderCorrect: #c: curve -> p: point c -> tempBuffer: lbuffer uint64 (size 100) -> Stack bool
  (requires fun h -> 
    live h p /\ live h tempBuffer /\ 
    disjoint p tempBuffer /\
    point_x_as_nat c h p < prime256 /\ 
    point_y_as_nat c h p < prime256 /\
    point_z_as_nat c h p < prime256
  )
  (ensures fun h0 r h1 -> 
    modifies(loc tempBuffer) h0 h1 /\ 
    (let (xN, yN, zN) = scalar_multiplication #c (prime_order_seq #P256) (point_prime_to_coordinates c (as_seq h0 p)) in 
     r == Spec.ECC.isPointAtInfinity (xN, yN, zN))
  )

let isOrderCorrect #c p tempBuffer = 
  push_frame(); 
    let len = getCoordinateLenU64 c in 
    let multResult = create (size 3 *! len) (u64 0) in 
    multByOrder2 multResult p tempBuffer;
    let result = isPointAtInfinityPublic #c multResult in  
  pop_frame();
    result


let verifyQValidCurvePoint pubKeyAsPoint tempBuffer = 
  let coordinatesValid = isCoordinateValid pubKeyAsPoint in 
  if not coordinatesValid then false else 
    let belongsToCurve = isPointOnCurvePublic pubKeyAsPoint in 
    (* let orderCorrect = isOrderCorrect pubKeyAsPoint tempBuffer in  *)
    coordinatesValid && belongsToCurve (* && orderCorrect *)


let verifyQ #c pubKey = 
  push_frame();
    let h0 = ST.get() in
    let len = getCoordinateLenU64 c in 
    let lenScalar = getScalarLen c in 
    
    let pubKeyX = sub pubKey (size 0) lenScalar in 
    let pubKeyY = sub pubKey lenScalar lenScalar in 
    
    let tempBuffer = create (size 30 *! len) (u64 0) in 
      let tempBufferV = sub tempBuffer (size 0) (size 25 *! len) in 
      let publicKeyJ = sub tempBuffer (size 25 *! len) (size 3 *! len) in 
      let publicKeyB = sub tempBuffer (size 28 *! len) (size 2 *! len) in  
	let publicKeyX = sub publicKeyB (size 0) len in 
	let publicKeyY = sub publicKeyB len len in 
    
(*     toUint64ChangeEndian #c pubKeyX publicKeyX;
    toUint64ChangeEndian #c pubKeyY publicKeyY; *)
  let h1 = ST.get() in 
    (*   lemma_core_0 c publicKeyX h1;
      uints_from_bytes_le_nat_lemma #U64 #SEC #4 (as_seq h1 pubKeyX);  
      lemma_core_0 c publicKeyY h1;
      uints_from_bytes_le_nat_lemma #U64 #SEC #4 (as_seq h1 pubKeyY); 

      changeEndianLemma #c (uints_from_bytes_be (as_seq h1 (gsub pubKey (size 0) (size 32))));
      uints_from_bytes_be_nat_lemma #U64 #_ #4 (as_seq h1 (gsub pubKey (size 0) (size 32)));
      
      changeEndianLemma #c (uints_from_bytes_be (as_seq h1 (gsub pubKey (size 32) (size 32))));
      uints_from_bytes_be_nat_lemma #U64 #_ #4 (as_seq h1 (gsub pubKey (size 32) (size 32)));
 *)
  bufferToJac #c publicKeyB publicKeyJ;
  let r = verifyQValidCurvePoint #c publicKeyJ tempBufferV in 
  pop_frame();
  r
