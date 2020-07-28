module Hacl.Impl.P256.Signature.Common

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.ByteBuffer 
open Lib.ByteSequence
open Lib.Buffer 

open Spec.P256 
open Hacl.Spec.P256.Definition
open Hacl.Lemmas.P256

open Spec.ECDSA
open Hacl.Spec.ECDSA.Definition

open Hacl.Impl.P256.LowLevel 
open Hacl.Impl.P256.MontgomeryMultiplication
open Hacl.Impl.ECDSA.MontgomeryMultiplication

open Hacl.Impl.P256.LowLevel.PrimeSpecific
open Hacl.Impl.P256.Core

open Hacl.Impl.P256.Math 
open FStar.Math.Lemmas
open FStar.Mul

open Hacl.Impl.P256.Arithmetics
open Hacl.Impl.P256.LowLevel .RawCmp
open Hacl.Spec.P256.MontgomeryMultiplication
friend Hacl.Spec.P256.MontgomeryMultiplication

#set-options "--fuel 0 --ifuel 0 --z3rlimit 100"

#push-options "--ifuel 1"

let bufferToJac p result = 
  let partPoint = sub result (size 0) (size 8) in 
  copy partPoint p;
  upd result (size 8) (u64 1);
  upd result (size 9) (u64 0);
  upd result (size 10) (u64 0);
  upd result (size 11) (u64 0)

#pop-options


inline_for_extraction noextract
val y_2: #c: curve -> y: felem c -> r: felem c -> Stack unit
  (requires fun h -> as_nat c h y < prime /\ live h y /\ live h r /\ eq_or_disjoint y r)
  (ensures fun h0 _ h1 -> modifies (loc r) h0 h1 /\ as_nat c h1 r == toDomain_ #c ((as_nat c h0 y) * (as_nat c h0 y) % prime))

let y_2 #c y r = 
  toDomain #c y r;
  montgomery_square_buffer #c r r


inline_for_extraction noextract
val upload_p256_point_on_curve_constant: #c: curve ->  x: felem c -> Stack unit
  (requires fun h -> live h x)
  (ensures fun h0 _ h1 -> modifies (loc x) h0 h1 /\ 
    as_nat c h1 x == toDomain_ #c (bCoordinate #P256) /\
    as_nat c h1 x < prime
 )

let upload_p256_point_on_curve_constant x = 
  upd x (size 0) (u64 15608596021259845087);
  upd x (size 1) (u64 12461466548982526096);
  upd x (size 2) (u64 16546823903870267094);
  upd x (size 3) (u64 15866188208926050356);
  assert_norm (
    15608596021259845087 + 12461466548982526096 * pow2 64 + 
    16546823903870267094 * pow2 64 * pow2 64 + 
    15866188208926050356 * pow2 64 * pow2 64 * pow2 64 == bCoordinate #P256 * pow2 256 % prime)


val lemma_xcube: x_: nat {x_ < prime} -> Lemma 
  (((x_ * x_ * x_ % prime) - (3 * x_ % prime)) % prime == (x_ * x_ * x_ - 3 * x_) % prime)

let lemma_xcube x_ = 
  lemma_mod_add_distr (- (3 * x_ % prime)) (x_ * x_ * x_) prime;
  lemma_mod_sub_distr (x_ * x_ * x_ ) (3 * x_) prime


val lemma_xcube2: #c: curve -> x_ : nat {x_ < prime} -> Lemma (toDomain_ #c (((((x_ * x_ * x_) - (3 * x_)) % prime) + bCoordinate #P256) % prime) == toDomain_ #c ((x_ * x_ * x_  + aCoordinate #P256 * x_ + bCoordinate #P256) % prime))

let lemma_xcube2 x_ = 
  lemma_mod_add_distr (bCoordinate #P256) ((x_ * x_ * x_) - (3 * x_)) prime


inline_for_extraction noextract
val xcube_minus_x: #c: curve -> x: felem c -> r: felem c -> Stack unit 
  (requires fun h -> as_nat c h x < prime /\ live h x  /\ live h r /\ eq_or_disjoint x r)
  (ensures fun h0 _ h1 -> 
    modifies (loc r) h0 h1 /\
    (
      let x_ = as_nat c h0 x in 
      as_nat c h1 r = toDomain_ #c ((x_ * x_ * x_ - 3 * x_ + bCoordinate #P256) % prime))
    )

let xcube_minus_x #c x r = 
  push_frame();
      let h0 = ST.get() in 
    let xToDomainBuffer = create (size 4) (u64 0) in 
    let minusThreeXBuffer = create (size 4) (u64 0) in 
    let p256_constant = create (size 4) (u64 0) in 
  toDomain #c x xToDomainBuffer;
  montgomery_square_buffer #c xToDomainBuffer r;
  montgomery_multiplication_buffer #c r xToDomainBuffer r;
    lemma_mod_mul_distr_l ((as_nat c h0 x) * (as_nat c h0 x)) (as_nat c h0 x) prime;
  multByThree #c xToDomainBuffer minusThreeXBuffer;
  p256_sub r minusThreeXBuffer r;
    upload_p256_point_on_curve_constant #c p256_constant;
  p256_add r p256_constant r;
  pop_frame(); 
  
  let x_ = as_nat c h0 x in 
  lemma_xcube x_;
  lemma_mod_add_distr (bCoordinate #P256) ((x_ * x_ * x_) - (3 * x_)) prime;
  lemma_xcube2 #c x_


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


val lemma_modular_multiplication_p256_2_d: #c: curve -> 
  a:nat {a < prime256} -> b:nat {b < prime256} -> 
  Lemma (toDomain_ #c a = toDomain_ #c b <==> a == b)

let lemma_modular_multiplication_p256_2_d #c a b = 
   lemmaToDomain #c a;
   lemmaToDomain #c b;
   lemma_modular_multiplication_p256_2 a b


let isPointOnCurvePublic #c p = 
  push_frame(); 
    let y2Buffer = create (size 4) (u64 0) in 
    let xBuffer = create (size 4) (u64 0) in 
  let h0 = ST.get() in 
    let x = sub p (size 0) (size 4) in 
    let y = sub p (size 4) (size 4) in 
    y_2 #c y y2Buffer;
    xcube_minus_x #c x xBuffer;
    
    lemma_modular_multiplication_p256_2_d #c ((as_nat c h0 y) * (as_nat c h0 y) % prime) (let x_ = as_nat c h0 x in (x_ * x_ * x_ - 3 * x_ + bCoordinate #P256) % prime);
    
    let r = compare_felem #c y2Buffer xBuffer in 
    let z = not (eq_0_u64 r) in 
  pop_frame();
     z


val isCoordinateValid: #c: curve -> p: point c -> Stack bool 
  (requires fun h -> live h p /\ point_z_as_nat c h p == 1)
  (ensures fun h0 r h1 -> 
    modifies0 h0 h1 /\ 
    r == (point_x_as_nat c h0 p < prime256 && point_y_as_nat c h0 p < prime256 && point_z_as_nat c h0 p < prime256)
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
val multByOrder: #c: curve -> result: point c ->  p: point c -> tempBuffer: lbuffer uint64 (size 100) -> Stack unit 
  (requires fun h -> 
    live h result /\ live h p /\ live h tempBuffer /\
    LowStar.Monotonic.Buffer.all_disjoint [loc result; loc p; loc tempBuffer] /\
    point_x_as_nat c h p < prime256 /\ 
    point_y_as_nat c h p < prime256 /\
    point_z_as_nat c h p < prime256
  )
  (ensures fun h0 _ h1 ->
    modifies (loc result |+| loc p |+| loc tempBuffer) h0 h1 /\
    (
      let xN, yN, zN = scalar_multiplication #P256 (prime_order_seq #P256) (point_prime_to_coordinates (as_seq h0 p)) in 
      let x3, y3, z3 = point_x_as_nat c h1 result, point_y_as_nat c h1 result, point_z_as_nat c h1 result in 
      x3 == xN /\ y3 == yN /\ z3 == zN 
    ) 
  ) 


#push-options "--z3rlimit 100"

let multByOrder result p tempBuffer =
  recall_contents order_buffer (prime_order_seq #P256);
  assert (disjoint p order_buffer);
  assert (disjoint result order_buffer);
  assert (disjoint tempBuffer order_buffer);
  scalarMultiplication p result order_buffer tempBuffer

#pop-options


inline_for_extraction noextract
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
      let xN, yN, zN = scalar_multiplication (prime_order_seq #P256) (point_prime_to_coordinates (as_seq h0 p)) in 
      let x3, y3, z3 = point_x_as_nat c h1 result, point_y_as_nat c h1 result, point_z_as_nat c h1 result in 
      x3 == xN /\ y3 == yN /\ z3 == zN 
    )
  )

let multByOrder2 result p tempBuffer = 
  push_frame();
  let pBuffer = create (size 12) (u64 0) in 
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
    (let (xN, yN, zN) = scalar_multiplication (prime_order_seq #P256) (point_prime_to_coordinates (as_seq h0 p)) in 
     r == Spec.P256.isPointAtInfinity (xN, yN, zN))
  )

let isOrderCorrect #c p tempBuffer = 
  push_frame(); 
    let multResult = create (size 12) (u64 0) in 
    multByOrder2 multResult p tempBuffer;
    let result = isPointAtInfinityPublic #c multResult in  
  pop_frame();
    result


let verifyQValidCurvePoint pubKeyAsPoint tempBuffer = 
  let coordinatesValid = isCoordinateValid pubKeyAsPoint in 
  if not coordinatesValid then false else 
    let belongsToCurve = isPointOnCurvePublic pubKeyAsPoint in 
    let orderCorrect = isOrderCorrect pubKeyAsPoint tempBuffer in 
    coordinatesValid && belongsToCurve && orderCorrect


let verifyQ #c pubKey = 
  push_frame();
    let h0 = ST.get() in
    let pubKeyX = sub pubKey (size 0) (size 32) in 
    let pubKeyY = sub pubKey (size 32) (size 32) in 
    let tempBuffer = create (size 120) (u64 0) in 
      let tempBufferV = sub tempBuffer (size 0) (size 100) in 
      let publicKeyJ = sub tempBuffer (size 100) (size 12) in 
      let publicKeyB = sub tempBuffer (size 112) (size 8) in  
	let publicKeyX = sub publicKeyB (size 0) (size 4) in 
	let publicKeyY = sub publicKeyB (size 4) (size 4) in 
    
    toUint64ChangeEndian #c pubKeyX publicKeyX;
    toUint64ChangeEndian #c pubKeyY publicKeyY;
  let h1 = ST.get() in 
      lemma_core_0 c publicKeyX h1;
      uints_from_bytes_le_nat_lemma #U64 #SEC #4 (as_seq h1 pubKeyX);  
      lemma_core_0 c publicKeyY h1;
      uints_from_bytes_le_nat_lemma #U64 #SEC #4 (as_seq h1 pubKeyY); 

      changeEndianLemma (uints_from_bytes_be (as_seq h1 (gsub pubKey (size 0) (size 32))));
      uints_from_bytes_be_nat_lemma #U64 #_ #4 (as_seq h1 (gsub pubKey (size 0) (size 32)));
      
      changeEndianLemma (uints_from_bytes_be (as_seq h1 (gsub pubKey (size 32) (size 32))));
      uints_from_bytes_be_nat_lemma #U64 #_ #4 (as_seq h1 (gsub pubKey (size 32) (size 32)));

  bufferToJac #c publicKeyB publicKeyJ;
  let r = verifyQValidCurvePoint #c publicKeyJ tempBufferV in 
  pop_frame();
  r
