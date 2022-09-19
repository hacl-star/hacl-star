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
open Hacl.Impl.EC.LowLevel.RawCmp
open Hacl.Spec.MontgomeryMultiplication

open Hacl.Impl.EC.Core
open Hacl.Impl.EC.Masking
open Hacl.Impl.EC.Intro


#set-options "--max_fuel 0 --max_ifuel 0 --z3rlimit 100"

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


let fromForm #c i o = 
  let h0 = ST.get() in
  changeEndian i;
    let h1 = ST.get() in 
  lemma_change_endian #c (as_seq h0 i) (as_seq h1 i);
  toUint8 i o;
  lemma_lseq_nat_from_bytes (as_seq h0 i);
  lemma_nat_from_to_intseq_be_preserves_value (v (getCoordinateLenU64 c)) (as_seq h1 i);
  uints_to_bytes_be_nat_lemma #U64 #SEC (v (getCoordinateLenU64 c)) (as_nat c h0 i)


inline_for_extraction noextract
val fromFormPoint_: #c: curve -> i: point c -> o: pointAffine8 c -> Stack unit 
  (requires fun h -> live h i /\ live h o /\ disjoint i o /\ point_eval c h i /\ (
    let xCoordinate, yCoordinate, _ = point_as_nat c h i in 
    xCoordinate < pow2 (getPower c) /\ yCoordinate < pow2 (getPower c)))
  (ensures fun h0 _ h1 -> modifies (loc i |+| loc o) h0 h1 /\ (
    let coordinateX_u64, coordinateY_u64, _ = point_as_nat c h0 i in 
    let coordinateX_u8, coordinateY_u8 = getXAff8 #c o, getYAff8 #c o in
    as_seq h1 coordinateX_u8 == nat_to_bytes_be (getCoordinateLen c) coordinateX_u64 /\
    as_seq h1 coordinateY_u8 == nat_to_bytes_be (getCoordinateLen c) coordinateY_u64 /\    
    nat_from_bytes_be (as_seq h1 coordinateX_u8) == coordinateX_u64 /\
    nat_from_bytes_be (as_seq h1 coordinateY_u8) == coordinateY_u64))

let fromFormPoint_ #c i o = 
  let len = getCoordinateLenU64 c in 
  let scalarLen = getCoordinateLenU c in 
  
  let resultBufferX = sub i (size 0) len in
  let resultBufferY = sub i len len in

  let resultX = sub o (size 0) scalarLen in
  let resultY = sub o scalarLen scalarLen in

  fromForm #c resultBufferX resultX;
  fromForm #c resultBufferY resultY


[@CInline]
let fromFormPoint_p256 = fromFormPoint_ #P256 
[@CInline]
let fromFormPoint_p384 = fromFormPoint_ #P384 

(* [@CInline]
let fromFormPoint_generic = fromFormPoint_ #Default  *)

let fromFormPoint #c i o = 
  match c with 
  |P256 -> fromFormPoint_p256 i o 
  |P384 -> fromFormPoint_p384 i o
  

let toForm #c i o = 
  let open Lib.ByteSequence in 
    let h0 = ST.get() in 
  toUint64ChangeEndian i o;
    let h1 = ST.get() in 
  lemma_change_endian #c (as_seq h1 o) (uints_from_bytes_be #_ #_ #(v (getCoordinateLenU64 c)) (as_seq h0 i));
  uints_from_bytes_be_nat_lemma #U64 #_ #(v (getCoordinateLenU64 c))  (as_seq h0 i);
  lemma_lseq_nat_from_bytes (as_seq h1 o)


inline_for_extraction noextract
val toFormPoint_: #c: curve -> i: pointAffine8 c -> o: point c -> Stack unit 
  (requires fun h -> live h i /\ live h o /\ disjoint i o /\ (
    let pointScalarXSeq = nat_from_bytes_be (as_seq h (getXAff8 i)) in
    let pointScalarYSeq = nat_from_bytes_be (as_seq h (getYAff8 i)) in 
      pointScalarXSeq <> 0 /\  pointScalarYSeq <> 0))
  (ensures fun h0 _ h1 -> modifies (loc o) h0 h1 /\ (
    let pointScalarXSeq = nat_from_bytes_be (as_seq h0 (getXAff8 i))  in 
    let pointScalarYSeq = nat_from_bytes_be (as_seq h0 (getYAff8 i)) in 
    let x, y, z = as_nat c h1 (getX o), as_nat c h1 (getY o), as_nat c h1 (getZ o) in  
    let pointJacX, pointJacY, pointJacZ = toJacobianCoordinates (pointScalarXSeq, pointScalarYSeq) in 
    x == pointScalarXSeq /\ y == pointScalarYSeq /\ z == 1 /\
    x == pointJacX /\ y == pointJacY /\ z == pointJacZ))
      
let toFormPoint_ #c i o = 
  let len = getCoordinateLenU64 c in 
  let coordLen = getCoordinateLenU c in 
  
  let pointScalarX = sub i (size 0) coordLen in 
  let pointScalarY = sub i coordLen coordLen in 

  let pointX = sub o (size 0) len in 
  let pointY = sub o len len in 
  let pointZ = sub o (size 2 *! len) len in 

    let h0 = ST.get() in 
  toForm #c pointScalarX pointX;
  toForm #c pointScalarY pointY;
  uploadOneImpl #c pointZ


[@CInline]
let toFormPoint_p256 = toFormPoint_ #P256
[@CInline]
let toFormPoint_p384 = toFormPoint_ #P384

let toFormPoint #c i o = 
  match c with 
  |P256 -> toFormPoint_p256 i o 
  |P384 -> toFormPoint_p384 i o 



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


let isPointAtInfinity_public #c p =  
  let len = getCoordinateLenU64 c in 
  let zCoordinate = sub p (size 2 *! len) len in 
  isZero_uint64_nCT #c zCoordinate 


inline_for_extraction noextract
val isPointOnCurve_: #c: curve -> p: point c -> Stack bool
  (requires fun h -> live h p /\ felem_eval c h (getX p) /\ felem_eval c h (getY p) /\ as_nat c h (getZ p) == 1)
  (ensures fun h0 r h1 -> modifies0 h0 h1 /\ r == isPointOnCurve #c (point_as_nat c h0 p))

let isPointOnCurve_ #c p = 
  let h0 = ST.get() in 
  push_frame(); 
    let sz: FStar.UInt32.t = getCoordinateLenU64 c in 
    let y2Buffer = create sz (u64 0) in 
    let xBuffer = create sz (u64 0) in 
    let x = sub p (size 0) sz in 
    let y = sub p sz sz in
    
    y_2 #c y y2Buffer;
    xcube_minus_x #c x xBuffer;

    lemma_modular_multiplication_2_d #c ((as_nat c h0 y) * (as_nat c h0 y) % (getPrime c)) 
      (let x_ = as_nat c h0 x in (x_ * x_ * x_ - 3 * x_ + bCoordinate #c) % (getPrime c));
      
    let r = cmp_felem_felem_u64 #c y2Buffer xBuffer in 
    let z = not (eq_0_u64 r) in 
  pop_frame(); 
  z



[@CInline]
let isPointOnCurve_p256 = isPointOnCurve_ #P256
[@CInline]
let isPointOnCurve_p384 = isPointOnCurve_ #P384
(* [@CInline]
let isPointOnCurvePublic_generic = isPointOnCurvePublic_ #Default
 *)

let isPointOnCurve #c p = 
  match c with 
  |P256 -> isPointOnCurve_p256 p
  |P384 -> isPointOnCurve_p384 p 
  (* |Default -> isPointOnCurvePublic_generic p  *)



inline_for_extraction noextract
val isCoordinateValid_public: #c: curve -> p: point c -> Stack bool 
  (requires fun h -> live h p /\ as_nat c h (getZ p) == 1)
  (ensures fun h0 r h1 ->  modifies0 h0 h1 /\ (
    let prime = getPrime c in
    r == (as_nat c h0 (getX p) < prime && as_nat c h0 (getY p) < prime && as_nat c h0 (getZ p) < prime)))


let isCoordinateValid_public #c p = 
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

  let r = lessX && lessY in
  pop_frame();
  r  


inline_for_extraction noextract
val isCoordinateValid_private: #c: curve -> p: point c -> Stack bool 
  (requires fun h -> live h p /\ as_nat c h (getZ p) == 1)
  (ensures fun h0 r h1 ->  modifies0 h0 h1 /\ (
    let prime = getPrime c in
    r == (as_nat c h0 (getX p) < prime && as_nat c h0 (getY p) < prime && as_nat c h0 (getZ p) < prime)))


let isCoordinateValid_private #c p = 
  push_frame();

  let len = getCoordinateLenU64 c in 
  let tempBuffer = create len (u64 0) in 
  recall_contents #_ #(getCoordinateLenU64 c) (prime_buffer #c) (Lib.Sequence.of_list (prime_list c));
  
  let x = sub p (size 0) len in 
  let y = sub p len len in 
  
  let carryX = sub_bn_prime #c x tempBuffer in
  let carryY = sub_bn_prime #c y tempBuffer in 
  
  let lessX = eq_u64_CT carryX (u64 1) in   
  let lessY = eq_u64_CT carryY (u64 1) in 

  let r = logand lessX lessY in
  pop_frame();
  let z = not (eq_0_u64 r) in 
  z


inline_for_extraction
val multByOrder: #c: curve {isPrimeGroup c == false} -> #l: ladder -> result: point c ->  p: point c -> 
  tempBuffer: lbuffer uint64 (size 20 *! getCoordinateLenU64 c) -> Stack unit 
  (requires fun h -> 
    live h p /\ live h result /\ live h tempBuffer /\ point_eval c h p /\
    LowStar.Monotonic.Buffer.all_disjoint [loc p; loc tempBuffer; loc result])
  (ensures fun h0 _ h1 -> modifies (loc result |+| loc p |+| loc tempBuffer) h0 h1 /\ point_eval c h1 result /\
    scalar_multiplication (Lib.Sequence.of_list (order_u8_list c)) (point_as_nat c h0 p) == point_as_nat c h1 result)

let multByOrder #c #l result p tempBuffer =
  recall_contents (order_u8_buffer #c) (Lib.Sequence.of_list (order_u8_list c));
  scalarMultiplication #c #CONST #l p result (order_u8_buffer #c) tempBuffer


inline_for_extraction noextract
val multByOrder2: #c: curve {isPrimeGroup c == false} -> #l: ladder -> result: point c -> p: point c
  -> tempBuffer: lbuffer uint64 (size 20 *! getCoordinateLenU64 c) -> Stack unit 
  (requires fun h -> 
    live h p /\ live h result /\ live h tempBuffer /\ point_eval c h p /\
    LowStar.Monotonic.Buffer.all_disjoint [loc p; loc tempBuffer; loc result])
  (ensures fun h0 _ h1  -> modifies (loc result |+| loc tempBuffer) h0 h1 /\ point_eval c h1 result /\
    scalar_multiplication (Lib.Sequence.of_list (order_u8_list c)) (point_as_nat c h0 p) == point_as_nat c h1 result)

let multByOrder2 #c #l result p tempBuffer = 
    let h0 = ST.get() in 
  push_frame();
    let len = getCoordinateLenU64 c in 
    let pBuffer = create (size 3 *! len) (u64 0) in 
    let h = ST.get() in 
    Hacl.Impl.P.PointAdd.Aux.lemma_coord_eval c h0 h p;
  copy_point p pBuffer;
  multByOrder #c #l result pBuffer tempBuffer;
  pop_frame()  
    


[@ (Comment "  This code is not side channel resistant")]
inline_for_extraction noextract
val isOrderCorrect_public: #c: curve {isPrimeGroup c == false} -> #l: ladder -> p: point c 
  -> tempBuffer: lbuffer uint64 (size 20 *! getCoordinateLenU64 c) -> Stack bool
  (requires fun h -> 
    live h p /\ live h tempBuffer /\ point_eval c h p)
  (ensures fun h0 r h1 -> modifies (loc tempBuffer) h0 h1 /\ (
    let pointMultOrder = scalar_multiplication (Lib.Sequence.of_list (order_u8_list c)) (point_as_nat c h0 p) in 
     r == Spec.ECC.isPointAtInfinity pointMultOrder))

let isOrderCorrect_public #c #l p tempBuffer = 
    let h0 = ST.get() in 
  push_frame(); 
    let len = getCoordinateLenU64 c in 
    let multResult = create (size 3 *! len) (u64 0) in 
    let h = ST.get() in 
    Hacl.Impl.P.PointAdd.Aux.lemma_coord_eval c h0 h p;
    multByOrder2 #c #l multResult p tempBuffer;
    let result = isPointAtInfinity_public #c multResult in  
  pop_frame();
    result



[@ (Comment "  This code is not side channel resistant")]
inline_for_extraction noextract
val isOrderCorrect_private: #c: curve {isPrimeGroup c == false} -> #l: ladder -> p: point c 
  -> tempBuffer: lbuffer uint64 (size 20 *! getCoordinateLenU64 c) -> Stack bool
  (requires fun h -> 
    live h p /\ live h tempBuffer (* /\ point_eval c h p /\
    LowStar.Monotonic.Buffer.all_disjoint [loc p; loc tempBuffer; ] /\
    ~ (isPointAtInfinity (point_as_nat c h p)) *))
  (ensures fun h0 r h1 -> modifies (loc tempBuffer) h0 h1 /\ (
    let pointMultOrder = scalar_multiplication (Lib.Sequence.of_list (order_u8_list c)) (point_as_nat c h0 p) in 
     r == Spec.ECC.isPointAtInfinity pointMultOrder))
     
let isOrderCorrect_private #c #l p tempBuffer = 
    let h0 = ST.get() in 
  push_frame(); 
    let len = getCoordinateLenU64 c in 
    let multResult = create (size 3 *! len) (u64 0) in 
    let h = ST.get() in 
    Hacl.Impl.P.PointAdd.Aux.lemma_coord_eval c h0 h p;
    multByOrder2 #c #l multResult p tempBuffer;
    let r = isPointAtInfinityPrivate #c multResult in  
  pop_frame();
    let z = not (eq_0_u64 r) in 
    z


inline_for_extraction noextract
val verifyQValidCurvePoint_public_: #c: curve -> #l: ladder -> pubKey: point c 
  -> tempBuffer:lbuffer uint64 (size 20 *! getCoordinateLenU64 c) -> 
  Stack bool
  (requires fun h -> live h pubKey /\ live h tempBuffer /\ 
    LowStar.Monotonic.Buffer.all_disjoint [loc pubKey; loc tempBuffer] /\ as_nat c h (getZ pubKey) == 1)
  (ensures  fun h0 r h1 -> modifies (loc tempBuffer) h0 h1 /\ (
    let p = as_nat c h0 (getX pubKey),  as_nat c h0 (getY pubKey),  as_nat c h0 (getZ pubKey) in 
    ~ (isPointAtInfinity #Jacobian p) /\ r == verifyQValidCurvePointSpec #c p))

let verifyQValidCurvePoint_public_ #c #l pubKey tempBuffer = 
    let h0 = ST.get() in 
  let coordinatesValid = isCoordinateValid_public pubKey in 
  if not coordinatesValid then false else begin
    let h1 = ST.get() in 
    Hacl.Impl.P.PointAdd.Aux.lemma_coord_eval c h0 h1 pubKey;
    let belongsToCurve = isPointOnCurve #c pubKey in 

    [@inline_let]
    let r = normalize_term (isPrimeGroup c) in 
    match r with 
    |true -> coordinatesValid && belongsToCurve
    |false -> let orderCorrect = isOrderCorrect_public #c #l pubKey tempBuffer in coordinatesValid && belongsToCurve && orderCorrect
  end


inline_for_extraction noextract
val verifyQValidCurvePoint_private_: #c: curve -> #l: ladder -> pubKey: point c 
  -> tempBuffer:lbuffer uint64 (size 20 *! getCoordinateLenU64 c) -> 
  Stack bool
  (requires fun h -> live h pubKey /\ live h tempBuffer /\ 
    LowStar.Monotonic.Buffer.all_disjoint [loc pubKey; loc tempBuffer] /\ as_nat c h (getZ pubKey) == 1)
  (ensures  fun h0 r h1 -> modifies (loc tempBuffer) h0 h1 /\ (
    let p = as_nat c h0 (getX pubKey),  as_nat c h0 (getY pubKey),  as_nat c h0 (getZ pubKey) in 
    ~ (isPointAtInfinity #Jacobian p) /\ r == verifyQValidCurvePointSpec #c p))

let verifyQValidCurvePoint_private_ #c #l pubKey tempBuffer = 
    let h0 = ST.get() in 
  let coordinatesValid = isCoordinateValid_private pubKey in 
  if not coordinatesValid then false else begin
    let h1 = ST.get() in 
    Hacl.Impl.P.PointAdd.Aux.lemma_coord_eval c h0 h1 pubKey;
    let belongsToCurve = isPointOnCurve_ pubKey in 

    [@inline_let]
    let r = normalize_term (isPrimeGroup c) in 
    match r with 
    |true -> coordinatesValid && belongsToCurve
    |false -> let orderCorrect = isOrderCorrect_private #c #l pubKey tempBuffer in coordinatesValid && belongsToCurve && orderCorrect
  end


let verifyQValidCurvePoint_private_p256 #l = verifyQValidCurvePoint_private_ #P256 #l

let verifyQValidCurvePoint_private_p384 #l = verifyQValidCurvePoint_private_ #P384 #l

let verifyQValidCurvePoint_private #c #l = 
  match c with 
  |P256 -> verifyQValidCurvePoint_private_p256 #l
  |P384 -> verifyQValidCurvePoint_private_p384 #l


val verifyQValidCurvePoint_public_p256: #l: ladder -> pubKey: point P256 
  -> tempBuffer:lbuffer uint64 (size 20 *! getCoordinateLenU64 P256) -> 
  Stack bool
  (requires fun h -> live h pubKey /\ live h tempBuffer /\ 
    LowStar.Monotonic.Buffer.all_disjoint [loc pubKey; loc tempBuffer] /\ as_nat P256 h (getZ pubKey) == 1)
  (ensures  fun h0 r h1 -> modifies (loc tempBuffer) h0 h1  /\ (
    let p = as_nat P256 h0 (getX pubKey),  as_nat P256 h0 (getY pubKey),  as_nat P256 h0 (getZ pubKey) in 
    ~ (isPointAtInfinity #Jacobian p) /\ r == verifyQValidCurvePointSpec #P256 p))

let verifyQValidCurvePoint_public_p256 = verifyQValidCurvePoint_public_ #P256


val verifyQValidCurvePoint_public_p384: #l: ladder -> pubKey: point P384
  -> tempBuffer:lbuffer uint64 (size 20 *! getCoordinateLenU64 P384) -> 
  Stack bool
  (requires fun h -> live h pubKey /\ live h tempBuffer /\ 
    LowStar.Monotonic.Buffer.all_disjoint [loc pubKey; loc tempBuffer] /\ as_nat P384 h (getZ pubKey) == 1)
  (ensures  fun h0 r h1 -> modifies (loc tempBuffer) h0 h1  /\ (
    let p = as_nat P384 h0 (getX pubKey),  as_nat P384 h0 (getY pubKey),  as_nat P384 h0 (getZ pubKey) in 
    ~ (isPointAtInfinity #Jacobian p) /\ r == verifyQValidCurvePointSpec #P384 p))

let verifyQValidCurvePoint_public_p384 = verifyQValidCurvePoint_public_ #P384


let verifyQValidCurvePoint_public #c #l = 
  match c with 
  |P256 -> verifyQValidCurvePoint_public_p256 #l
  |P384 -> verifyQValidCurvePoint_public_p384 #l


let verifyQ_public #c #l pubKey = 
  push_frame();
    let h0 = ST.get() in
    let len = getCoordinateLenU64 c in 
    
    let tempBuffer = create (size 20 *! len) (u64 0) in 
    let publicKeyJ = create (size 3 *! len) (u64 0) in 
    
  toFormPoint #c pubKey publicKeyJ; 
  let r = verifyQValidCurvePoint_public #c #l publicKeyJ tempBuffer in 
  pop_frame();
  r


let verifyQ_private #c #l pubKey = 
  push_frame();
    let h0 = ST.get() in
    let len = getCoordinateLenU64 c in 
    
    let tempBuffer = create (size 20 *! len) (u64 0) in 
    let publicKeyJ = create (size 3 *! len) (u64 0) in 

  toFormPoint #c pubKey publicKeyJ; 
  let r = verifyQValidCurvePoint_private #c #l publicKeyJ tempBuffer in 
  pop_frame();
  r
