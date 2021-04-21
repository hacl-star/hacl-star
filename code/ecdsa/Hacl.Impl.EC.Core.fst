module Hacl.Impl.EC.Core 

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer

open Hacl.Spec.EC.Definition
open Spec.ECC
open Hacl.Impl.EC.Reduction
open Hacl.Impl.EC.Exponent

open Hacl.Impl.EC.MontgomeryMultiplication
open Hacl.Impl.EC.Math 
open Hacl.Impl.EC.Masking

open FStar.Tactics 
open FStar.Tactics.Canon

open FStar.Math.Lemmas
open Hacl.Lemmas.P256

open FStar.Mul
open Hacl.Impl.EC.MontgomeryLadder
open Spec.ECC.Curves


#set-options "--z3rlimit 200" 

let toDomain #c value result = 
  push_frame();
    let h0 = ST.get() in 
    let len = getCoordinateLenU64 c in 
    let multBuffer = create (size 2 *! len) (u64 0) in 
    shiftLeftWord value multBuffer;
    reduction multBuffer result;
    lemmaToDomain #c #DH (as_nat c h0 value);
  pop_frame()  


let fromDomain f result = 
  montgomery_multiplication_buffer_by_one_dh f result  


let pointToDomain #c p result = 
  let h0 = ST.get() in 
  let len = getCoordinateLenU64 c in 
  
  let p_x = sub p (size 0) len in 
  let p_y = sub p len len in 
  let p_z = sub p (size 2 *! len) len in 
    
  let r_x = sub result (size 0) len in 
  let r_y = sub result len len in 
  let r_z = sub result (size 2 *! len) len in 

  toDomain #c p_x r_x;
  toDomain #c p_y r_y;
  toDomain #c p_z r_z


let pointFromDomain #c p result = 
  let len = getCoordinateLenU64 c in 

  let p_x = sub p (size 0) len in 
  let p_y = sub p len len in 
  let p_z = sub p (size 2 *! len) len in 

  let r_x = sub result (size 0) len in 
  let r_y = sub result len len in 
  let r_z = sub result (size 2 *! len) len in 

  fromDomain #c p_x r_x;
  fromDomain #c p_y r_y;
  fromDomain #c p_z r_z


val copy_point: #c: curve ->  p: point c -> result: point c -> Stack unit 
  (requires fun h -> live h p /\ live h result /\ disjoint p result) 
  (ensures fun h0 _ h1 -> modifies (loc result) h0 h1 /\ as_seq h1 result == as_seq h0 p)

let copy_point p result = copy result p
 
let getPower2 c = pow2 (getPower c)

(* https://crypto.stackexchange.com/questions/43869/point-at-infinity-and-error-handling*)
val lemma_pointAtInfInDomain: #c: curve -> x: nat -> y: nat -> z: nat {z < getPrime c} -> 
  Lemma (
    isPointAtInfinity (x, y, z) == 
    isPointAtInfinity ((fromDomain_ #c #DH x), (fromDomain_ #c #DH y), (fromDomain_ #c #DH z)))

let lemma_pointAtInfInDomain #c x y z =
  lemmaFromDomain #c #DH z;
  lemma_multiplication_not_mod_prime #c z


(* The point is a point at infinity iff z == 0 *)
let isPointAtInfinityPrivate #c p =  
  let h0 = ST.get() in 
  let len = getCoordinateLenU64 c in 
    
  let start = len *! size 2 in 

  let zCoordinate = sub p start len in 
  let r = isZero_uint64_CT #c zCoordinate in 

 lemma_pointAtInfInDomain #c
    (as_nat c h0 (gsub p (size 0) len))
    (as_nat c h0 (gsub p len len))
    (as_nat c h0 (gsub p (2ul *! len) len)); 
  r

val normalisation_update: #c: curve -> z2x: felem c -> z3y: felem c -> p: point c -> resultPoint: point c -> 
  Stack unit 
  (requires fun h -> live h z2x /\ live h z3y /\ live h resultPoint /\ live h p /\ 
    felem_eval c h z2x /\ felem_eval c h z3y /\ felem_eval c h (getZ p) /\ point_eval c h p /\
    disjoint z2x z3y /\ disjoint z2x resultPoint /\ disjoint z3y resultPoint)
  (ensures fun h0 _ h1 -> modifies (loc resultPoint) h0 h1 /\ point_eval c h1 resultPoint /\ (
    let x0, y0, z0 = point_as_nat c h0 p in 
    let x1, y1, z1 = point_as_nat c h1 resultPoint in
    x1 == fromDomain_ #c #DH (as_nat c h0 z2x) /\ 
    y1 == fromDomain_ #c #DH (as_nat c h0 z3y) /\ (
    if Spec.ECC.isPointAtInfinity (fromDomain_ #c #DH x0, fromDomain_ #c #DH y0, fromDomain_ #c #DH z0) 
    then z1 == 0 else  z1 == 1)))

let normalisation_update #c z2x z3y p resultPoint = 
  push_frame(); 
    let len = getCoordinateLenU64 c in 
    
  let zeroBuffer = create len (u64 0) in   
  let resultX = sub resultPoint (size 0) len in 
  let resultY = sub resultPoint len len in 
  let resultZ = sub resultPoint (size 2 *! len) len in 
  
  let bit = isPointAtInfinityPrivate p in

  fromDomain z2x resultX; 
  fromDomain z3y resultY;
  uploadOneImpl #c resultZ;
  copy_conditional #c resultZ zeroBuffer bit;
    lemma_create_zero_buffer (v len) c;

  pop_frame()


val lemma_norm: #c: curve -> pD : point_nat_prime #c -> r: point_nat_prime #c ->
  Lemma 
  (requires (
    let prime = getPrime c in 
    let xD, yD, zD = pD in 
    let x3, y3, z3 = r in 
    x3 == xD * (pow (zD * zD % prime) (prime - 2) % prime) % prime /\
    y3 == yD * (pow ((zD * zD % prime) * zD % prime) (prime - 2) % prime) % prime/\
    (if Spec.ECC.isPointAtInfinity (xD, yD, zD) then z3 == 0 else z3 == 1)))
  (ensures (let xN, yN, zN = _norm #c pD in r == (xN, yN, zN))) 


let lemma_norm #c pD r = 
  let prime = getPrime c in 

  let xD, yD, zD = pD in 
  let x3, y3, z3 = r in 

  calc (==)
  {
    xD * (pow (zD * zD % prime) (prime - 2) % prime) % prime;
    (==) {lemma_pow_mod_n_is_fpow prime (zD * zD % prime) (prime - 2)}
    xD * (modp_inv2 #c (zD * zD)) % prime;
    (==) {_ by (canon())}
    modp_inv2 #c (zD * zD) * xD % prime; 
  };  

  calc (==) 
  {
    yD * (pow ((zD * zD % prime) * zD % prime) (prime - 2) % prime) % prime;
    (==) {lemma_mod_mul_distr_l (zD * zD) zD prime}
    yD * (pow (zD * zD * zD % prime) (prime - 2) % prime) % prime;
    (==) {lemma_pow_mod_n_is_fpow prime (zD * zD * zD % prime) (prime - 2)}
    yD * (modp_inv2 #c (zD * zD * zD)) % prime;
    (==) {}
    yD * (modp_inv2 #c (zD * zD * zD)) % prime;
    (==) {_ by (canon())}
    modp_inv2 #c (zD * zD * zD) * yD % prime;
  }



let norm #c p resultPoint tempBuffer = 
  [@inline_let]
  let len = getCoordinateLenU64 c in 

  let xf = sub p (size 0) len in 
  let yf = sub p len len in 
  let zf = sub p (size 2 *! len) len in 
  
  let z2f = sub tempBuffer len len in 
  let z3f = sub tempBuffer (size 2 *! len) len in

  let t8 = sub tempBuffer (3ul *! len) (8ul *! len) in 

    let h0 = ST.get() in 
  montgomery_square_buffer_dh #c zf z2f;
  montgomery_multiplication_buffer_dh #c z2f zf z3f; 

  exponent #c z2f z2f t8; 
  exponent #c z3f z3f t8; 
  montgomery_multiplication_buffer_dh #c xf z2f z2f;
  montgomery_multiplication_buffer_dh #c yf z3f z3f;
  normalisation_update z2f z3f p resultPoint; 

    let h1 = ST.get() in 

  lemma_norm #c
    (fromDomainPoint #c #DH (point_as_nat c h0 p)) (point_as_nat c h1 resultPoint)


let normX #c p result tempBuffer = 
  [@inline_let]
  let len = getCoordinateLenU64 c in 
  
  let xf = sub p (size 0) len in 
  let zf = sub p (size 2 *! len) len in 
  
  let z2f = sub tempBuffer len len in 
  let t8 = sub tempBuffer (3ul *. len) (8ul *. len) in 

    let h0 = ST.get() in 
  montgomery_square_buffer_dh #c zf z2f; 
  exponent #c z2f z2f t8; 
  montgomery_multiplication_buffer_dh #c z2f xf z2f; 
  fromDomain z2f result;

  
    let prime = getPrime c in 

    let xD = fromDomain_ #c #DH (as_nat c h0 xf) in 
    let zD = fromDomain_ #c #DH (as_nat c h0 zf) in 
    
    calc (==)
    {
      (pow (zD * zD % prime) (prime - 2) % prime) * xD % prime;
      (==) {lemma_pow_mod_n_is_fpow prime (zD * zD % prime) (prime - 2)}
      (modp_inv2 #c (zD * zD)) * xD % prime;
    }  


val lemma_point_to_domain: #c: curve ->  h0: mem -> h1: mem ->  p: point c -> result: point c ->
  Lemma (requires (point_eval c h0 p /\ point_eval c h1 result /\
    point_x_as_nat c h1 result == toDomain_ #c #DH (point_x_as_nat c h0 p) /\
    point_y_as_nat c h1 result == toDomain_ #c #DH (point_y_as_nat c h0 p) /\
    point_z_as_nat c h1 result == toDomain_ #c #DH (point_z_as_nat c h0 p)))
   (ensures (fromDomainPoint #c #DH (point_as_nat c h1 result) == point_as_nat c h0 p))

let lemma_point_to_domain #c h0 h1 p result = ()


val lemma_pif_to_domain: #c: curve -> h: mem -> p: point c -> Lemma
  (requires (point_eval c h p /\ point_x_as_nat c h p == 0 /\ point_y_as_nat c h p == 0 /\ point_z_as_nat c h p == 0))
  (ensures (fromDomainPoint #c #DH (point_as_nat c h p) == point_as_nat c h p))


let lemma_pif_to_domain #c h p = 
  let (x, y, z) = point_as_nat c h p in 
  let (x3, y3, z3) = fromDomainPoint #c #DH (x, y, z) in 
  lemmaFromDomain #c #DH x;
  lemmaFromDomain #c #DH y;
  lemmaFromDomain #c #DH z;
  lemma_multiplication_not_mod_prime #c x; 
  lemma_multiplication_not_mod_prime #c y;
  lemma_multiplication_not_mod_prime #c z


val lemma_coord: #c: curve -> h3: mem -> q: point c {point_eval c h3 q} -> Lemma (
   let (r0, r1, r2) = fromDomainPoint #c #DH (point_as_nat c h3 q) in 
   let xD = fromDomain_ #c #DH (point_x_as_nat c h3 q) in 
   let yD = fromDomain_ #c #DH (point_y_as_nat c h3 q) in 
   let zD = fromDomain_ #c #DH (point_z_as_nat c h3 q) in 
   r0 == xD /\ r1 == yD /\ r2 == zD)	

let lemma_coord h3 q = ()


val uploadStartPoints: #c: curve -> q: point c -> p: point c -> result: point c -> Stack unit 
  (requires fun h -> live h q /\ live h p /\ live h result /\ 
    disjoint p q /\ disjoint q result /\ eq_or_disjoint p result /\ point_eval c h p /\
    ~ (isPointAtInfinity (point_as_nat c h p)))
  (ensures fun h0 _ h1 -> modifies (loc result |+| loc q) h0 h1 /\
    point_eval c h1 q /\ point_eval c h1 result /\ (
    let pD = fromDomainPoint #c #DH (point_as_nat c h1 q) in 
    let qD = fromDomainPoint #c #DH (point_as_nat c h1 result) in 
    qD == point_as_nat c h0 p /\ isPointAtInfinity pD /\  pointEqual #c pD (point_mult #c 0 qD) /\ ~ (pointEqual #c pD qD)))

let uploadStartPoints #c q p result = 
    let h0 = ST.get() in 
  uploadZeroPoint #c q;
    let h1 = ST.get() in 
  Hacl.Impl.P.PointAdd.Aux.lemma_coord_eval c h0 h1 p;
  pointToDomain #c p result;
    let h2 = ST.get() in 
  Hacl.Impl.P.PointAdd.Aux.lemma_coord_eval c h1 h2 q;
  
  lemma_point_to_domain h1 h2 p result;
  lemma_pif_to_domain #c h1 q;

  let qD = fromDomainPoint #c #DH (point_as_nat c h2 result) in 
  point_mult_0 #c qD 0; 

  let x, y, z = point_as_nat c h2 result in 
  lemma_pointAtInfInDomain #c x y z


val scalar_multiplication_t_0: #c: curve -> #t:buftype -> q: point c -> p: point c -> result: point c -> 
  scalar: lbuffer_t t uint8 (getScalarLenBytes c) -> 
  tempBuffer: lbuffer uint64 (size 17 *! getCoordinateLenU64 c) ->
  Stack unit 
  (requires fun h -> live h q /\ live h p /\ live h result /\ live h scalar /\ live h tempBuffer /\
    LowStar.Monotonic.Buffer.all_disjoint [loc p; loc q; loc tempBuffer; loc scalar] /\
    disjoint q result /\ eq_or_disjoint p result /\ disjoint result tempBuffer /\ disjoint result scalar /\
    point_eval c h p /\ ~ (isPointAtInfinity (point_as_nat c h p)))
  (ensures fun h0 _ h1 -> modifies (loc q |+| loc result |+| loc tempBuffer) h0 h1 /\ point_eval c h1 q /\ (
    let i1 = point_as_nat c h0 p in 
    point_mult_0 i1 0; 
    let pD = fromDomainPoint #c #DH (point_as_nat c h1 q) in
    let r0, r1 = montgomery_ladder_spec_left (as_seq h0 scalar) (pointAtInfinity , i1) in pointEqual pD r0))


let scalar_multiplication_t_0 #c  q p result scalar tempBuffer = 
    let h0 = ST.get() in 
  uploadStartPoints q p result; 
    let h1 = ST.get() in 
  montgomery_ladder q result scalar tempBuffer


val point_mult_0: #c: curve -> p: point_nat_prime #c ->  Lemma (point_mult #c 0 p == pointAtInfinity)

let point_mult_0 #c p = Spec.ECC.point_mult_0 p 0


inline_for_extraction
val scalarMultiplication_t: #c: curve -> #t:buftype -> p: point c -> result: point c -> 
  scalar: lbuffer_t t uint8 (getScalarLenBytes c) -> 
  tempBuffer: lbuffer uint64 (size 20 *! getCoordinateLenU64 c) ->
  Stack unit
  (requires fun h -> 
    live h p /\ live h result /\ live h scalar /\ live h tempBuffer /\
    LowStar.Monotonic.Buffer.all_disjoint [loc p; loc tempBuffer; loc scalar; loc result] /\ point_eval c h p /\
    ~ (isPointAtInfinity (point_as_nat c h p)))
  (ensures fun h0 _ h1 -> modifies (loc p |+| loc result |+| loc tempBuffer) h0 h1 /\ point_eval c h1 result /\ (
    pointEqual (scalar_multiplication (as_seq h0 scalar) (point_as_nat c h0 p)) (point_as_nat c h1 result)))

val size_cuttable_scalar_mult: #c: curve -> 
  Lemma (let len = getCoordinateLenU64 c in  (v (size 3 *! len) + v (size 17 *! len) <= v (size 20 *! len)))

let size_cuttable_scalar_mult #c = ()

let scalarMultiplication_t #c #t p result scalar tempBuffer  = 
    let h0 = ST.get() in 
  let len = getCoordinateLenU64 c in 
  let q = sub tempBuffer (size 0) (size 3 *! len) in 
  size_cuttable_scalar_mult #c;
  let buff = sub tempBuffer (size 3 *! len) (size 17 *! len) in
  scalar_multiplication_t_0 q p result scalar buff; 
  norm q result buff; 
  let i1 = point_as_nat c h0 p in 
    point_mult_0 i1


let scalarMultiplicationL #c = scalarMultiplication_t #c #MUT
let scalarMultiplicationI #c = scalarMultiplication_t #c #IMMUT
let scalarMultiplicationC #c = scalarMultiplication_t #c #CONST


let scalarMultiplication #c #buf_type p result scalar tempBuffer = 
  match buf_type with 
  |MUT -> scalarMultiplicationL #c p result scalar tempBuffer 
  |IMMUT -> scalarMultiplicationI #c p result scalar tempBuffer
  |CONST -> scalarMultiplicationC #c p result scalar tempBuffer


let scalarMultiplicationWithoutNorm #c p result scalar tempBuffer = 
  let h0 = ST.get() in  
  let len = getCoordinateLenU64 c in 
  let q = sub tempBuffer (size 0) (size 3 *! len) in 
  uploadZeroPoint #c q;
  let buff = sub tempBuffer (size 3 *! len) (size 22 *! len) in 
  pointToDomain p result;
    let h1 = ST.get() in 
    admit();
  montgomery_ladder q result scalar buff;
  copy_point q result;  
    lemma_point_to_domain h0 h1 p result;
    lemma_pif_to_domain #c h1 q
    

let secretToPublic #c result scalar tempBuffer = 
  push_frame(); 
    let len = getCoordinateLenU64 c in 
    let basePoint = create (size 3 *! len) (u64 0) in 
  uploadBasePoint #c basePoint;
    let q = sub tempBuffer (size 0) (size 3 *! len) in 
    let buff = sub tempBuffer (size 3 *! len) (size 22 *! len) in 
  uploadZeroPoint #c q; 
  admit();
  let h1 = ST.get() in 
    lemma_pif_to_domain #c h1 q;
  montgomery_ladder #c q basePoint scalar buff; 
  norm q result buff;  
  pop_frame();
  admit()


let secretToPublicWithoutNorm #c result scalar tempBuffer = 
  push_frame(); 
    let len = getCoordinateLenU64 c in 
    let basePoint = create (size 3 *! len) (u64 0) in 
  uploadBasePoint #c basePoint;
      let q = sub tempBuffer (size 0) (size 3 *! len) in 
      let buff = sub tempBuffer (size 3 *! len) (size 22 *! len) in 
  uploadZeroPoint #c q; 
  admit();
      let h1 = ST.get() in 
      lemma_pif_to_domain #c h1 q; 
  montgomery_ladder #c q basePoint scalar buff; 
  copy_point q result;
  pop_frame()  



