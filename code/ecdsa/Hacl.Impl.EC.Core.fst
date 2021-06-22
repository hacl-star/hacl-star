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
open Hacl.EC.Lemmas

open FStar.Mul
open Hacl.Impl.EC.MontgomeryLadder
open Spec.ECC.Curves


#set-options "--z3rlimit 200 --max_fuel 0 --max_ifuel 0" 

inline_for_extraction noextract 
val toDomain_t: #c: curve -> value: felem c -> result: felem c -> Stack unit 
  (requires fun h -> felem_eval c h value /\ live h value /\ live h result /\ eq_or_disjoint value result)
  (ensures fun h0 _ h1 -> modifies (loc result) h0 h1 /\ as_nat c h1 result = toDomain #c (as_nat c h0 value) /\ 
    felem_eval c h1 result)

let toDomain_t #c value result = 
  push_frame();
    let h0 = ST.get() in 
    let len = getCoordinateLenU64 c in 
    let multBuffer = create (size 2 *! len) (u64 0) in 
    shiftLeftWord value multBuffer;
    reduction multBuffer result;
    lemmaToDomain #c #DH (as_nat c h0 value);
  pop_frame()  

[@CInline]
let toDomain_p256 = toDomain_t #P256 
[@CInline]
let toDomain_p384 = toDomain_t #P384
[@CInline]
let toDomain_generic = toDomain_t #Default

let toDomain #c value result = 
  match c with 
  |P256 -> toDomain_p256 value result
  |P384 -> toDomain_p384 value result
  |Default -> toDomain_generic value result


inline_for_extraction
val fromDomain_t: #c: curve -> f: felem c -> result: felem c -> Stack unit 
  (requires fun h -> live h f /\ live h result /\ felem_eval c h f)
  (ensures fun h0 _ h1 -> modifies (loc result) h0 h1 /\ 
    as_nat c h1 result = (as_nat c h0 f * modp_inv2 #c (pow2 (getPower c))) % getPrime c /\ 
    as_nat c h1 result = fromDomain #c (as_nat c h0 f))

let fromDomain_t f result = 
  montgomery_multiplication_buffer_by_one_dh f result  

[@CInline]
let fromDomain_p256 = fromDomain_t #P256 
[@CInline]
let fromDomain_p384 = fromDomain_t #P384
[@CInline]
let fromDomain_generic = fromDomain_t #Default

let fromDomain #c value result = 
  match c with 
  |P256 -> fromDomain_p256 value result
  |P384 -> fromDomain_p384 value result
  |Default -> fromDomain_generic value result




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


let copy_point #c p result = 
  let h0 = ST.get() in 
    copy result p;
  let h1 = ST.get() in 
    lemma_equal_lseq_equal_nat (as_seq h0 p) (as_seq h1 result);

    let xP = as_seq h0 (getX p) in 
    let yP = as_seq h0 (getY p) in 
    let zP = as_seq h0 (getZ p) in 
    
    let xR = as_seq h1 (getX result) in 
    let yR = as_seq h1 (getY result) in 
    let zR = as_seq h1 (getZ result) in 


    assert(as_seq h0 (gsub p (size 2 *! getCoordinateLenU64 c) (getCoordinateLenU64 c)) == 
      as_seq h1 (gsub result (size 2 *! getCoordinateLenU64 c) (getCoordinateLenU64 c)));

    lemma_equal_lseq_equal_nat xP xR;
    lemma_equal_lseq_equal_nat yP yR;
    lemma_equal_lseq_equal_nat zP zR
 

let getPower2 c = pow2 (getPower c)


(* The point is a point at infinity iff z == 0 *)
let isPointAtInfinityPrivate #c p =  
  let h0 = ST.get() in 
  let len = getCoordinateLenU64 c in 
    
  let start = len *! size 2 in 

  let zCoordinate = sub p start len in 
  let r = isZero_uint64_CT #c zCoordinate in 
    let h1 = ST.get() in 

 lemma_pointAtInfInDomain #c
    (as_nat c h0 (gsub p (size 0) len))
    (as_nat c h0 (gsub p len len))
    (as_nat c h0 (gsub p (2ul *! len) len)); 
  Hacl.Impl.P.PointAdd.Aux.lemma_coord_eval c h0 h1 p;
  r

inline_for_extraction noextract
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
    then z1 == 0 else z1 == 1)))

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
    lemma_create_zero_buffer #U64 (v len) c;

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


inline_for_extraction noextract
val norm_: #c: curve -> p: point c -> resultPoint: point c -> 
  tempBuffer: lbuffer uint64 (size 17 *! getCoordinateLenU64 c) -> Stack unit
  (requires fun h -> live h p /\ live h resultPoint /\ live h tempBuffer /\ point_eval c h p /\
    disjoint p tempBuffer /\ disjoint tempBuffer resultPoint) 
  (ensures fun h0 _ h1 -> point_eval c h1 resultPoint /\
    modifies (loc tempBuffer |+| loc resultPoint) h0 h1 /\ (
    let resultPoint = point_as_nat c h1 resultPoint in 
    let pointD = fromDomainPoint #c #DH (point_as_nat c h0 p) in 
    let pointNorm = _norm #c pointD in
    pointNorm == resultPoint))

let norm_ #c p resultPoint tempBuffer = 
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

[@CInline]
let norm_p256 = norm_ #P256 
[@CInline]
let norm_p384 = norm_ #P384 
[@CInline]
let norm_generic = norm_ #Default 

let norm #c p resultPoint = 
  match c with 
  |P256 -> norm_p256 p resultPoint
  |P384 -> norm_p384 p resultPoint
  |Default -> norm_generic p resultPoint


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

inline_for_extraction noextract
val uploadStartPoints: #c: curve -> q: point c -> p: point c -> result: point c -> Stack unit 
  (requires fun h -> live h q /\ live h p /\ live h result /\
    disjoint p q /\ disjoint q result /\ eq_or_disjoint p result /\ point_eval c h p /\
    ~ (isPointAtInfinity (point_as_nat c h p)))
  (ensures fun h0 _ h1 -> modifies (loc result |+| loc q) h0 h1 /\
    point_eval c h1 q /\ point_eval c h1 result /\ (
    let pD = fromDomainPoint #c #DH (point_as_nat c h1 q) in 
    let qD = fromDomainPoint #c #DH (point_as_nat c h1 result) in 
    qD == point_as_nat c h0 p /\ pD == pointAtInfinity #c /\ 
    pointEqual #c pD (point_mult #c 0 qD) /\ ~ (pointEqual #c pD qD)))

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

inline_for_extraction noextract
val scalar_multiplication_t_0: #c: curve -> #t:buftype -> q: point c -> p: point c -> result: point c -> 
  scalar: scalar_t #t #c -> 
  tempBuffer: lbuffer uint64 (size 17 *! getCoordinateLenU64 c) ->
  Stack unit 
  (requires fun h -> live h q /\ live h p /\ live h result /\ live h scalar /\ live h tempBuffer /\
    LowStar.Monotonic.Buffer.all_disjoint [loc p; loc q; loc tempBuffer; loc scalar] /\
    disjoint q result /\ eq_or_disjoint p result /\ disjoint result tempBuffer /\ disjoint result scalar /\
    point_eval c h p /\ ~ (isPointAtInfinity (point_as_nat c h p)))
  (ensures fun h0 _ h1 -> modifies (loc q |+| loc result |+| loc tempBuffer) h0 h1 /\ point_eval c h1 q /\ (
    let i1 = point_as_nat c h0 p in point_mult_0 i1 0; 
    let pD = fromDomainPoint #c #DH (point_as_nat c h1 q) in
    let r0, r1 = montgomery_ladder_spec_left (as_seq h0 scalar) (pointAtInfinity, i1) in 
    pD == r0))


let scalar_multiplication_t_0 #c q p result scalar tempBuffer = 
  uploadStartPoints q p result; 
  montgomery_ladder q result scalar tempBuffer


val point_mult0_is_infinity: #c: curve -> p: point_nat_prime #c -> Lemma (point_mult #c 0 p == pointAtInfinity)

let point_mult0_is_infinity #c p = Spec.ECC.point_mult_0 p 0


inline_for_extraction
val scalarMultiplication_t: #c: curve -> #t:buftype -> p: point c -> result: point c -> 
  scalar: scalar_t #t #c -> 
  tempBuffer: lbuffer uint64 (size 20 *! getCoordinateLenU64 c) ->
  Stack unit
  (requires fun h -> 
    live h p /\ live h result /\ live h scalar /\ live h tempBuffer /\
    LowStar.Monotonic.Buffer.all_disjoint [loc p; loc tempBuffer; loc scalar; loc result] /\ point_eval c h p /\
    ~ (isPointAtInfinity (point_as_nat c h p)))
  (ensures fun h0 _ h1 -> modifies (loc p |+| loc result |+| loc tempBuffer) h0 h1 /\ point_eval c h1 result /\ (
    let pD = point_as_nat c h1 result in 
    scalar_multiplication (as_seq h0 scalar) (point_as_nat c h0 p) == pD))
(*
val size_cuttable_scalar_mult: #c: curve -> 
  Lemma (let len = getCoordinateLenU64 c in  (v (size 3 *! len) + v (size 17 *! len) <= v (size 20 *! len)))

let size_cuttable_scalar_mult #c = ()
*)

let scalarMultiplication_t #c #t p result scalar tempBuffer  = 
    let h0 = ST.get() in 
  let len = getCoordinateLenU64 c in 
  let q = sub tempBuffer (size 0) (size 3 *! len) in 
  let buff = sub tempBuffer (size 3 *! len) (size 17 *! len) in
  scalar_multiplication_t_0 #c #t q p result scalar buff; 
  norm q result buff; 
  let i1 = point_as_nat c h0 p in 
    point_mult0_is_infinity i1

inline_for_extraction noextract
let scalarMultiplicationL #c = scalarMultiplication_t #c #MUT
let scalarMultiplicationI #c = scalarMultiplication_t #c #IMMUT
inline_for_extraction noextract
let scalarMultiplicationC #c = scalarMultiplication_t #c #CONST

#push-options "--ifuel 1"

let scalarMultiplication #c #buf_type p result scalar tempBuffer = 
  match buf_type with 
  |MUT -> scalarMultiplicationL #c p result scalar tempBuffer 
  |IMMUT -> scalarMultiplicationI #c p result scalar tempBuffer
  |CONST -> scalarMultiplicationC #c p result scalar tempBuffer

#pop-options 

inline_for_extraction noextract
val scalarMultiplicationWithoutNorm_: #c: curve -> p: point c -> result: point c 
  -> scalar: scalar_t #MUT #c
  -> tempBuffer: lbuffer uint64 (size 20 *! getCoordinateLenU64 c) ->
  Stack unit
  (requires fun h -> point_eval c h p /\ live h p /\ live h result /\ live h scalar /\ live h tempBuffer /\
    LowStar.Monotonic.Buffer.all_disjoint [loc p; loc tempBuffer; loc scalar; loc result] /\
    ~ (isPointAtInfinity (point_as_nat c h p)))
  (ensures fun h0 _ h1 -> modifies (loc p |+| loc result |+| loc tempBuffer) h0 h1 /\ point_eval c h1 result /\ (
    let p1 = fromDomainPoint #c #DH (point_as_nat c h1 result) in 
    let p = point_as_nat c h0 p in point_mult_0 #c p 0; 
    let rN, _ = montgomery_ladder_spec_left #c (as_seq h0 scalar) (pointAtInfinity, p) in 
    rN == p1)) 
    
let scalarMultiplicationWithoutNorm_ #c p result scalar tempBuffer = 
    let h0 = ST.get() in 
  let len = getCoordinateLenU64 c in 
  let q = sub tempBuffer (size 0) (size 3 *! len) in 
  let buff = sub tempBuffer (size 3 *! len) (size 17 *! len) in
  normalize_term (scalar_multiplication_t_0 #c #MUT q p result scalar buff); 
  copy_point q result

val scalarMultiplicationWithoutNorm_p256: p: point P256 -> result: point P256
  -> scalar: scalar_t #MUT #P256
  -> tempBuffer: lbuffer uint64 (size 20 *! getCoordinateLenU64 P256) ->
  Stack unit
  (requires fun h -> point_eval P256 h p /\ live h p /\ live h result /\ live h scalar /\ live h tempBuffer /\
    LowStar.Monotonic.Buffer.all_disjoint [loc p; loc tempBuffer; loc scalar; loc result] /\
    ~ (isPointAtInfinity (point_as_nat P256 h p)))
  (ensures fun h0 _ h1 -> modifies (loc p |+| loc result |+| loc tempBuffer) h0 h1 /\ point_eval P256 h1 result /\ (
    let p1 = fromDomainPoint #P256 #DH (point_as_nat P256 h1 result) in 
    let p = point_as_nat P256 h0 p in point_mult_0 #P256 p 0; 
    let rN, _ = montgomery_ladder_spec_left #P256 (as_seq h0 scalar) (pointAtInfinity, p) in 
    rN == p1)) 

[@CInline]
let scalarMultiplicationWithoutNorm_p256 = scalarMultiplicationWithoutNorm_ #P256


val scalarMultiplicationWithoutNorm_p384: p: point P384 -> result: point P384
  -> scalar: scalar_t #MUT #P384
  -> tempBuffer: lbuffer uint64 (size 20 *! getCoordinateLenU64 P384) ->
  Stack unit
  (requires fun h -> point_eval P384 h p /\ live h p /\ live h result /\ live h scalar /\ live h tempBuffer /\
    LowStar.Monotonic.Buffer.all_disjoint [loc p; loc tempBuffer; loc scalar; loc result] /\
    ~ (isPointAtInfinity (point_as_nat P384 h p)))
  (ensures fun h0 _ h1 -> modifies (loc p |+| loc result |+| loc tempBuffer) h0 h1 /\ point_eval P384 h1 result /\ (
    let p1 = fromDomainPoint #P384 #DH (point_as_nat P384 h1 result) in 
    let p = point_as_nat P384 h0 p in point_mult_0 #P384 p 0; 
    let rN, _ = montgomery_ladder_spec_left #P384 (as_seq h0 scalar) (pointAtInfinity, p) in 
    rN == p1)) 

[@CInline]
let scalarMultiplicationWithoutNorm_p384 = scalarMultiplicationWithoutNorm_ #P384

val scalarMultiplicationWithoutNorm_generic: p: point Default -> result: point Default
  -> scalar: scalar_t #MUT #Default
  -> tempBuffer: lbuffer uint64 (size 20 *! getCoordinateLenU64 Default) ->
  Stack unit
  (requires fun h -> point_eval Default h p /\ live h p /\ live h result /\ live h scalar /\ live h tempBuffer /\
    LowStar.Monotonic.Buffer.all_disjoint [loc p; loc tempBuffer; loc scalar; loc result] /\
    ~ (isPointAtInfinity (point_as_nat Default h p)))
  (ensures fun h0 _ h1 -> modifies (loc p |+| loc result |+| loc tempBuffer) h0 h1 /\ point_eval Default h1 result /\ (
    let p1 = fromDomainPoint #Default #DH (point_as_nat Default h1 result) in 
    let p = point_as_nat Default h0 p in point_mult_0 #Default p 0; 
    let rN, _ = montgomery_ladder_spec_left #Default (as_seq h0 scalar) (pointAtInfinity, p) in 
    rN == p1)) 

[@CInline]
let scalarMultiplicationWithoutNorm_generic = scalarMultiplicationWithoutNorm_ #Default


let scalarMultiplicationWithoutNorm #c = 
  match c with 
  |P256 -> scalarMultiplicationWithoutNorm_p256
  |P384 -> scalarMultiplicationWithoutNorm_p384
  |Default -> scalarMultiplicationWithoutNorm_generic


inline_for_extraction noextract
val uploadStartPointsS2P: #c: curve -> q: point c -> result: point c -> Stack unit 
  (requires fun h -> live h q /\ live h result /\ disjoint q result)
  (ensures fun h0 _ h1 -> modifies (loc result |+| loc q) h0 h1 /\
    point_eval c h1 q /\ point_eval c h1 result /\ (
    let pD = fromDomainPoint #c #DH (point_as_nat c h1 q) in 
    let qD = fromDomainPoint #c #DH (point_as_nat c h1 result) in 
    qD == basePoint #c /\ pD == pointAtInfinity #c /\ 
    pointEqual #c pD (point_mult #c 0 qD) /\ ~ (pointEqual #c pD qD)))

let uploadStartPointsS2P #c q result = 
  uploadZeroPoint #c q;
    let h1 = ST.get() in 
  Hacl.Impl.EC.Setup.uploadBasePoint #c result;
    let h2 = ST.get() in 
    Hacl.Impl.P.PointAdd.Aux.lemma_coord_eval c h1 h2 q;
    lemma_pif_to_domain #c h1 q;
  let qD = fromDomainPoint #c #DH (point_as_nat c h2 result) in 
    point_mult_0 #c qD 0; 
    let x, y, z = point_as_nat c h2 result in 
    lemma_pointAtInfInDomain #c x y z

inline_for_extraction noextract
val secretToPublic_0: #c: curve -> #t: buftype -> q: point c -> result: point c -> 
  scalar: lbuffer_t t uint8 (getScalarLenBytes c) -> 
  tempBuffer: lbuffer uint64 (size 17 *! getCoordinateLenU64 c) ->
  Stack unit 
  (requires fun h -> live h q /\ live h result /\ live h scalar /\ live h tempBuffer /\
    LowStar.Monotonic.Buffer.all_disjoint [loc q; loc tempBuffer; loc scalar] /\
    disjoint q result /\ disjoint result tempBuffer /\ disjoint result scalar)
  (ensures fun h0 _ h1 -> modifies (loc q |+| loc result |+| loc tempBuffer) h0 h1 /\ point_eval c h1 q /\ (
    let i1 = basePoint #c in 
    point_mult_0 i1 0; 
    let pD = fromDomainPoint #c #DH (point_as_nat c h1 q) in
    let r0, _ = montgomery_ladder_spec_left (as_seq h0 scalar) (pointAtInfinity , i1) in pD == r0))


let secretToPublic_0 #c q result scalar tempBuffer = 
  uploadStartPointsS2P q result; 
(*   montgomery_ladder q result scalar tempBuffer *)
  Hacl.Impl.EC.Masking.ScalarAccess.montgomery_ladder_2_precomputed result scalar tempBuffer;
  copy q result


let secretToPublic #c result scalar tempBuffer = 
  let h0 = ST.get() in 
  let len = getCoordinateLenU64 c in 
  let q = sub tempBuffer (size 0) (size 3 *! len) in
  let buff = sub tempBuffer (size 3 *! len) (size 17 *! len) in 

  secretToPublic_0 q result scalar buff;
  norm q result buff


inline_for_extraction noextract
val secretToPublicWithoutNorm_: #c: curve -> result: point c 
  -> scalar: scalar_t #MUT #c
  -> tempBuffer: lbuffer uint64 (size 20 *! getCoordinateLenU64 c) ->
  Stack unit (requires fun h -> live h result /\ live h scalar /\ live h tempBuffer /\ 
    LowStar.Monotonic.Buffer.all_disjoint [loc tempBuffer; loc scalar; loc result])
  (ensures fun h0 _ h1 -> point_eval c h1 result /\ modifies (loc result |+| loc tempBuffer) h0 h1 /\ (
    let p1 = fromDomainPoint #c #DH (point_as_nat c h1 result) in point_mult_0 (basePoint #c) 0;
    let rN, _ = montgomery_ladder_spec_left (as_seq h0 scalar) (pointAtInfinity, basePoint #c) in 
    p1 == rN))  


let secretToPublicWithoutNorm_ #c result scalar tempBuffer = 
  let len = getCoordinateLenU64 c in 
  let q = sub tempBuffer (size 0) (size 3 *! len) in
  let buff = sub tempBuffer (size 3 *! len) (size 17 *! len) in 

  uploadStartPointsS2P result q; 
  montgomery_ladder result q scalar buff

[@CInline]
val secretToPublicWithoutNorm_p256: result: point P256
  -> scalar: scalar_t #MUT #P256
  -> tempBuffer: lbuffer uint64 (size 20 *! getCoordinateLenU64 P256) ->
  Stack unit (requires fun h -> live h result /\ live h scalar /\ live h tempBuffer /\ 
    LowStar.Monotonic.Buffer.all_disjoint [loc tempBuffer; loc scalar; loc result])
  (ensures fun h0 _ h1 -> point_eval P256 h1 result /\ modifies (loc result |+| loc tempBuffer) h0 h1 /\ (
    let p1 = fromDomainPoint #P256 #DH (point_as_nat P256 h1 result) in point_mult_0 (basePoint #P256) 0;
    let rN, _ = montgomery_ladder_spec_left (as_seq h0 scalar) (pointAtInfinity, basePoint #P256) in 
    p1 == rN))  


let secretToPublicWithoutNorm_p256 = secretToPublicWithoutNorm_ #P256

[@CInline]
val secretToPublicWithoutNorm_p384: result: point P384
  -> scalar: scalar_t #MUT #P384
  -> tempBuffer: lbuffer uint64 (size 20 *! getCoordinateLenU64 P384) ->
  Stack unit (requires fun h -> live h result /\ live h scalar /\ live h tempBuffer /\ 
    LowStar.Monotonic.Buffer.all_disjoint [loc tempBuffer; loc scalar; loc result])
  (ensures fun h0 _ h1 -> point_eval P384 h1 result /\ modifies (loc result |+| loc tempBuffer) h0 h1 /\ (
    let p1 = fromDomainPoint #P384 #DH (point_as_nat P384 h1 result) in point_mult_0 (basePoint #P384) 0;
    let rN, _ = montgomery_ladder_spec_left (as_seq h0 scalar) (pointAtInfinity, basePoint #P384) in 
    p1 == rN))  


let secretToPublicWithoutNorm_p384 = secretToPublicWithoutNorm_ #P384

[@CInline]
val secretToPublicWithoutNorm_generic: result: point Default
  -> scalar: scalar_t #MUT #Default
  -> tempBuffer: lbuffer uint64 (size 20 *! getCoordinateLenU64 Default) ->
  Stack unit (requires fun h -> live h result /\ live h scalar /\ live h tempBuffer /\ 
    LowStar.Monotonic.Buffer.all_disjoint [loc tempBuffer; loc scalar; loc result])
  (ensures fun h0 _ h1 -> point_eval Default h1 result /\ modifies (loc result |+| loc tempBuffer) h0 h1 /\ (
    let p1 = fromDomainPoint #Default #DH (point_as_nat Default h1 result) in point_mult_0 (basePoint #Default) 0;
    let rN, _ = montgomery_ladder_spec_left (as_seq h0 scalar) (pointAtInfinity, basePoint #Default) in 
    p1 == rN))  


let secretToPublicWithoutNorm_generic = secretToPublicWithoutNorm_ #Default


let secretToPublicWithoutNorm #c = 
  match c with 
  |P256 -> secretToPublicWithoutNorm_p256
  |P384 -> secretToPublicWithoutNorm_p384
  |Default -> secretToPublicWithoutNorm_generic
