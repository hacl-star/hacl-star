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
open Hacl.Impl.EC.ScalarMult.Radix

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
(* [@CInline]
let toDomain_generic = toDomain_t #Default *)

let toDomain #c value result = 
  match c with 
  |P256 -> toDomain_p256 value result
  |P384 -> toDomain_p384 value result
(*   |Default -> toDomain_generic value result *)


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
(* [@CInline]
let fromDomain_generic = fromDomain_t #Default *)

let fromDomain #c value result = 
  match c with 
  |P256 -> fromDomain_p256 value result
  |P384 -> fromDomain_p384 value result
  (* |Default -> fromDomain_generic value result *)


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
    if Spec.ECC.isPointAtInfinity #Jacobian (fromDomain_ #c #DH x0, fromDomain_ #c #DH y0, fromDomain_ #c #DH z0) 
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
    (if Spec.ECC.isPointAtInfinity #Jacobian (xD, yD, zD) then z3 == 0 else z3 == 1)))
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
(* [@CInline]
let norm_generic = norm_ #Default  *)

let norm #c p resultPoint tempBuffer = 
  match c with 
  |P256 -> norm_p256 p resultPoint tempBuffer
  |P384 -> norm_p384 p resultPoint tempBuffer
  (* |Default -> norm_generic p resultPoint *)


let norm_out #c p result = 
    let h0 = ST.get() in 
    push_frame();
  let tempBuffer = create (size 17 *! getCoordinateLenU64 c) (u64 0) in 
  let h1 = ST.get() in 
    Hacl.Impl.P.PointAdd.Aux.lemma_coord_eval c h0 h1 p;
  norm p result tempBuffer;
    let h2 = ST.get() in 
    pop_frame();
    let h3 = ST.get() in 
    Hacl.Impl.P.PointAdd.Aux.lemma_coord_eval c h2 h3 result


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
  Lemma 
  (requires (point_eval c h0 p /\ point_eval c h1 result /\
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
    ~ (isPointAtInfinity #Jacobian (point_as_nat c h p)))
  (ensures fun h0 _ h1 -> modifies (loc result |+| loc q) h0 h1 /\
    point_eval c h1 q /\ point_eval c h1 result /\ (
    let pD = fromDomainPoint #c #DH (point_as_nat c h1 q) in 
    let qD = fromDomainPoint #c #DH (point_as_nat c h1 result) in 
    qD == point_as_nat c h0 p /\ isPointAtInfinity pD /\ 
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
val scalar_multiplication_t_0: #c: curve -> #t:buftype -> #l : ladder
  ->  p: point c 
  -> result: point c 
  -> scalar: scalar_t #t #c 
  -> tempBuffer: lbuffer uint64 (size 20 *! getCoordinateLenU64 c) ->
  Stack unit 
  (requires fun h ->  live h p /\ live h result /\ live h scalar /\ live h tempBuffer /\
    LowStar.Monotonic.Buffer.all_disjoint [loc p;  loc tempBuffer; loc scalar] /\
    eq_or_disjoint p result /\ disjoint result tempBuffer /\ disjoint result scalar /\
    point_eval c h p /\ ~ (isPointAtInfinity #Jacobian (point_as_nat c h p)) /\
    scalar_as_nat (as_seq h scalar) < getOrder #c)
  (ensures fun h0 _ h1 -> modifies (loc result |+| loc tempBuffer) h0 h1 /\ point_eval c h1 result /\ (
    let p0 = point_as_nat c h0 p in 
    let qD = fromDomainPoint #c #DH (point_as_nat c h1 result) in
    pointEqual qD (point_mult #c (scalar_as_nat #c (as_seq h0 scalar)) p0)))
    

let scalar_multiplication_t_0 #c #t #l p result scalar tempBuffer = 
  let h0 = ST.get() in 
  match l with 
  |MontLadder -> begin
    push_frame();
    let len = getCoordinateLenU64 c in 
    let q = sub tempBuffer (size 0) (size 3 *! len) in
    let temp = sub tempBuffer (size 3 *! len) (size 17 *! len) in 
      let h1 = ST.get() in 
      Hacl.Impl.P.PointAdd.Aux.lemma_coord_eval c h0 h1 p;
    uploadStartPoints q p result; 
    montgomery_ladder q result scalar temp; 
    copy_point q result; 
      let h2 = ST.get() in 
      pop_frame();
	let h3 = ST.get() in 
	Hacl.Impl.P.PointAdd.Aux.lemma_coord_eval c h2 h3 result
    end
  |Radix -> 
    pointToDomain #c p result;
    Hacl.Impl.EC.ScalarMult.Radix.scalar_mult_radix #c result scalar tempBuffer


val point_mult0_is_infinity: #c: curve -> p: point_nat_prime #c ->
  Lemma (isPointAtInfinity (point_mult #c 0 p))

let point_mult0_is_infinity #c p = Spec.ECC.point_mult_0 #c p 0


val exp_of_one: a: pos { a > 1} -> b: pos ->  Lemma (exp #a 1 b == 1)

let rec exp_of_one a b = 
  match b with 
  |1 -> assert_norm (exp #a 1 1 == 1)
  |_ -> 
    exp_of_one a (b - 1);
    lemma_pow_mod_n_is_fpow a 1 (b - 1); 
    pow_plus 1 (b - 1) 1;
    lemma_mod_mul_distr_l (pow 1 (b - 1)) (pow 1 1) a;
    power_one 1;
    lemma_pow_mod_n_is_fpow a 1 b


val norm_twice_lemma: #c: curve ->  a: point_nat_prime #c -> q: point_nat_prime #c -> 
  Lemma (pointEqual #c a q ==> pointEqual (_norm #c a) q)

let norm_twice_lemma #c p q =
  let prime = getPrime c in  
  calc (==) {
    modp_inv_prime prime (1 % prime);
  (==) {small_mod 1 prime} 
    modp_inv_prime prime 1;
  (==) {exp_of_one prime (prime - 2)}
    1;}


inline_for_extraction
val scalarMultiplication_t: #c: curve -> #t:buftype -> #l: ladder -> p: point c -> result: point c -> 
  scalar: scalar_t #t #c ->
  tempBuffer: lbuffer uint64 (size 20 *! getCoordinateLenU64 c) ->
  Stack unit
  (requires fun h -> 
    live h p /\ live h result /\ live h scalar /\ live h tempBuffer /\
    scalar_as_nat (as_seq h scalar) < getOrder #c /\ 
    LowStar.Monotonic.Buffer.all_disjoint [loc p; loc tempBuffer; loc scalar; loc result] /\ point_eval c h p /\
    ~ (isPointAtInfinity #Jacobian (point_as_nat c h p)))
  (ensures fun h0 _ h1 -> modifies (loc p |+| loc result |+| loc tempBuffer) h0 h1 /\ point_eval c h1 result /\ (
    let p0 = point_as_nat c h0 p in 
    let qD = point_as_nat c h1 result in
    pointEqual qD (point_mult #c (scalar_as_nat #c (as_seq h0 scalar)) p0) /\ 
    (not (isPointAtInfinity #Jacobian (scalar_multiplication (as_seq h0 scalar) p0)) ==>
      qD == fromJacobianCoordinates #c (scalar_multiplication (as_seq h0 scalar) p0))))

let scalarMultiplication_t #c #t #l p result scalar tempBuffer  = 
    let h0 = ST.get() in 
  let len = getCoordinateLenU64 c in 
  scalar_multiplication_t_0 #c #t #l p result scalar tempBuffer; 
    let h1 = ST.get() in 
  let t = sub tempBuffer (size 0) (size 17 *! len) in 
  norm result result t; 
    norm_twice_lemma #c (fromDomainPoint #c #DH (point_as_nat c h1 result)) (point_mult #c (scalar_as_nat #c (as_seq h0 scalar)) (point_as_nat c h0 p))


inline_for_extraction noextract
let scalarMultiplicationL #c #l = scalarMultiplication_t #c #MUT #l
let scalarMultiplicationI #c #l = scalarMultiplication_t #c #IMMUT #l
inline_for_extraction noextract
let scalarMultiplicationC #c #l = scalarMultiplication_t #c #CONST #l


#push-options "--ifuel 1"

let scalarMultiplication #c #buf_type #l p result scalar tempBuffer = 
  match buf_type with 
  |MUT -> scalarMultiplicationL #c #l p result scalar tempBuffer
  |IMMUT -> scalarMultiplicationI #c #l p result scalar tempBuffer
  |CONST -> scalarMultiplicationC #c #l p result scalar tempBuffer

#pop-options 


[@CInline]
let scalarMultiplicationWithoutNorm_p256_ml = scalar_multiplication_t_0 #P256 #MUT #MontLadder
[@CInline]
let scalarMultiplicationWithoutNorm_p384_ml = scalar_multiplication_t_0 #P384 #MUT #MontLadder

[@CInline]
let scalarMultiplicationWithoutNorm_p256_radix = scalar_multiplication_t_0 #P256 #MUT #Radix
[@CInline]
let scalarMultiplicationWithoutNorm_p384_radix = scalar_multiplication_t_0 #P384 #MUT #Radix


let scalarMultiplicationWithoutNorm #c #l = 
  match c with 
  |P256 -> begin
    match l with 
    |MontLadder -> scalarMultiplicationWithoutNorm_p256_ml
    |Radix -> scalarMultiplicationWithoutNorm_p256_radix
  end
  |P384 -> 
    begin
      match l with 
      |MontLadder -> scalarMultiplicationWithoutNorm_p384_ml
      |Radix -> scalarMultiplicationWithoutNorm_p384_radix
    end


inline_for_extraction noextract
val uploadStartPointsS2P: #c: curve -> q: point c -> result: point c -> Stack unit 
  (requires fun h -> live h q /\ live h result /\ disjoint q result)
  (ensures fun h0 _ h1 -> modifies (loc result |+| loc q) h0 h1 /\
    point_eval c h1 q /\ point_eval c h1 result /\ (
    let pD = fromDomainPoint #c #DH (point_as_nat c h1 q) in 
    let qD = fromDomainPoint #c #DH (point_as_nat c h1 result) in 
    qD == basePoint #c /\ isPointAtInfinity pD /\ 
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


let secretToPublic #c #l result scalar tempBuffer = 
  let h0 = ST.get() in 
  let len = getCoordinateLenU64 c in 
  let q = sub tempBuffer (size 0) (size 3 *! len) in
  let buff = sub tempBuffer (size 3 *! len) (size 17 *! len) in 
  match l with 
  |MontLadder -> 
    begin
      admit(); 
      uploadStartPointsS2P q result; 
      montgomery_ladder q result scalar buff;
	let h1 = ST.get() in 
      norm q result buff;
      norm_twice_lemma #c (fromDomainPoint #c #DH (point_as_nat c h1 q)) (point_mult #c (scalar_as_nat #c (as_seq h0 scalar)) (basePoint #c))
    end
  |Radix  -> 
    begin
      secret_to_public_radix q scalar buff;
	let h1 = ST.get() in 
      norm q result buff;
	let h2 = ST.get() in 
      norm_twice_lemma #c (fromDomainPoint #c #DH (point_as_nat c h1 q)) (point_mult #c (scalar_as_nat #c (as_seq h0 scalar)) (basePoint #c))

    end


inline_for_extraction noextract
val secretToPublicWithoutNorm_: #c: curve -> #l: ladder -> result: point c 
  -> scalar: scalar_t #MUT #c
  -> tempBuffer: lbuffer uint64 (size 20 *! getCoordinateLenU64 c) ->
  Stack unit (requires fun h -> live h result /\ live h scalar /\ live h tempBuffer /\ 
    LowStar.Monotonic.Buffer.all_disjoint [loc tempBuffer; loc scalar; loc result] /\ 
    scalar_as_nat (as_seq h scalar) < getOrder #c)
  (ensures fun h0 _ h1 -> point_eval c h1 result /\ modifies (loc result |+| loc tempBuffer) h0 h1 /\ (
    let p0 = basePoint #c in 
    let qD = fromDomainPoint #c #DH (point_as_nat c h1 result) in
    pointEqual #c qD (point_mult #c (scalar_as_nat #c (as_seq h0 scalar)) p0)))

let secretToPublicWithoutNorm_ #c #l result scalar tempBuffer = 
  let h0 = ST.get() in 
  let len = getCoordinateLenU64 c in 
  let q = sub tempBuffer (size 0) (size 3 *! len) in
  let buff = sub tempBuffer (size 3 *! len) (size 17 *! len) in 
  match l with 
  |MontLadder -> 
    begin
      uploadStartPointsS2P q result; 
      montgomery_ladder q result scalar buff;
      copy_point q result
    end
  |Radix  -> 
    begin
      secret_to_public_radix result scalar buff
    end


[@CInline]
let secretToPublicWithoutNorm_p256_ml = secretToPublicWithoutNorm_ #P256 #MontLadder
[@CInline]
let secretToPublicWithoutNorm_p384_ml = secretToPublicWithoutNorm_ #P384 #MontLadder
[@CInline]
let secretToPublicWithoutNorm_p256_radix = secretToPublicWithoutNorm_ #P256 #Radix
[@CInline]
let secretToPublicWithoutNorm_p384_radix = secretToPublicWithoutNorm_ #P384 #Radix


let secretToPublicWithoutNorm #c #l = 
  match c with 
  |P256 -> begin
    match l with 
    |MontLadder -> secretToPublicWithoutNorm_p256_ml
    |Radix -> secretToPublicWithoutNorm_p256_radix
  end
  |P384 -> 
    begin
      match l with 
      |MontLadder -> secretToPublicWithoutNorm_p384_ml
      |Radix -> secretToPublicWithoutNorm_p384_radix
    end
