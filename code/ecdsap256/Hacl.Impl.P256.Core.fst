module Hacl.Impl.P256.Core 

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Hacl.Impl.P256.Arithmetics

open Lib.Buffer

open Spec.P256.Lemmas
open Spec.P256.Definitions
open Spec.P256.MontgomeryMultiplication
open Spec.P256.MontgomeryMultiplication.PointAdd
open Spec.P256
open Hacl.Impl.SolinasReduction
open Hacl.Impl.P256.LowLevel 
open Hacl.Impl.P256.LowLevel.PrimeSpecific
open Hacl.Impl.P256.MontgomeryMultiplication
open Hacl.Impl.ScalarMultiplication.WNAF
open Hacl.Impl.P256.Math 

open Hacl.Impl.P256.PointAdd
open Hacl.Impl.P256.PointDouble

open FStar.Tactics 
open FStar.Tactics.Canon

open FStar.Math.Lemmas

open Hacl.Impl.P256.Q.PrimitivesMasking

friend Spec.P256.MontgomeryMultiplication
open FStar.Mul


val swap: p: point_prime -> q: point_prime -> Tot (r: tuple2 point_prime point_prime {let pNew, qNew = r in 
  pNew == q /\ qNew == p})

let swap p q = (q, p)


val conditional_swap: i: uint64 -> p: point_prime -> q: point_prime -> Tot (r: tuple2 point_prime point_prime
  {
    let pNew, qNew = r in 
    if uint_v i = 0 then pNew == p /\ qNew == q
    else
      let p1, q1 = swap p q in 
      p1 == pNew /\ q1 == qNew
 }
)

let conditional_swap i p q = 
  if uint_v i = 0 then 
    (p, q)
  else
    (q, p)


#set-options "--z3rlimit 150 --max_fuel 0 --max_ifuel 0" 
let toDomain value result = 
  push_frame();
    let multBuffer = create (size 8) (u64 0) in 
    shift_256_impl value multBuffer;
    solinas_reduction_impl multBuffer result;
  pop_frame()  


let fromDomain f result = 
  montgomery_multiplication_buffer_by_one f result  

let pointToDomain p result = 
    let p_x = sub p (size 0) (size 4) in 
    let p_y = sub p (size 4) (size 4) in 
    let p_z = sub p (size 8) (size 4) in 
    
    let r_x = sub result (size 0) (size 4) in 
    let r_y = sub result (size 4) (size 4) in 
    let r_z = sub result (size 8) (size 4) in 

    toDomain p_x r_x;
    toDomain p_y r_y;

    upd result (size 8) (u64 1);
    upd result (size 9) (u64 18446744069414584320);
    upd result (size 10) (u64 18446744073709551615);
    upd result (size 11) (u64 4294967294)
    

let pointFromDomain p result = 
    let p_x = sub p (size 0) (size 4) in 
    let p_y = sub p (size 4) (size 4) in 
    let p_z = sub p (size 8) (size 4) in 

    let r_x = sub result (size 0) (size 4) in 
    let r_y = sub result (size 4) (size 4) in 
    let r_z = sub result (size 8) (size 4) in 

    fromDomain p_x r_x;
    fromDomain p_y r_y;
    fromDomain p_z r_z

inline_for_extraction noextract
val copy_point: p: point -> result: point -> Stack unit 
  (requires fun h -> live h p /\ live h result /\ disjoint p result) 
  (ensures fun h0 _ h1 -> modifies (loc result) h0 h1 /\ as_seq h1 result == as_seq h0 p)

let copy_point p result = copy result p
 

(* https://crypto.stackexchange.com/questions/43869/point-at-infinity-and-error-handling*)
val lemma_pointAtInfInDomain: x: nat -> y: nat -> z: nat {z < prime256} -> 
  Lemma (isPointAtInfinity (x, y, z) == isPointAtInfinity ((fromDomain_ x), (fromDomain_ y), (fromDomain_ z)))

let lemma_pointAtInfInDomain x y z =
  assert (if isPointAtInfinity (x, y, z) then z == 0 else z <> 0);
  assert_norm (modp_inv2 (pow2 256) % prime256 <> 0);
  lemmaFromDomain z;
  assert (fromDomain_ z == (z * modp_inv2 (pow2 256) % prime256));
  assert_norm (0 * modp_inv2 (pow2 256) % prime256 == 0);
  lemma_multiplication_not_mod_prime z;
  assert (if z = 0 then z * modp_inv2 (pow2 256) % prime256 == 0
                   else fromDomain_ z <> 0)


let isPointAtInfinityPrivate p =  
  let h0 = ST.get() in
  let z0 = index p (size 8) in 
  let z1 = index p (size 9) in 
  let z2 = index p (size 10) in 
  let z3 = index p (size 11) in 
  let z0_zero = eq_mask z0 (u64 0) in 
  let z1_zero = eq_mask z1 (u64 0) in 
  let z2_zero = eq_mask z2 (u64 0) in 
  let z3_zero = eq_mask z3 (u64 0) in 
     eq_mask_lemma z0 (u64 0);
     eq_mask_lemma z1 (u64 0);
     eq_mask_lemma z2 (u64 0);
     eq_mask_lemma z3 (u64 0);   
  let r = logand(logand z0_zero z1_zero) (logand z2_zero z3_zero) in 
    lemma_pointAtInfInDomain (as_nat h0 (gsub p (size 0) (size 4))) (as_nat h0 (gsub p (size 4) (size 4))) (as_nat h0 (gsub p (size 8) (size 4)));
  r


val lemma_norm_as_specification: xD: nat{xD < prime256} -> yD: nat{yD < prime256} -> 
  zD: nat {zD < prime256} -> 
  x3 : nat {x3 == xD * (pow (zD * zD) (prime - 2) % prime) % prime}-> 
  y3 : nat {y3 == yD * (pow (zD * zD * zD) (prime -2) % prime) % prime} -> 
  z3: nat {if isPointAtInfinity(xD, yD, zD) then z3 == 0 else z3 == 1} -> 
  Lemma (
  let (xN, yN, zN) = _norm (xD, yD, zD) in 
  x3 == xN /\ y3 == yN /\ z3 == zN)


let lemma_norm_as_specification xD yD zD x3 y3 z3 = 
  power_distributivity (zD * zD * zD) (prime - 2) prime;
  power_distributivity (zD * zD) (prime -2) prime


[@ CInline]
val cswap: bit:uint64{v bit <= 1} -> p:point -> q:point
  -> Stack unit
    (requires fun h ->
      live h p /\ live h q /\ (disjoint p q \/ p == q) /\
           
      as_nat h (gsub p (size 0) (size 4)) < prime /\ 
      as_nat h (gsub p (size 4) (size 4)) < prime /\
      as_nat h (gsub p (size 8) (size 4)) < prime /\
       
      as_nat h (gsub q (size 0) (size 4)) < prime /\  
      as_nat h (gsub q (size 4) (size 4)) < prime /\
      as_nat h (gsub q (size 8) (size 4)) < prime
)
    (ensures  fun h0 _ h1 ->
      modifies (loc p |+| loc q) h0 h1 /\
      (let pBefore = as_seq h0 p in let qBefore = as_seq h0 q in 
  let pAfter = as_seq h1 p in let qAfter = as_seq h1 q in 
  let condP0, condP1 = conditional_swap bit pBefore qBefore  in 
  condP0 == pAfter /\ condP1 == qAfter) /\ 

      (v bit == 1 ==> as_seq h1 p == as_seq h0 q /\ as_seq h1 q == as_seq h0 p) /\
      (v bit == 0 ==> as_seq h1 p == as_seq h0 p /\ as_seq h1 q == as_seq h0 q))


let cswap bit p1 p2 =
  let open Lib.Sequence in 
  let h0 = ST.get () in
  let mask = u64 0 -. bit in

  [@ inline_let]
  let inv h1 (i:nat{i <= 12}) =
    (forall (k:nat{k < i}).
      if v bit = 1
      then (as_seq h1 p1).[k] == (as_seq h0 p2).[k] /\ (as_seq h1 p2).[k] == (as_seq h0 p1).[k]
      else (as_seq h1 p1).[k] == (as_seq h0 p1).[k] /\ (as_seq h1 p2).[k] == (as_seq h0 p2).[k]) /\
    (forall (k:nat{i <= k /\ k < 12}).
      (as_seq h1 p1).[k] == (as_seq h0 p1).[k] /\ (as_seq h1 p2).[k] == (as_seq h0 p2).[k]) /\
    modifies (loc p1 |+| loc p2) h0 h1 in
 
  Lib.Loops.for 0ul 12ul inv
    (fun i ->
      let dummy = mask &. (p1.(i) ^. p2.(i)) in
      p1.(i) <- p1.(i) ^. dummy;
      p2.(i) <- p2.(i) ^. dummy;
      lemma_cswap2_step bit ((as_seq h0 p1).[v i]) ((as_seq h0 p2).[v i])
    );
  let h1 = ST.get () in
  Lib.Sequence.eq_intro (as_seq h1 p1) (if v bit = 1 then as_seq h0 p2 else as_seq h0 p1);
  Lib.Sequence.eq_intro (as_seq h1 p2) (if v bit = 1 then as_seq h0 p1 else as_seq h0 p2)



inline_for_extraction noextract
val normalisation_update: z2x: felem -> z3y: felem ->p: point ->  resultPoint: point -> Stack unit 
  (requires fun h -> live h z2x /\ live h z3y /\ live h resultPoint /\ live h p /\ 
    as_nat h z2x < prime256 /\ as_nat h z3y < prime /\
    as_nat h (gsub p (size 8) (size 4)) < prime256 /\
    disjoint z2x z3y /\ disjoint z2x resultPoint /\ disjoint z3y resultPoint)
  (ensures fun h0 _ h1 -> modifies (loc resultPoint) h0 h1 /\
    (
      let x0 = as_nat h0 (gsub p (size 0) (size 4)) in 
      let y0 = as_nat h0 (gsub p (size 4) (size 4)) in 
      let z0 = as_nat h0 (gsub p (size 8) (size 4)) in 

      let x1 = as_nat h1 (gsub resultPoint (size 0) (size 4)) in 
      let y1 = as_nat h1 (gsub resultPoint (size 4) (size 4)) in 
      let z1 = as_nat h1 (gsub resultPoint (size 8) (size 4)) in 

      x1 == fromDomain_(as_nat h0 z2x) /\ y1 == fromDomain_(as_nat h0 z3y)  /\ 
      (
  if Spec.P256.isPointAtInfinity (fromDomain_ x0, fromDomain_ y0, fromDomain_ z0) then  z1 == 0 else z1 == 1
      ))
  )


let normalisation_update z2x z3y p resultPoint = 
  push_frame(); 
    let zeroBuffer = create (size 4) (u64 0) in 
    
  let resultX = sub resultPoint (size 0) (size 4) in 
  let resultY = sub resultPoint (size 4) (size 4) in 
  let resultZ = sub resultPoint (size 8) (size 4) in 
    let h0 = ST.get() in 
  let bit = isPointAtInfinityPrivate p in
  fromDomain z2x resultX;
  fromDomain z3y resultY;
  uploadOneImpl resultZ;
    let h1 = ST.get() in 
  copy_conditional resultZ zeroBuffer bit;
    let h2 = ST.get() in 
  pop_frame()
  

let norm p resultPoint tempBuffer = 
  let xf = sub p (size 0) (size 4) in 
  let yf = sub p (size 4) (size 4) in 
  let zf = sub p (size 8) (size 4) in 

  
  let z2f = sub tempBuffer (size 4) (size 4) in 
  let z3f = sub tempBuffer (size 8) (size 4) in
  let tempBuffer20 = sub tempBuffer (size 12) (size 32) in 

    let h0 = ST.get() in 
  montgomery_square_buffer zf z2f; 
    let h1 = ST.get() in 
  montgomery_multiplication_buffer z2f zf z3f;
    let h2 = ST.get() in 
      lemma_mod_mul_distr_l (fromDomain_ (as_nat h0 zf) * fromDomain_ (as_nat h0 zf)) (fromDomain_ (as_nat h0 zf)) prime256;
      assert (as_nat h1 z2f = toDomain_ (fromDomain_ (as_nat h0 zf) * fromDomain_ (as_nat h0 zf) % prime256));
      assert (as_nat h2 z3f = toDomain_ (fromDomain_ (as_nat h0 zf) * fromDomain_ (as_nat h0 zf) * fromDomain_ (as_nat h0 zf) % prime256));

  exponent z2f z2f tempBuffer20;
    let h3 = ST.get() in 
      assert(as_nat h3 z2f = toDomain_ (pow (fromDomain_ (as_nat h2 z2f)) (prime256 - 2) % prime256));
  exponent z3f z3f tempBuffer20;
    let h4 = ST.get() in 
      assert(as_nat h4 z3f = toDomain_ (pow (fromDomain_ (as_nat h3 z3f)) (prime256 - 2) % prime256));
     
  montgomery_multiplication_buffer xf z2f z2f;
  montgomery_multiplication_buffer yf z3f z3f;
  normalisation_update z2f z3f p resultPoint; 

    let h3 = ST.get() in 
    lemmaEraseToDomainFromDomain (fromDomain_ (as_nat h0 zf)); 
    power_distributivity (fromDomain_ (as_nat h0 zf) * fromDomain_ (as_nat h0 zf)) (prime -2) prime;
    power_distributivity (fromDomain_ (as_nat h0 zf) * fromDomain_ (as_nat h0 zf) * fromDomain_ (as_nat h0 zf)) (prime -2) prime;

    lemma_norm_as_specification (fromDomain_ (point_x_as_nat h0 p)) (fromDomain_ (point_y_as_nat h0 p)) (fromDomain_ (point_z_as_nat h0 p)) (point_x_as_nat h3 resultPoint) (point_y_as_nat h3 resultPoint) (point_z_as_nat h3 resultPoint);

    assert(
       let zD = fromDomain_(point_z_as_nat h0 p) in 
       let xD = fromDomain_(point_x_as_nat h0 p) in 
       let yD = fromDomain_(point_y_as_nat h0 p) in 
       let (xN, yN, zN) = _norm (xD, yD, zD) in 
       point_x_as_nat h3 resultPoint == xN /\ point_y_as_nat h3 resultPoint == yN /\ point_z_as_nat h3 resultPoint == zN)


let normX p result tempBuffer = 
  let xf = sub p (size 0) (size 4) in 
  let yf = sub p (size 4) (size 4) in 
  let zf = sub p (size 8) (size 4) in 

  
  let z2f = sub tempBuffer (size 4) (size 4) in 
  let z3f = sub tempBuffer (size 8) (size 4) in
  let tempBuffer20 = sub tempBuffer (size 12) (size 20) in 

    let h0 = ST.get() in 
  montgomery_square_buffer zf z2f; 
  exponent z2f z2f tempBuffer20;
  montgomery_multiplication_buffer z2f xf z2f;
  fromDomain z2f result;
  assert_norm (prime >= 2);
    power_distributivity (fromDomain_ (as_nat h0 zf) * fromDomain_ (as_nat h0 zf)) (prime -2) prime


(* this piece of code is taken from Hacl.Curve25519 *)
(* changed Endian for Scalar Bit access *)
inline_for_extraction noextract
val scalar_bit:
    #buf_type: buftype -> 
    s:lbuffer_t buf_type uint8 (size 32)
  -> n:size_t{v n < 256}
  -> Stack uint64
    (requires fun h0 -> live h0 s)
    (ensures  fun h0 r h1 -> h0 == h1 /\ r == ith_bit (as_seq h0 s) (v n) /\ v r <= 1)

let scalar_bit #buf_type s n =
  let h0 = ST.get () in
  mod_mask_lemma ((Lib.Sequence.index (as_seq h0 s) (31 - v n / 8)) >>. (n %. 8ul)) 1ul;
  assert_norm (1 = pow2 1 - 1);
  assert (v (mod_mask #U8 #SEC 1ul) == v (u8 1)); 
  to_u64 ((s.(31ul -. n /. 8ul) >>. (n %. 8ul)) &. u8 1)


inline_for_extraction noextract  
val montgomery_ladder_step1: p: point -> q: point ->tempBuffer: lbuffer uint64 (size 88) -> Stack unit
  (requires fun h -> live h p /\ live h q /\ live h tempBuffer /\ 
    LowStar.Monotonic.Buffer.all_disjoint [loc p; loc q; loc tempBuffer] /\

    as_nat h (gsub p (size 0) (size 4)) < prime /\ 
    as_nat h (gsub p (size 4) (size 4)) < prime /\
    as_nat h (gsub p (size 8) (size 4)) < prime /\
  
    as_nat h (gsub q (size 0) (size 4)) < prime /\  
    as_nat h (gsub q (size 4) (size 4)) < prime /\
    as_nat h (gsub q (size 8) (size 4)) < prime
  
  )
  (ensures fun h0 _ h1 -> modifies (loc p |+| loc q |+|  loc tempBuffer) h0 h1 /\ 
    (
      let pX = as_nat h0 (gsub p (size 0) (size 4)) in
      let pY = as_nat h0 (gsub p (size 4) (size 4)) in
      let pZ = as_nat h0 (gsub p (size 8) (size 4)) in

      let qX = as_nat h0 (gsub q (size 0) (size 4)) in
      let qY = as_nat h0 (gsub q (size 4) (size 4)) in
      let qZ = as_nat h0 (gsub q (size 8) (size 4)) in

      let r0X = as_nat h1 (gsub p (size 0) (size 4)) in
      let r0Y = as_nat h1 (gsub p (size 4) (size 4)) in
      let r0Z = as_nat h1 (gsub p (size 8) (size 4)) in

      let r1X = as_nat h1 (gsub q (size 0) (size 4)) in
      let r1Y = as_nat h1 (gsub q (size 4) (size 4)) in
      let r1Z = as_nat h1 (gsub q (size 8) (size 4)) in


      let (rN0X, rN0Y, rN0Z), (rN1X, rN1Y, rN1Z) = _ml_step1 (fromDomain_ pX, fromDomain_ pY, fromDomain_ pZ) (fromDomain_ qX, fromDomain_ qY, fromDomain_ qZ) in 
      
      fromDomain_ r0X == rN0X /\ fromDomain_ r0Y == rN0Y /\ fromDomain_ r0Z == rN0Z /\
      fromDomain_ r1X == rN1X /\ fromDomain_ r1Y == rN1Y /\ fromDomain_ r1Z == rN1Z /\ 

      r0X < prime /\ r0Y < prime /\ r0Z < prime /\
      r1X < prime /\ r1Y < prime /\ r1Z < prime
  ) 
)


let montgomery_ladder_step1 r0 r1 tempBuffer = 
  point_add r0 r1 r1 tempBuffer;
  point_double r0 r0 tempBuffer
      

val lemma_step: i: size_t {uint_v i < 256} -> Lemma  (uint_v ((size 255) -. i) == 255 - (uint_v i))
let lemma_step i = ()


inline_for_extraction noextract 
val montgomery_ladder_step: #buf_type: buftype-> 
  p: point -> q: point ->tempBuffer: lbuffer uint64 (size 88) -> 
  scalar: lbuffer_t buf_type uint8 (size 32) -> 
  i:size_t{v i < 256} -> 
  Stack unit
  (requires fun h -> live h p /\ live h q /\ live h tempBuffer /\ live h scalar /\
    LowStar.Monotonic.Buffer.all_disjoint [loc p; loc q; loc tempBuffer; loc scalar] /\
     
    as_nat h (gsub p (size 0) (size 4)) < prime /\ 
    as_nat h (gsub p (size 4) (size 4)) < prime /\
    as_nat h (gsub p (size 8) (size 4)) < prime /\
  
    as_nat h (gsub q (size 0) (size 4)) < prime /\  
    as_nat h (gsub q (size 4) (size 4)) < prime /\
    as_nat h (gsub q (size 8) (size 4)) < prime
  )
  (ensures fun h0 _ h1 -> modifies (loc p |+| loc q |+| loc tempBuffer) h0 h1 /\ 
    (
      
      let pX = as_nat h0 (gsub p (size 0) (size 4)) in
      let pY = as_nat h0 (gsub p (size 4) (size 4)) in
      let pZ = as_nat h0 (gsub p (size 8) (size 4)) in

      let qX = as_nat h0 (gsub q (size 0) (size 4)) in
      let qY = as_nat h0 (gsub q (size 4) (size 4)) in
      let qZ = as_nat h0 (gsub q (size 8) (size 4)) in

      let r0X = as_nat h1 (gsub p (size 0) (size 4)) in
      let r0Y = as_nat h1 (gsub p (size 4) (size 4)) in
      let r0Z = as_nat h1 (gsub p (size 8) (size 4)) in

      let r1X = as_nat h1 (gsub q (size 0) (size 4)) in
      let r1Y = as_nat h1 (gsub q (size 4) (size 4)) in
      let r1Z = as_nat h1 (gsub q (size 8) (size 4)) in

      let (rN0X, rN0Y, rN0Z), (rN1X, rN1Y, rN1Z) = _ml_step (as_seq h0 scalar) (uint_v i) ((fromDomain_ pX, fromDomain_ pY, fromDomain_ pZ), (fromDomain_ qX, fromDomain_ qY, fromDomain_ qZ)) in 
      
      fromDomain_ r0X == rN0X /\ fromDomain_ r0Y == rN0Y /\ fromDomain_ r0Z == rN0Z /\
      fromDomain_ r1X == rN1X /\ fromDomain_ r1Y == rN1Y /\ fromDomain_ r1Z == rN1Z /\ 

      r0X < prime /\ r0Y < prime /\ r0Z < prime /\
      r1X < prime /\ r1Y < prime /\ r1Z < prime
    ) 
  )


let montgomery_ladder_step #buf_type r0 r1 tempBuffer scalar i = 
  let bit0 = (size 255) -. i in 
  let bit = scalar_bit scalar bit0 in 
  cswap bit r0 r1; 
  montgomery_ladder_step1 r0 r1 tempBuffer; 
  cswap bit r0 r1; 
    lemma_step i




inline_for_extraction noextract
val montgomery_ladder: #buf_type: buftype->  p: point -> q: point ->
  scalar: lbuffer_t buf_type uint8 (size 32) -> 
  tempBuffer:  lbuffer uint64 (size 88)  -> 
  Stack unit
  (requires fun h -> live h p /\ live h q /\ live h scalar /\  live h tempBuffer /\
    LowStar.Monotonic.Buffer.all_disjoint [loc p; loc q; loc tempBuffer; loc scalar] /\
    as_nat h (gsub p (size 0) (size 4)) < prime /\ 
    as_nat h (gsub p (size 4) (size 4)) < prime /\
    as_nat h (gsub p (size 8) (size 4)) < prime /\
  
    as_nat h (gsub q (size 0) (size 4)) < prime /\  
    as_nat h (gsub q (size 4) (size 4)) < prime /\
    as_nat h (gsub q (size 8) (size 4)) < prime )
  (ensures fun h0 _ h1 -> modifies (loc p |+| loc q |+| loc tempBuffer) h0 h1 /\
    (
      as_nat h1 (gsub p (size 0) (size 4)) < prime /\ 
      as_nat h1 (gsub p (size 4) (size 4)) < prime /\
      as_nat h1 (gsub p (size 8) (size 4)) < prime /\
  
      as_nat h1 (gsub q (size 0) (size 4)) < prime /\  
      as_nat h1 (gsub q (size 4) (size 4)) < prime /\
      as_nat h1 (gsub q (size 8) (size 4)) < prime /\


      (
  let p1 = fromDomainPoint(point_prime_to_coordinates (as_seq h1 p)) in 
  let q1 = fromDomainPoint(point_prime_to_coordinates (as_seq h1 q)) in 
  let rN, qN = montgomery_ladder_spec (as_seq h0 scalar) 
    (
      fromDomainPoint(point_prime_to_coordinates (as_seq h0 p)),  
      fromDomainPoint(point_prime_to_coordinates (as_seq h0 q))
    ) in 
  rN == p1 /\ qN == q1
      )
   )
 )

let montgomery_ladder #a p q scalar tempBuffer =  
  let h0 = ST.get() in 


  [@inline_let]
  let spec_ml h0 = _ml_step (as_seq h0 scalar) in 

  [@inline_let] 
  let acc (h:mem) : GTot (tuple2 point_nat_prime point_nat_prime) = 
  (fromDomainPoint(point_prime_to_coordinates (as_seq h p)), fromDomainPoint(point_prime_to_coordinates (as_seq h q)))  in 
  
  Lib.LoopCombinators.eq_repeati0 256 (spec_ml h0) (acc h0);
  [@inline_let]
  let inv h (i: nat {i <= 256}) = 
    as_nat h (gsub p (size 0) (size 4)) < prime /\ 
    as_nat h (gsub p (size 4) (size 4)) < prime /\
    as_nat h (gsub p (size 8) (size 4)) < prime /\
  
    as_nat h (gsub q (size 0) (size 4)) < prime /\  
    as_nat h (gsub q (size 4) (size 4)) < prime /\
    as_nat h (gsub q (size 8) (size 4)) < prime /\
    modifies3 p q tempBuffer h0 h   /\
    acc h == Lib.LoopCombinators.repeati i (spec_ml h0) (acc h0)

    in 

  for 0ul 256ul inv 
    (fun i -> let h2 = ST.get() in
      montgomery_ladder_step p q tempBuffer scalar i; 
      Lib.LoopCombinators.unfold_repeati 256 (spec_ml h0) (acc h0) (uint_v i)
    )

(* prime = 2**256 - 2**224 + 2**192 + 2**96 -1

def norm(p):    
    x, y, z = p
    z2i = power_mod(z * z, -1, prime)
    z3i = power_mod(z * z * z, -1, prime)
    return ((x * z2i) % prime, (y * z3i) % prime, 1)

def toD(x):
    return x * power_mod (2 ** 256, 1, prime) % prime

def fromD(x):
    return x * power_mod (2 ** 256, prime - 2, prime) % prime

def toFakeAffine(p):
    x, y = p 
    multiplier = power_mod (2 ** 256, prime - 2, prime) 
    x = x * multiplier * multiplier % prime
    y = y * multiplier * multiplier * multiplier % prime
    return (x, y)

p256 = 0xFFFFFFFF00000001000000000000000000000000FFFFFFFFFFFFFFFFFFFFFFFF
a256 = p256 - 3
b256 = 0x5AC635D8AA3A93E7B3EBBD55769886BC651D06B0CC53B0F63BCE3C3E27D2604B
gx = 0x6B17D1F2E12C4247F8BCE6E563A440F277037D812DEB33A0F4A13945D898C296
gy = 0x4FE342E2FE1A7F9B8EE7EB4A7C0F9E162BCE33576B315ECECBB6406837BF51F5
qq = 0xFFFFFFFF00000000FFFFFFFFFFFFFFFFBCE6FAADA7179E84F3B9CAC2FC632551
FF = GF(p256)

EC = EllipticCurve([FF(a256), FF(b256)])

EC.set_order(qq)

G = EC(FF(gx), FF(gy))

def printf(p):
    x, y = p 
    for i in range(4):
        print("u64 " + str(hex((Integer(x) >> (i * 64)) % 2 ** 64)) + "; ")
    for i in range(4):
        print("u64 " + str (hex((Integer(y) >> (i * 64)) % 2 ** 64)) + "; ")
    

for i in range(16):
    pxD = i * G.xy()[0]
    pyD = i * G.xy()[1]
    printf (toFakeAffine((to D (pxD), toD (pyD))))

 *)

inline_for_extraction noextract
let points_radix_16_list : x:list uint64{List.Tot.length x == 128} =
  let open FStar.Mul in 
  [@inline_let]
  let x = [ 
    u64 0x0; u64 0x0; u64 0x0; u64 0x0; 
    u64 0x0; u64 0x0; u64 0x0; u64 0x0; 

    u64 0x1fb38ab1388ad777; u64 0x1dfee06615fa309d; u64 0xfcac986c3afea4a7; u64 0xdf65c2da29fb821a; 
    u64 0xeff44e23f63f8f6d; u64 0xaa02cd3ed4b681a4; u64 0xdd5fda3363818af8; u64 0xfc53bc2629fbf0b3; 

    u64 0x12631d721b91beea; u64 0x5f73f2d3a11a09f8; u64 0xac41f54484d5fcd8; u64 0x86578e5c56025df4; 
    u64 0x577c956b15ed6b5a; u64 0xb59c5f77982d848; u64 0xb7c5e2c190fcdcc2; u64 0x7d64d13ef1c91ffd; 

    u64 0xd40c2d6273f9d9f1; u64 0x4dc6f628063ef17c; u64 0x498e81df7ab17aa5; u64 0xabb2a5026f17173c; 
    u64 0x4a3d7527f6739ef3; u64 0xd941003268184c91; u64 0xd2d458b8d401508b; u64 0xb7437ab810ac5451; 

    u64 0x5256d9bdab491252; u64 0x972d326eb1084c12; u64 0xc3e96455e2ec3bfa; u64 0xb75c723b549a10ff; 
    u64 0x9d9185f9f8a18961; u64 0x2200a07b8589ba82; u64 0x637b9d96fd4e9f5e; u64 0xce75bfb2575e6cfa; 

    u64 0x7dd4477db8b77c7d; u64 0x80818a776e5503b0; u64 0x6fc7d58fb59581d; u64 0xd899fb87efe43022; 
    u64 0x23b9912111694135; u64 0x7e5de7bac33fa1c8; u64 0xb3b83722a70e7d43; u64 0xf06cfecbfb9bb38f; 

    u64 0xaa39277dfa93656; u64 0x3dabb6cce67c5201; u64 0x473ffb8bf1f94677; u64 0xb9f0b93637453e56; 
    u64 0x8fce12ec20958fb2; u64 0xcc16d74ff7786061; u64 0x3678438a8235d096; u64 0xe39ea044f06b43f6; 

    u64 0xbb40bdb5775c9950; u64 0xd244a74cdc703cdd; u64 0x83dc1b8a6105dd53; u64 0x38d9d50d49ef0437; 
    u64 0x58be44eba6096472; u64 0x960afaec386fa5c5; u64 0x1440032e000134b9; u64 0x601e721454d6ba96; 

    u64 0x79ec42228671b9b6; u64 0xfdc00dc48df9e25c; u64 0x44500833d71d2e77; u64 0x2bda4c3c0bc103d5; 
    u64 0x51528408aa925d53; u64 0xefcb55b9c2f3a37d; u64 0x9f28f6bb9846c915; u64 0xe1547ce1d8340e55; 

    u64 0x97e310c1995b3ed2; u64 0xed861937196256e6; u64 0x1c6762abff2c65f2; u64 0x268345e0978fcedd; 
    u64 0x35ca2e572b784881; u64 0x28ac888da0acd1b7; u64 0x305640dc06a41baf; u64 0x997c6fd2cb671bfb; 

    u64 0xf40d9eaf4a31e15a; u64 0x8991dd7d54cfe03a; u64 0x4889a3463a8deb0c; u64 0x4cbf48092cd0a1fa; 
    u64 0xc6965c4fbe18fb8c; u64 0x1d499d0cb216fa84; u64 0x8d5fe52c705dd3eb; u64 0x812b268f84313b34; 

    u64 0x313b58808261591a; u64 0xc2c322508f53d933; u64 0xa49ef3f95094ed1b; u64 0x13e326786e98c63; 
    u64 0x34be8167cd460429; u64 0x698a328099a6b31; u64 0xb9be3ba51b0c922d; u64 0xe59cca03f7674ed; 
    
    u64 0x4fbf7e505d3aca7c; u64 0x2f4f8ba62020715; u64 0x840502262ac1ec42; u64 0xb8e0532775197de7; 
    u64 0x9142a358cf4e9b4b; u64 0xc86a3c567e5d8626; u64 0xd4051282b4a7992a; u64 0xe7573c5999e3974e;
    
    u64 0xd814a606da7bd76b; u64 0x15604730f38cb788; u64 0xbd195f868fbdd6c4; u64 0xdb96f5b00a51d3f7; 
    u64 0xe1385c8a9b507fea; u64 0x878e27813ee7310; u64 0x6d7d8b12aea7e096; u64 0x54978ad11e2f5cca; 
    
    u64 0x49fffd6c3c4d07d4; u64 0x703638f71fab7a5d; u64 0xbed6e367fcc73960; u64 0x215e161835a61d75; 
    u64 0xe52288a5e87a660b; u64 0xf1d127ee3c802cb5; u64 0xccde3c6aafc46044; u64 0xdc11c08ef14cff32; 

    u64 0x29216f9ceca46668; u64 0x22e584a3b2891c5e; u64 0xe6deecd7810f6d87; u64 0x6aff4b94a55659a3; 
   u64 0x12b59bb6d2e9f876; u64 0x27ed01943aa02eab; u64 0x8d6d420841f57075; u64 0xe7b47285ef60a461;  
  ] in x




inline_for_extraction
let points_radix_16 : x: glbuffer uint64 128ul {witnessed #uint64 #(size 128) x (Lib.Sequence.of_list points_radix_16_list) /\ recallable x} =
    createL_global points_radix_16_list



let getScalar #a scalar i = 
  push_frame(); 

  let word = 
    (* let half = logand i 0xful in  *)
    let half = shift_right i 1ul in 
  to_u32(index scalar half) in 

  let open Hacl.Impl.P256.Q.PrimitivesMasking in 
  let bitShift = logand i (u32 1) in 

  let mask = to_u32 (cmovznz01  0xf0 0x0f  bitShift) in  
  let shiftMask = to_u32 (cmovznz01  0x4 0x0 bitShift) in

  let result = logand word mask in 
  let result = shift_right result shiftMask in 
 
  pop_frame();
  result
  


let montgomery_ladder_step_radix_precomputed p tempBuffer scalar i =  
  let bits: uint32 = getScalar scalar (i) in 

  let pointToAdd = sub points_radix_16 (bits *. size 8) (size 8) in 
  
  point_double p p tempBuffer;
  point_double p p tempBuffer;
  point_double p p tempBuffer;
  point_double p p tempBuffer;

  
  Hacl.Impl.P256.MixedPointAdd.point_add_mixed p pointToAdd p tempBuffer


let montgomery_ladder_step_radix p tempBuffer precomputedTable scalar i =  
  let bits = getScalar scalar i in 

  let pointToAdd = sub precomputedTable (bits *. size 12) (size 12) in 
  
  point_double p p tempBuffer;
  point_double p p tempBuffer;
  point_double p p tempBuffer;
  point_double p p tempBuffer;

  point_add pointToAdd p p tempBuffer



inline_for_extraction noextract
val montgomery_ladder_2_precomputed: #buf_type: buftype -> p: point -> 
  scalar: lbuffer_t buf_type uint8 (size 32) -> 
  tempBuffer:  lbuffer uint64 (size 88)  -> 
  Stack unit
  (requires fun h -> True )
  (ensures fun h0 _ h1 -> modifies (loc p |+| loc tempBuffer) h0 h1)

let montgomery_ladder_2_precomputed #a p scalar tempBuffer =  
 let h0 = ST.get() in 




  [@inline_let]
  let spec_ml h0 = _ml_step (as_seq h0 scalar) in 

  [@inline_let] 
  let acc (h:mem) : GTot (point_nat_prime) = (fromDomainPoint(point_prime_to_coordinates (as_seq h p)))  in 

  [@inline_let]
  let inv h (i: nat {i <= 64}) = True in 

 
  let bits: uint32 = getScalar scalar 0 in 
  let pointToStart = sub points_radix_16 (bits *. size 8) (size 8) in 
  let pointToStart = const_to_lbuffer pointToStart in 

  copy (sub p (size 0) (size 8)) pointToStart;

  upd p (size 8) (u64 1);
  upd p (size 9) (u64 0);
  upd p (size 10) (u64 0);
  upd p (size 11) (u64 0);


  for 1ul 64ul inv 
    (fun i -> let h2 = ST.get() in
      montgomery_ladder_step_radix_precomputed p tempBuffer scalar i
    )

inline_for_extraction noextract
val uploadZeroPoint: p: point -> Stack unit 
  (requires fun h -> True)
  (ensures fun h0 _ h1 -> True)

let uploadZeroPoint p = 
  uploadZeroImpl (sub p (size 0) (size 4));
  uploadZeroImpl (sub p (size 4) (size 4));
  uploadZeroImpl (sub p (size 8) (size 4))


[@ CInline]
val generatePrecomputedTable: b: lbuffer uint64 (size 192) -> publicKey: point ->
  tempBuffer: lbuffer uint64 (size 88) -> Stack unit  
  (requires fun h -> True)
  (ensures fun h0 _ h1 -> True)

let generatePrecomputedTable b publicKey tempBuffer = 
  let point0 = sub b (size 0) (size 12) in 
  let point1 = sub b (size 12) (size 12) in 
  let point2 = sub b (size 24) (size 12) in 
  let point3 = sub b (size 36) (size 12) in 
  let point4 = sub b (size 48) (size 12) in 
  let point5 = sub b (size 60) (size 12) in 
  let point6 = sub b (size 72) (size 12) in 
  let point7 = sub b (size 84) (size 12) in 
  let point8 = sub b (size 96) (size 12) in 
  let point9 = sub b (size 108) (size 12) in 
  let point10 = sub b (size 120) (size 12) in 
  let point11 = sub b (size 132) (size 12) in 
  let point12 = sub b (size 144) (size 12) in 
  let point13 = sub b (size 156) (size 12) in 
  let point14 = sub b (size 168) (size 12) in 
  let point15 = sub b (size 180) (size 12) in 

  uploadZeroPoint point0;
  copy_point publicKey point1;
  point_double publicKey point2 tempBuffer;
  point_add point2 point1 point3 tempBuffer;
  point_double point2 point4 tempBuffer;
  point_add point4 point1 point5 tempBuffer;
  point_double point3 point6 tempBuffer;
  point_add point6 point1 point7 tempBuffer;
  point_double point4 point8 tempBuffer;
  point_add point8 point1 point9 tempBuffer;
  point_double point5 point10 tempBuffer;
  point_add point10 point1 point11 tempBuffer;
  point_double point6 point12 tempBuffer;
  point_add point12 point1 point13 tempBuffer;
  point_double point7 point14 tempBuffer;
  point_add point14 point1 point15 tempBuffer



inline_for_extraction noextract
val montgomery_ladder_2: #buf_type: buftype -> p: point -> 
  scalar: lbuffer_t buf_type uint8 (size 32) -> 
  tempBuffer:  lbuffer uint64 (size 88)  -> 
  precomputedTable: lbuffer uint64 (size 192) ->
  Stack unit
  (requires fun h -> True )
  (ensures fun h0 _ h1 -> modifies (loc p |+| loc tempBuffer) h0 h1)

let montgomery_ladder_2 #a p scalar tempBuffer precomputedTable =  
 let h0 = ST.get() in 
   push_frame();

     [@inline_let]
     let spec_ml h0 = _ml_step (as_seq h0 scalar) in 

     [@inline_let] 
     let acc (h:mem) : GTot (point_nat_prime) = (fromDomainPoint(point_prime_to_coordinates (as_seq h p)))  in 

     [@inline_let]
     let inv h (i: nat {i <= 64}) = True in 

     for 0ul 64ul inv 
       (fun i -> let h2 = ST.get() in
	 montgomery_ladder_step_radix p tempBuffer precomputedTable scalar i
       );
   pop_frame()




inline_for_extraction noextract
val zero_buffer: p: point -> 
  Stack unit
    (requires fun h -> live h p)
    (ensures fun h0 _ h1 ->     
      modifies (loc p) h0 h1 /\
      (
  let k = Lib.Sequence.create 12 (u64 0) in 
  as_nat h1 (gsub p (size 0) (size 4)) == 0 /\ 
  as_nat h1 (gsub p (size 4) (size 4)) == 0 /\
  as_nat h1 (gsub p (size 8) (size 4)) == 0 
    )
  )

let zero_buffer p = 
  upd p (size 0) (u64 0);
  upd p (size 1) (u64 0);
  upd p (size 2) (u64 0);
  upd p (size 3) (u64 0);
  upd p (size 4) (u64 0);
  upd p (size 5) (u64 0);
  upd p (size 6) (u64 0);
  upd p (size 7) (u64 0);
  upd p (size 8) (u64 0);
  upd p (size 9) (u64 0);
  upd p (size 10) (u64 0);
  upd p (size 11) (u64 0)


val lemma_point_to_domain: h0: mem -> h1: mem ->  p: point -> result: point ->  Lemma
   (requires (point_x_as_nat h0 p < prime /\ point_y_as_nat h0 p < prime /\ point_z_as_nat h0 p < prime /\
       point_x_as_nat h1 result == toDomain_ (point_x_as_nat h0 p) /\
       point_y_as_nat h1 result == toDomain_ (point_y_as_nat h0 p) /\
       point_z_as_nat h1 result == toDomain_ (point_z_as_nat h0 p) 
     )
   )
   (ensures (fromDomainPoint(point_prime_to_coordinates (as_seq h1 result)) == point_prime_to_coordinates (as_seq h0 p)))

let lemma_point_to_domain h0 h1 p result = 
  let (x, y, z) = point_prime_to_coordinates (as_seq h1 result) in ()


val lemma_pif_to_domain: h: mem ->  p: point -> Lemma
  (requires (point_x_as_nat h p == 0 /\ point_y_as_nat h p == 0 /\ point_z_as_nat h p == 0))
  (ensures (fromDomainPoint (point_prime_to_coordinates (as_seq h p)) == point_prime_to_coordinates (as_seq h p)))

let lemma_pif_to_domain h p = 
  let (x, y, z) = point_prime_to_coordinates (as_seq h p) in 
  let (x3, y3, z3) = fromDomainPoint (x, y, z) in 
  lemmaFromDomain x;
  lemmaFromDomain y;
  lemmaFromDomain z;
  lemma_multiplication_not_mod_prime x; 
  lemma_multiplication_not_mod_prime y;
  lemma_multiplication_not_mod_prime z


val lemma_coord: h3: mem -> q: point -> Lemma (
   let (r0, r1, r2) = fromDomainPoint(point_prime_to_coordinates (as_seq h3 q)) in 
  let xD = fromDomain_ (point_x_as_nat h3 q) in 
  let yD = fromDomain_ (point_y_as_nat h3 q) in 
  let zD = fromDomain_ (point_z_as_nat h3 q) in 
    r0 == xD /\ r1 == yD /\ r2 == zD) 

let lemma_coord h3 q = ()


inline_for_extraction
val scalarMultiplication_t: #t:buftype ->
  m: montgomery_ladder_mode ->

   p: point -> result: point -> 
  scalar: lbuffer_t t uint8 (size 32) -> 
  tempBuffer: lbuffer uint64 (size 100) ->
  Stack unit
    (requires fun h -> 
      live h p /\ live h result /\ live h scalar /\ live h tempBuffer /\
    LowStar.Monotonic.Buffer.all_disjoint [loc p; loc tempBuffer; loc scalar; loc result] /\
    as_nat h (gsub p (size 0) (size 4)) < prime /\ 
    as_nat h (gsub p (size 4) (size 4)) < prime /\
    as_nat h (gsub p (size 8) (size 4)) < prime
    )
  (ensures fun h0 _ h1 -> 
    modifies (loc p |+| loc result |+| loc tempBuffer) h0 h1 /\ 
    
    as_nat h1 (gsub result (size 0) (size 4)) < prime256 /\ 
    as_nat h1 (gsub result (size 4) (size 4)) < prime256 /\
    as_nat h1 (gsub result (size 8) (size 4)) < prime256 /\
    
    modifies (loc p |+| loc result |+| loc tempBuffer) h0 h1 /\
    (
      let x3, y3, z3 = point_x_as_nat h1 result, point_y_as_nat h1 result, point_z_as_nat h1 result in 
      let (xN, yN, zN) = scalar_multiplication (as_seq h0 scalar) (point_prime_to_coordinates (as_seq h0 p)) in 
      x3 == xN /\ y3 == yN /\ z3 == zN 
  )
) 


let scalarMultiplication_t #t m p result scalar tempBuffer  = 
(*
    let h0 = ST.get() in 
  let q = sub tempBuffer (size 0) (size 12) in 
  zero_buffer q;
  let buff = sub tempBuffer (size 12) (size 88) in 
  pointToDomain p result;
    let h2 = ST.get() in 
  montgomery_ladder q result scalar buff;
    let h3 = ST.get() in 
    lemma_point_to_domain h0 h2 p result;
    lemma_pif_to_domain h2 q;
  norm q result buff; 
    lemma_coord h3 q *)



    let h0 = ST.get() in 
  let q = sub tempBuffer (size 0) (size 12) in 
  (* zero_buffer q; *)
  let buff = sub tempBuffer (size 12) (size 88) in 
  pointToDomain p result;
    let h2 = ST.get() in 

    begin
  match m with 
  |Ladder ->
     let bufferPrecomputed = create (size 192) (u64 0) in 
     generatePrecomputedTable bufferPrecomputed result buff;
     montgomery_ladder_2 q scalar buff bufferPrecomputed
  |Radix4 ->
      montgomery_ladder q result scalar buff
  |Comb ->
      montgomery_ladder q result scalar buff
  end;

    let h3 = ST.get() in 
    lemma_point_to_domain h0 h2 p result;
    lemma_pif_to_domain h2 q;
  norm q result buff; 
    lemma_coord h3 q





let scalarMultiplicationL = scalarMultiplication_t #MUT

let scalarMultiplicationI = scalarMultiplication_t #IMMUT
let scalarMultiplicationC = scalarMultiplication_t #CONST

let scalarMultiplication #buf_type m p result scalar tempBuffer = 
  match buf_type with 
  |MUT -> scalarMultiplicationL m p result scalar tempBuffer 
  |IMMUT -> scalarMultiplicationI m p result scalar tempBuffer
  |CONST -> scalarMultiplicationC m p result scalar tempBuffer


inline_for_extraction noextract
val uploadBasePoint: p: point -> Stack unit 
  (requires fun h -> live h p)
  (ensures fun h0 _ h1 -> modifies (loc p) h0 h1 /\ 
    as_nat h1 (gsub p (size 0) (size 4)) < prime256 /\ 
    as_nat h1 (gsub p (size 4) (size 4)) < prime256 /\
    as_nat h1 (gsub p (size 8) (size 4)) < prime256 /\
      (
  let x1 = as_nat h1 (gsub p (size 0) (size 4)) in 
  let y1 = as_nat h1 (gsub p (size 4) (size 4)) in 
  let z1 = as_nat h1 (gsub p (size 8) (size 4)) in 

  let bpX = 0x6B17D1F2E12C4247F8BCE6E563A440F277037D812DEB33A0F4A13945D898C296 in 
  let bpY = 0x4FE342E2FE1A7F9B8EE7EB4A7C0F9E162BCE33576B315ECECBB6406837BF51F5 in 

  fromDomain_ x1 == bpX /\ fromDomain_ y1 == bpY /\ fromDomain_ z1 ==  1
    )
)

let uploadBasePoint p = 
    let h0 = ST.get() in 
  upd p (size 0) (u64 8784043285714375740);
  upd p (size 1) (u64 8483257759279461889);
  upd p (size 2) (u64 8789745728267363600);
  upd p (size 3) (u64 1770019616739251654);
  assert_norm (8784043285714375740 + pow2 64 * 8483257759279461889 + pow2 64 * pow2 64 * 8789745728267363600 + pow2 64 * pow2 64 * pow2 64 * 1770019616739251654 < prime256); 
    assert_norm (8784043285714375740 + pow2 64 * 8483257759279461889 + pow2 64 * pow2 64 * 8789745728267363600 + pow2 64 * pow2 64 * pow2 64 * 1770019616739251654 = 11110593207902424140321080247206512405358633331993495164878354046817554469948); 
  assert_norm(0x6B17D1F2E12C4247F8BCE6E563A440F277037D812DEB33A0F4A13945D898C296 == fromDomain_ 11110593207902424140321080247206512405358633331993495164878354046817554469948);

  upd p (size 4) (u64 15992936863339206154);
  upd p (size 5) (u64 10037038012062884956);
  upd p (size 6) (u64 15197544864945402661);
  upd p (size 7) (u64 9615747158586711429);
  assert_norm(15992936863339206154 + pow2 64 * 10037038012062884956 + pow2 64 * pow2 64 * 15197544864945402661 + pow2 64 * pow2 64 * pow2 64 * 9615747158586711429 < prime256);
  assert_norm (15992936863339206154 + pow2 64 * 10037038012062884956 + pow2 64 * pow2 64 * 15197544864945402661 + pow2 64 * pow2 64 * pow2 64 * 9615747158586711429 = 60359023176204190920225817201443260813112970217682417638161152432929735267850);
  assert_norm (0x4FE342E2FE1A7F9B8EE7EB4A7C0F9E162BCE33576B315ECECBB6406837BF51F5 == fromDomain_ 60359023176204190920225817201443260813112970217682417638161152432929735267850);
  
  
  upd p (size 8) (u64 1);
  upd p (size 9) (u64 18446744069414584320);
  upd p (size 10) (u64 18446744073709551615);
  upd p (size 11) (u64 4294967294);
  assert_norm (1 + pow2 64 * 18446744069414584320 + pow2 64 * pow2 64 * 18446744073709551615 + pow2 64 * pow2 64 * pow2 64 * 4294967294 < prime256);
  assert_norm (1 = fromDomain_ 26959946660873538059280334323183841250350249843923952699046031785985);
  assert_norm (1 + pow2 64 * 18446744069414584320 + pow2 64 * pow2 64 * 18446744073709551615 + pow2 64 * pow2 64 * pow2 64 * 4294967294 = 26959946660873538059280334323183841250350249843923952699046031785985) 


(*
let scalarMultiplicationWithoutNorm p result scalar tempBuffer = 
  let h0 = ST.get() in 
  let q = sub tempBuffer (size 0) (size 12) in 
  zero_buffer q;
  let buff = sub tempBuffer (size 12) (size 88) in 
  pointToDomain p result;
    let h2 = ST.get() in 
  montgomery_ladder q result scalar buff;
  copy_point q result;  
    let h3 = ST.get() in 
    lemma_point_to_domain h0 h2 p result;
    lemma_pif_to_domain h2 q
    

let secretToPublicWithoutNorm result scalar tempBuffer = 
    push_frame(); 
      let basePoint = create (size 12) (u64 0) in 
    uploadBasePoint basePoint;
      let q = sub tempBuffer (size 0) (size 12) in 
      let buff = sub tempBuffer (size 12) (size 88) in 
    zero_buffer q; 
      let h1 = ST.get() in 
      lemma_pif_to_domain h1 q; 
    montgomery_ladder q basePoint scalar buff; 
    copy_point q result;
  pop_frame()  

*)




let scalarMultiplicationWithoutNorm p result scalar tempBuffer = 
  let h0 = ST.get() in 
  let q = sub tempBuffer (size 0) (size 12) in 
  zero_buffer q;
  let buff = sub tempBuffer (size 12) (size 88) in 
  pointToDomain p result;
    let h2 = ST.get() in 
  montgomery_ladder_2_precomputed result scalar buff;
  copy_point q result;  
    let h3 = ST.get() in 
    lemma_point_to_domain h0 h2 p result;
    lemma_pif_to_domain h2 q


let secretToPublic m result scalar tempBuffer =
  let buff = sub tempBuffer (size 12) (size 88) in
  begin
  match m with 
  |Ladder -> 
    let basePoint = sub tempBuffer (size 0) (size 12) in 
      uploadBasePoint basePoint;
    montgomery_ladder result basePoint scalar buff
  |Radix4 ->
      montgomery_ladder_2_precomputed result scalar buff
  |Comb -> 
    scalar_multiplication_cmb result scalar buff
   end; 
  (* zero_buffer result; *)
    let h1 = ST.get() in 
    lemma_pif_to_domain h1 basePoint;

  norm result result buff



let secretToPublicWithoutNorm result scalar tempBuffer = 
    push_frame(); 
      let basePoint = create (size 12) (u64 0) in 
    uploadBasePoint basePoint;
      let q = sub tempBuffer (size 0) (size 12) in 
      let buff = sub tempBuffer (size 12) (size 88) in 
    zero_buffer q; 
      let h1 = ST.get() in 
      lemma_pif_to_domain h1 q; 
    montgomery_ladder_2_precomputed basePoint scalar buff; 
    copy_point q result;
  pop_frame()  


(* 
prime = 2**256 - 2**224 + 2**192 + 2**96 -1

def norm(p):    
    x, y, z = p
    z2i = power_mod(z * z, -1, prime)
    z3i = power_mod(z * z * z, -1, prime)
    return ((x * z2i) % prime, (y * z3i) % prime, 1)

def toD(x):
    return x * power_mod (2 ** 256, 1, prime) % prime

def fromD(x):
    return x * power_mod (2 ** 256, prime - 2, prime) % prime

def toFakeAffine(p):
    x, y, z = p 
    multiplier = power_mod (2 ** 256, prime - 2, prime) 
    x = x * multiplier * multiplier % prime
    y = y * multiplier * multiplier * multiplier % prime
    return (x, y, 1)

pX = 0x6B17D1F2E12C4247F8BCE6E563A440F277037D812DEB33A0F4A13945D898C296
pY = 0x4FE342E2FE1A7F9B8EE7EB4A7C0F9E162BCE33576B315ECECBB6406837BF51F5
pZ = 1

pxD = toD(pX)
pyD = toD(pY)
pzD = toD(pZ)

pxD, pyD, pzD = toFakeAffine((pxD, pyD, pzD))

print(hex(pxD), hex(pyD), hex(pzD))

pxE, pyE, pzE = norm((fromD(pxD), fromD(pyD), fromD(pzD)))

print((pxE == pX) and (pyE == pY))
 *)
