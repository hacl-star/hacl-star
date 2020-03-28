module Hacl.Impl.P256 

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Hacl.Impl.P256.Arithmetics

open Lib.Buffer

open Spec.P256.Lemmas
open Spec.P256.Definitions
open Spec.P256.MontgomeryMultiplication
open Spec.P256.MontgomeryMultiplication.PointDouble
open Spec.P256.MontgomeryMultiplication.PointAdd
open Spec.P256.Normalisation
open Spec.P256
open Hacl.Impl.SolinasReduction
open Hacl.Impl.LowLevel
open Hacl.Impl.P256.LowLevel
open Hacl.Impl.P256.MontgomeryMultiplication
open Hacl.Impl.P256.Math 

open Hacl.Impl.P256.PointAdd
open Hacl.Impl.P256.PointDouble



open FStar.Tactics 
open FStar.Tactics.Canon

open FStar.Math.Lemmas

friend Spec.P256.MontgomeryMultiplication
open FStar.Mul

#set-options "--z3rlimit 150 --max_fuel 0 --max_ifuel 0" 
let toDomain value result = 
  push_frame();
    let multBuffer = create (size 8) (u64 0) in 
    shift_256_impl value multBuffer;
    solinas_reduction_impl multBuffer result;
  pop_frame()  


let pointToDomain p result = 
    let p_x = sub p (size 0) (size 4) in 
    let p_y = sub p (size 4) (size 4) in 
    let p_z = sub p (size 8) (size 4) in 
    
    let r_x = sub result (size 0) (size 4) in 
    let r_y = sub result (size 4) (size 4) in 
    let r_z = sub result (size 8) (size 4) in 

    toDomain p_x r_x;
    toDomain p_y r_y;
    toDomain p_z r_z


val fromDomain: f: felem-> result: felem-> Stack unit 
  (requires fun h -> live h f /\ live h result /\ as_nat h f < prime)
  (ensures fun h0 _ h1 -> modifies (loc result) h0 h1 /\ 
    as_nat h1 result = (as_nat h0 f * modp_inv2(pow2 256)) % prime /\ 
    as_nat h1 result = fromDomain_ (as_nat h0 f))

let fromDomain f result = 
  montgomery_multiplication_buffer_by_one f result
    

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
  let tempBuffer20 = sub tempBuffer (size 12) (size 20) in 

    let h0 = ST.get() in 
  montgomery_multiplication_buffer zf zf z2f; 
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
  montgomery_multiplication_buffer zf zf z2f; 
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
val scalarMultiplication_t: #t:buftype -> p: point -> result: point -> 
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


let scalarMultiplication_t #t p result scalar tempBuffer  = 
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
    lemma_coord h3 q

let scalarMultiplicationL = scalarMultiplication_t #MUT

let scalarMultiplicationI = scalarMultiplication_t #IMMUT
let scalarMultiplicationC = scalarMultiplication_t #CONST

let scalarMultiplication #buf_type p result scalar tempBuffer = 
  match buf_type with 
  |MUT -> scalarMultiplicationL p result scalar tempBuffer 
  |IMMUT -> scalarMultiplicationI p result scalar tempBuffer
  |CONST -> scalarMultiplicationC p result scalar tempBuffer


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
    

let secretToPublic result scalar tempBuffer = 
  push_frame(); 
       let basePoint = create (size 12) (u64 0) in 
    uploadBasePoint basePoint;
      let q = sub tempBuffer (size 0) (size 12) in 
      let buff = sub tempBuffer (size 12) (size 88) in 
    zero_buffer q; 
      let h1 = ST.get() in 
      lemma_pif_to_domain h1 q;
    montgomery_ladder q basePoint scalar buff; 
    norm q result buff;  
  pop_frame()


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
