module Hacl.Impl.P256 

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.IntTypes.Compatibility
open Lib.Buffer

open Hacl.Spec.P256.Core

open Hacl.Spec.P256.Lemmas
open Hacl.Spec.P256.Definitions
open Hacl.Impl.SolinasReduction
open Hacl.Spec.P256.MontgomeryMultiplication
open Hacl.Spec.P256.MontgomeryMultiplication.PointDouble
open Hacl.Spec.P256.MontgomeryMultiplication.PointAdd
open Hacl.Spec.P256.Normalisation 
open Hacl.Impl.LowLevel
open Hacl.Spec.P256

 
open FStar.Math.Lemmas

friend Hacl.Spec.P256.MontgomeryMultiplication
open FStar.Mul

#reset-options "--z3rlimit 300" 

inline_for_extraction noextract 
val toDomain: value: felem -> result: felem ->  Stack unit 
  (requires fun h ->  as_nat h value < prime /\ live h value /\live h result /\ eq_or_disjoint value result)
  (ensures fun h0 _ h1 -> modifies (loc result) h0 h1 /\ as_nat h1 result = toDomain_ (as_nat h0 value)) 
 
let toDomain value result = 
  push_frame();
    let multBuffer = create (size 8) (u64 0) in 
    shift_256_impl value multBuffer;
    solinas_reduction_impl multBuffer result;
  pop_frame()  

(*to prove *)
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


inline_for_extraction noextract 
val multiplication_partially_opened: a: felem4 -> b: felem -> result: felem ->Stack unit
  (requires fun h -> as_nat4 a < prime /\ as_nat h b < prime /\ live h b /\ live h result)
  (ensures fun h0 _ h1 -> modifies (loc result) h0 h1 /\ as_nat h1 result = (as_nat4 a * as_nat h0 b * modp_inv2(pow2 256)) % prime)

let multiplication_partially_opened (a0, a1, a2, a3) b result = 
  let b0 = index b (size 0) in 
  let b1 = index b (size 1) in 
  let b2 = index b (size 2) in 
  let b3 = index b (size 3) in 

  let (r0, r1, r2, r3) = montgomery_multiplication (a0, a1, a2, a3) (b0, b1, b2, b3) in 
  assert(as_nat4 (r0, r1, r2, r3) = as_nat4 (a0, a1, a2, a3) * as_nat4 (b0, b1, b2, b3) * modp_inv2(pow2 256) % prime);
 
  upd result (size 0) r0;
  upd result (size 1) r1;
  upd result (size 2) r2;
  upd result (size 3) r3


val fromDomain: f: felem-> result: felem-> Stack unit 
  (requires fun h -> live h f /\ live h result /\ as_nat h f < prime)
  (ensures fun h0 _ h1 -> modifies (loc result) h0 h1 /\ as_nat h1 result = (as_nat h0 f * modp_inv2(pow2 256)) % prime/\ as_nat h1 result = fromDomain_ (as_nat h0 f))

let fromDomain f result = 
  multiplication_partially_opened ((u64 1), (u64 0), u64 0, u64 0) f result
    

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


val quatre: a: felem -> result: felem -> Stack unit
  (requires fun h -> live h a /\ live h result /\ disjoint a result /\ as_nat h a < prime)
  (ensures fun h0 _ h1 -> modifies (loc result) h0 h1 /\ 
    as_nat h1 result = felem_seq_as_nat (mm_quatre_seq (as_seq h0 a)) /\ 
    as_nat h1 result < prime /\ as_seq h1 result == mm_quatre_seq (as_seq h0 a))

#reset-options "--z3refresh --z3rlimit 500" 

let quatre a result = 
    let h0 = ST.get() in 
  montgomery_multiplication_buffer a a result;
  montgomery_multiplication_buffer result result result;
    let h1 = ST.get() in 
  assert(Lib.Sequence.equal (mm_quatre_seq (as_seq h0 a))  (as_seq h1 result))


val multByTwo: a: felem -> result: felem -> Stack unit 
  (requires fun h -> live h a /\ live h result /\ eq_or_disjoint a result /\ as_nat h a < prime )
  (ensures fun h0 _ h1 -> modifies (loc result) h0 h1 /\ 
    as_seq h1 result == mm_byTwo_seq (as_seq h0 a) /\ as_nat h1 result < prime)

let multByTwo a out = 
    let h0 = ST.get() in 
  p256_add a a out;
    let h1 = ST.get() in 
    assert(let out = as_seq h1 out in out == felem_add_seq (as_seq h0 a) (as_seq h0 a));
    lemma_add_same_value_is_by_two (as_seq h0 a)


val multByThree: a: felem -> result: felem -> Stack unit 
  (requires fun h -> live h a /\ live h result /\ disjoint a result /\ as_nat h a < prime )
  (ensures fun h0 _ h1 -> modifies (loc result) h0 h1 /\ as_nat h1 result < prime /\ 
  as_seq h1 result == mm_byThree_seq (as_seq h0 a))

let multByThree a result = 
    let h0 = ST.get() in 
  multByTwo a result;
  p256_add a result result;
  lemma_add_same_value_is_by_three (as_seq h0 a)


val multByFour: a: felem -> result: felem -> Stack unit 
  (requires fun h -> live h a /\ live h result /\ eq_or_disjoint a result /\ as_nat h a < prime )
  (ensures fun h0 _ h1 -> modifies (loc result) h0 h1 /\ as_nat h1 result < prime /\ as_seq h1 result == mm_byFour_seq (as_seq h0 a))

let multByFour a result  = 
    let h0 = ST.get() in 
  multByTwo a result;
    let h1 = ST.get() in 
    assert(as_seq h1 result == mm_byTwo_seq (as_seq h0 a));
  multByTwo result result;
    let h2 = ST.get() in 
    lemma_add_same_value_is_by_four (as_seq h0 a)


val multByEight: a: felem -> result: felem -> Stack unit 
  (requires fun h -> live h a /\ live h result /\ disjoint a result /\ as_nat h a < prime )
  (ensures fun h0 _ h1 -> modifies (loc result) h0 h1 /\ as_nat h1 result < prime /\ 
    as_seq h1 result == mm_byEight_seq (as_seq h0 a))

let multByEight a result  = 
    let h0 = ST.get() in 
  multByTwo a result;
  multByTwo result result;
  multByTwo result result;
  lemma_add_same_value_is_by_eight (as_seq h0 a)


val multByMinusThree: a: felem -> result: felem -> Stack unit 
  (requires fun h -> live h a /\ live h result /\ disjoint a result /\ as_nat h a < prime )
  (ensures fun h0 _ h1 -> modifies (loc result) h0 h1 /\ 
    as_nat h1 result < prime /\ as_seq h1 result == mm_byMinusThree_seq (as_seq h0 a))

let multByMinusThree a result  = 
  let h0 = ST.get() in 
    push_frame();
    multByThree a result;
    let zeros = create (size 4) (u64 0) in 
      let h1 = ST.get() in 
    p256_sub zeros result result;
  pop_frame();
  lemma_add_same_value_is_by_minus_three (as_seq h0 a) (as_seq h1 zeros)


val isZero_uint64:  f: felem -> Stack uint64
  (requires fun h -> live h f /\ as_nat h f < prime)
  (ensures fun h0 r h1 -> modifies0 h0 h1 /\ r == isZero_seq (as_seq h0 f))

let isZero_uint64 f = 
  let a0 = index f (size 0) in 
  let a1 = index f (size 1) in 
  let a2 = index f (size 2) in 
  let a3 = index f (size 3) in 
  isZero_tuple_u (a0, a1, a2, a3)


val copy_point: p: point -> result: point -> Stack unit 
  (requires fun h -> live h p /\ live h result /\ disjoint p result) 
  (ensures fun h0 _ h1 -> modifies (loc result) h0 h1 /\
    as_seq h1 result == copy_point_seq (as_seq h0 p))

let copy_point p result = copy result p
 

(* https://crypto.stackexchange.com/questions/43869/point-at-infinity-and-error-handling*)
#reset-options "--z3rlimit 500" 
inline_for_extraction noextract 
val point_double_compute_s_m: p: point -> s: felem -> m: felem -> tempBuffer:lbuffer uint64 (size 24) -> Stack unit
  (requires fun h -> live h p /\ live h s /\ live h m /\ live h tempBuffer /\
    disjoint p s /\ disjoint p m /\ disjoint p tempBuffer /\
    disjoint s m /\ disjoint s tempBuffer /\ disjoint m tempBuffer /\
    as_nat h (gsub p (size 8) (size 4)) < prime /\ 
    as_nat h (gsub p (size 0) (size 4)) < prime /\ 
    as_nat h (gsub p (size 4) (size 4)) < prime)
  (ensures fun h0 _ h1 -> 
    let x_sequence = Lib.Sequence.sub (as_seq h0 p) 0 4 in 
    let y_sequence = Lib.Sequence.sub (as_seq h0 p) 4 4 in 
    let z_sequence = Lib.Sequence.sub (as_seq h0 p) 8 4 in 
     felem_seq_as_nat x_sequence < prime /\
     felem_seq_as_nat y_sequence < prime /\
     felem_seq_as_nat z_sequence < prime /\  
     modifies (loc tempBuffer |+| loc s |+| loc m) h0 h1 /\ 
     as_nat h1 s < prime  /\ as_nat h1 m < prime /\
     (let (s_, m_) = point_double_compute_s_m_seq (as_seq h0 p) in as_seq h1 s == s_ /\ as_seq h1 m == m_))


let point_double_compute_s_m p s m tempBuffer =
  let h0 = ST.get() in 
    let px = sub p (size 0) (size 4) in 
    let py = sub p (size 4) (size 4) in 
    let pz = sub p (size 8) (size 4) in 

    let yy = sub tempBuffer (size 0) (size 4) in 
    let xyy = sub tempBuffer (size 4) (size 4) in 
    let zzzz = sub tempBuffer (size 8) (size 4) in 
    let minThreeZzzz = sub tempBuffer (size 12) (size 4) in 
    let xx = sub tempBuffer (size 16) (size 4) in 
    let threeXx = sub tempBuffer (size 20) (size 4) in 

    montgomery_multiplication_buffer py py yy; 
    montgomery_multiplication_buffer px yy xyy;
    multByFour xyy s;

    quatre pz zzzz; 
    multByMinusThree zzzz minThreeZzzz;
    montgomery_multiplication_buffer px px xx;
    multByThree xx threeXx;
    p256_add minThreeZzzz threeXx m;
  let h1 = ST.get() in 
  assert(let s_, m_ = point_double_compute_s_m_seq (as_seq h0 p) in Lib.Sequence.equal (s_) (as_seq h1 s)
    /\ Lib.Sequence.equal m_ (as_seq h1 m))


inline_for_extraction noextract 
val point_double_compute_x3: x3: felem -> 
  s: felem -> m: felem -> tempBuffer: lbuffer uint64 (size 8) -> Stack unit 
  (requires fun h -> live h x3 /\ live h s /\ live h m /\ live h tempBuffer /\
    
    LowStar.Monotonic.Buffer.all_disjoint [loc x3; loc s; loc m; loc tempBuffer] /\
    as_nat h s < prime /\ as_nat h m < prime 
  )
  (ensures fun h0 _ h1 -> modifies (loc x3 |+| loc tempBuffer) h0 h1 /\
    as_seq h1 x3 == point_double_compute_x3_seq (as_seq h0 s) (as_seq h0 m) /\ 
    as_nat h1 x3 < prime
   )

#reset-options "--z3rlimit 500 --z3refresh" 

let point_double_compute_x3 x3 s m tempBuffer = 
   let twoS = sub tempBuffer (size 0) (size 4) in 
   let mm = sub tempBuffer (size 4) (size 4) in 
    multByTwo s twoS;
    Hacl.Spec.P256.MontgomeryMultiplication.montgomery_multiplication_buffer m m mm;
    p256_sub mm twoS x3
 

inline_for_extraction noextract 
val point_double_compute_y3: p_y: felem ->  y3: felem ->  x3: felem -> 
  s: felem -> m: felem -> tempBuffer: lbuffer uint64 (size 16) -> Stack unit 
  (requires fun h -> live h p_y /\ live h y3 /\ live h x3 /\ live h s /\ live h m /\ live h tempBuffer
    /\ LowStar.Monotonic.Buffer.all_disjoint [loc p_y; loc y3; loc x3; loc s; loc m; loc tempBuffer]
    /\ as_nat h x3 < prime /\ as_nat h s < prime /\ as_nat h m < prime /\
    as_nat h p_y < prime)
    
  (ensures fun h0 _ h1 -> modifies (loc y3 |+| loc tempBuffer) h0 h1 /\ 
    as_seq h1 y3 == point_double_compute_y3_seq (as_seq h0 p_y) (as_seq h0 x3) (as_seq h0 s) (as_seq h0 m) /\
    as_nat h1 y3 < prime
   )

let point_double_compute_y3 p_y y3 x3 s m tempBuffer = 
    let yyyy = sub tempBuffer (size 0) (size 4) in 
    let eightYyyy = sub tempBuffer (size 4) (size 4) in 
    let sx3 = sub tempBuffer (size 8) (size 4) in 
    let msx3 = sub tempBuffer (size 12) (size 4) in 
    quatre p_y yyyy;
    multByEight yyyy eightYyyy;
    p256_sub s x3 sx3;
    Hacl.Spec.P256.MontgomeryMultiplication.montgomery_multiplication_buffer m sx3 msx3; 
    p256_sub msx3 eightYyyy y3

#reset-options "--z3refresh --z3rlimit 500"

let point_double p result tempBuffer = 
	let h0 = ST.get() in   
    let s = sub tempBuffer (size 0) (size 4) in 
    let m = sub tempBuffer (size 4) (size 4) in 
    let buffer_for_s_m = sub tempBuffer (size 8) (size 24) in 

    let buffer_for_x3 = sub tempBuffer (size 32) (size 8) in 
    let buffer_for_y3 = sub tempBuffer (size 40) (size 16) in 

    let pypz = sub tempBuffer (size 56) (size 4) in 

    let x3 : lbuffer_t MUT uint64 (size 4) = sub tempBuffer (size 60) (size 4) in 
    let y3 : lbuffer_t MUT uint64 (size 4) = sub tempBuffer (size 64) (size 4) in 
    let z3 : lbuffer_t MUT uint64 (size 4) = sub tempBuffer (size 68) (size 4) in 

    let p_x = sub p (size 0) (size 4) in 
    let p_y = sub p (size 4) (size 4) in 
    let p_z = sub p (size 8) (size 4) in 

   point_double_compute_s_m p s m buffer_for_s_m; 
     let h2 = ST.get() in 
     assert(modifies1 tempBuffer h0 h2);
   point_double_compute_x3 x3 s m buffer_for_x3;
   point_double_compute_y3 p_y y3 x3 s m buffer_for_y3;
     let h4 = ST.get() in 
     assert(modifies1 tempBuffer h2 h4);
   Hacl.Spec.P256.MontgomeryMultiplication.montgomery_multiplication_buffer p_y p_z pypz;
   multByTwo pypz z3;
     let h5 = ST.get() in  
     concat3 (size 4) x3 (size 4) y3 (size 4) z3 result ; 

   let hend = ST.get() in 
   assert(as_seq hend result == point_double_seq (as_seq h0 p));
   assert(modifies1 tempBuffer h0 h5);
   assert(modifies2 tempBuffer result h0 hend)

val copy_conditional: out: felem -> x: felem -> mask: uint64{uint_v mask = 0 \/ uint_v mask = pow2 64 - 1} -> Stack unit 
  (requires fun h -> live h out /\ live h x /\ as_nat h out < prime /\ as_nat h x < prime)
  (ensures fun h0 _ h1 -> modifies (loc out) h0 h1 /\ as_nat h1 out < prime /\ 
    as_seq h1 out == copy_conditional_seq (as_seq h0 out) (as_seq h0 x) mask)

let copy_conditional out x mask = 
    let h0 = ST.get() in 
  let out_0 = index out (size 0) in 
  let out_1 = index out (size 1) in 
  let out_2 = index out (size 2) in 
  let out_3 = index out (size 3) in 

  let x_0 = index x (size 0) in 
  let x_1 = index x (size 1) in 
  let x_2 = index x (size 2) in 
  let x_3 = index x (size 3) in 

  let (temp_0, temp_1, temp_2, temp_3)  = copy_conditional_tuple (out_0, out_1, out_2, out_3) (x_0, x_1, x_2, x_3) mask in 

  upd out (size 0) temp_0;
  upd out (size 1) temp_1;
  upd out (size 2) temp_2;
  upd out (size 3) temp_3;

    let h1 = ST.get() in 
    assert(Lib.Sequence.equal (as_seq h1 out) (copy_conditional_seq (as_seq h0 out) (as_seq h0 x) mask))


val copy_point_conditional: x3_out: felem -> y3_out: felem -> z3_out: felem -> p: point -> maskPoint: point -> Stack unit
  (requires fun h -> live h x3_out /\ live h y3_out /\ live h z3_out /\ live h p /\ live h maskPoint /\ 
    LowStar.Monotonic.Buffer.all_disjoint[loc x3_out; loc y3_out; loc z3_out; loc p; loc maskPoint] /\
    as_nat h x3_out < prime /\ as_nat h y3_out < prime /\ as_nat h z3_out < prime /\
    as_nat h (gsub p (size 0) (size 4)) < prime /\ 
    as_nat h (gsub p (size 4) (size 4)) < prime /\ 
    as_nat h (gsub p (size 8) (size 4)) < prime /\
    as_nat h (gsub maskPoint (size 0) (size 4)) < prime /\ 
    as_nat h (gsub maskPoint (size 4) (size 4)) < prime /\ 
    as_nat h (gsub maskPoint (size 8) (size 4)) < prime 
  )
  (ensures fun h0 _ h1 -> modifies (loc x3_out |+| loc y3_out |+| loc z3_out) h0 h1 /\ 
    as_nat h1 x3_out < prime /\
    as_nat h1 y3_out < prime /\
    as_nat h1 z3_out < prime /\
    (let xN, yN, zN = copy_point_conditional_seq (as_seq h0 x3_out) (as_seq h0 y3_out) (as_seq h0 z3_out) (as_seq h0 p) (as_seq h0 maskPoint) in 
      xN == as_seq h1 x3_out /\ yN == as_seq h1 y3_out /\ zN == as_seq h1 z3_out)
    )

let copy_point_conditional x3_out y3_out z3_out p maskPoint = 
  let h0 = ST.get() in 
  
  let z = sub maskPoint (size 8) (size 4) in 
  let mask = isZero_uint64 z in 

  let p_x = sub p (size 0) (size 4) in 
  let p_y = sub p (size 4) (size 4) in 
  let p_z = sub p (size 8) (size 4) in 

  copy_conditional x3_out p_x mask;
  copy_conditional y3_out p_y mask;
  copy_conditional z3_out p_z mask


let compare_felem a b = 
  let a_0 = index a (size 0) in 
  let a_1 = index a (size 1) in 
  let a_2 = index a (size 2) in 
  let a_3 = index a (size 3) in 

  let b_0 = index b (size 0) in 
  let b_1 = index b (size 1) in 
  let b_2 = index b (size 2) in 
  let b_3 = index b (size 3) in 

  equalFelem(a_0, a_1, a_2, a_3) (b_0, b_1, b_2, b_3)

inline_for_extraction noextract 
val move_from_jacobian_coordinates: u1: felem -> u2: felem -> s1: felem -> s2: felem ->  p: point -> q: point -> 
  tempBuffer16: lbuffer uint64 (size 16) -> 
  Stack unit (requires fun h -> live h u1 /\ live h u2 /\ live h s1 /\ live h s2 /\ live h p /\ live h q /\ live h tempBuffer16 /\
   LowStar.Monotonic.Buffer.all_disjoint [loc tempBuffer16; loc p; loc q; loc u1; loc u2; loc s1; loc s2] /\
    as_nat h (gsub p (size 8) (size 4)) < prime /\ 
    as_nat h (gsub p (size 0) (size 4)) < prime /\ 
    as_nat h (gsub p (size 4) (size 4)) < prime /\
    as_nat h (gsub q (size 8) (size 4)) < prime /\ 
    as_nat h (gsub q (size 0) (size 4)) < prime /\ 
    as_nat h (gsub q (size 4) (size 4)) < prime
    )
  (ensures fun h0 _ h1 -> 
    modifies (loc u1 |+| loc u2 |+| loc s1 |+| loc s2 |+| loc tempBuffer16) h0 h1 /\
    as_nat h1 u1 < prime /\ as_nat h1 u2 < prime /\ as_nat h1 s1 < prime /\ as_nat h1 s2 < prime  /\
    (
      let u1_, u2_, s1_, s2_ = move_from_jacobian_coordinates_seq (as_seq h0 p) (as_seq h0 q) in 
      as_seq h1 u1 == u1_ /\ as_seq h1 u2 == u2_ /\ as_seq h1 s1 == s1_ /\ as_seq h1 s2 == s2_
    )
  )  

let move_from_jacobian_coordinates u1 u2 s1 s2 p q tempBuffer = 
    let h0 = ST.get() in 
   let x1 = sub p (size 0) (size 4) in 
   let y1 = sub p (size 4) (size 4) in 
   let z1 = sub p (size 8) (size 4) in 

   let x2 = sub q (size 0) (size 4) in 
   let y2 = sub q (size 4) (size 4) in 
   let z2 = sub q (size 8) (size 4) in 

   let z2Square = sub tempBuffer (size 0) (size 4) in 
   let z1Square = sub tempBuffer (size 4) (size 4) in 
   let z2Cube = sub tempBuffer (size 8) (size 4) in 
   let z1Cube = sub tempBuffer (size 12) (size 4) in  

   montgomery_multiplication_buffer z2 z2 z2Square;
   montgomery_multiplication_buffer z1 z1 z1Square;
   montgomery_multiplication_buffer z2Square z2 z2Cube;
   montgomery_multiplication_buffer z1Square z1 z1Cube;

     let h1 = ST.get() in 
     assert(modifies1 tempBuffer h0 h1);

   montgomery_multiplication_buffer x1 z2Square u1;
   montgomery_multiplication_buffer x2 z1Square u2;

     let h2 = ST.get() in 
     assert(modifies2 u1 u2 h1 h2);

   montgomery_multiplication_buffer y1 z2Cube s1;
   montgomery_multiplication_buffer y2 z1Cube s2;

     let h3 = ST.get() in 
      assert(modifies2 s1 s2 h2 h3);
     assert(let u1_, u2_, s1_, s2_ = move_from_jacobian_coordinates_seq (as_seq h0 p) (as_seq h0 q) in 
      as_seq h3 u1 == u1_ /\ as_seq h3 u2 == u2_ /\ as_seq h3 s1 == s1_ /\ as_seq h3 s2 == s2_)
      
inline_for_extraction noextract 
val compute_common_params_point_add: h: felem -> r: felem -> uh: felem -> hCube: felem -> 
  u1: felem -> u2: felem -> s1: felem -> s2: felem -> tempBuffer: lbuffer uint64 (size 16) -> 
  Stack unit 
    (requires fun h0 -> live h0 h /\ live h0 r /\ live h0 uh /\ live h0 hCube /\ live h0 u1 /\ live h0 u2 /\ live h0 s1 /\ live h0 s2 /\ live h0 tempBuffer /\  LowStar.Monotonic.Buffer.all_disjoint [loc u1; loc u2; loc s1; loc s2; loc h; loc r; loc uh; loc hCube; loc tempBuffer] /\ 
  as_nat h0 u1 < prime /\ as_nat h0 u2 < prime /\ as_nat h0 s1 < prime /\ as_nat h0 s2 < prime)
    (ensures fun h0 _ h1 ->  modifies (loc h |+| loc r |+| loc uh |+| loc hCube |+| loc tempBuffer) h0 h1 /\ as_nat h1 h < prime /\ as_nat h1 r < prime /\ as_nat h1 uh < prime /\ as_nat h1 hCube < prime /\
      (let (hN, rN, uhN, hCubeN) = compute_common_params_point_add_seq (as_seq h0 u1) (as_seq h0 u2) (as_seq h0 s1) (as_seq h0 s2) in  as_seq h1 h == hN /\ as_seq h1 r == rN /\ as_seq h1 uh == uhN /\ as_seq h1 hCube == hCubeN)
    )


let compute_common_params_point_add h r uh hCube u1 u2 s1 s2 tempBuffer =  
      let temp = sub tempBuffer (size 0) (size 4) in 
      p256_sub u2 u1 h; 
      p256_sub s2 s1 r; 
      montgomery_multiplication_buffer h h temp;
      montgomery_multiplication_buffer u1 temp uh;
      montgomery_multiplication_buffer h temp hCube

inline_for_extraction noextract 
val computeX3_point_add: x3: felem -> hCube: felem -> uh: felem -> r: felem -> tempBuffer: lbuffer uint64 (size 16)->  Stack unit 
  (requires fun h0 -> live h0 x3 /\ live h0 hCube /\ live h0 uh /\ live h0 r /\ live h0 tempBuffer /\
    LowStar.Monotonic.Buffer.all_disjoint [loc x3; loc hCube; loc uh; loc r; loc tempBuffer] /\
    as_nat h0 hCube < prime /\as_nat h0 uh < prime /\ as_nat h0 r < prime
  )
  (ensures fun h0 _ h1 -> modifies (loc x3 |+| loc tempBuffer) h0 h1 /\ as_nat h1 x3 < prime /\ 
    as_seq h1 x3 == computeX3_point_add_seq (as_seq h0 hCube) (as_seq h0 uh) (as_seq h0 r) 
  )

let computeX3_point_add x3 hCube uh r tempBuffer = 
    let rSquare = sub tempBuffer (size 0) (size 4) in 
    let r_h = sub tempBuffer (size 4) (size 4) in 
    let twouh = sub tempBuffer (size 8) (size 4) in 
    montgomery_multiplication_buffer r r rSquare; 
    p256_sub rSquare hCube r_h;
    multByTwo uh twouh;
    p256_sub r_h twouh x3


inline_for_extraction noextract 
val computeY3_point_add:y3: felem -> s1: felem -> hCube: felem -> uh: felem -> x3_out: felem -> r: felem -> tempBuffer: lbuffer uint64 (size 16) -> 
  Stack unit (requires fun h -> live h y3 /\ live h s1 /\ live h hCube /\ live h uh /\ live h x3_out /\ live h r /\ live h tempBuffer /\
    LowStar.Monotonic.Buffer.all_disjoint [loc y3; loc s1; loc hCube; loc uh; loc x3_out; loc r; loc tempBuffer] /\
    as_nat h s1 < prime /\ as_nat h hCube < prime /\ as_nat h uh < prime /\ as_nat h x3_out <prime /\ as_nat h r < prime)
    (ensures fun h0 _ h1 -> modifies (loc y3 |+| loc tempBuffer) h0 h1 /\ as_nat h1 y3 < prime /\ 
    as_seq h1 y3 ==  computeY3_point_add_seq (as_seq h0 s1) (as_seq h0 hCube) (as_seq h0 uh) (as_seq h0 x3_out) (as_seq h0 r))
    
let computeY3_point_add y3 s1 hCube uh x3_out r tempBuffer = 
    let s1hCube = sub tempBuffer (size 0) (size 4) in 
    let u1hx3 = sub tempBuffer (size 4) (size 4) in 
    let ru1hx3 = sub tempBuffer (size 8) (size 4) in 

    montgomery_multiplication_buffer s1 hCube s1hCube;
    p256_sub uh x3_out u1hx3;
    montgomery_multiplication_buffer r u1hx3 ru1hx3;
    p256_sub ru1hx3 s1hCube y3


inline_for_extraction noextract 
val computeZ3_point_add: z3: felem ->  z1: felem -> z2: felem -> h: felem -> tempBuffer: lbuffer uint64 (size 16) -> 
  Stack unit (requires fun h0 -> live h0 z3 /\ live h0 z1 /\ live h0 z2 /\ live h0 h /\ live h0 tempBuffer /\ live h0 z3 /\
  LowStar.Monotonic.Buffer.all_disjoint [loc z1; loc z2; loc h; loc tempBuffer; loc z3] /\
  as_nat h0 z1 < prime /\ as_nat h0 z2 < prime /\ as_nat h0 h < prime)
  (ensures fun h0 _ h1 -> modifies (loc z3 |+| loc tempBuffer) h0 h1 /\ as_nat h1 z3 < prime /\ 
    as_seq h1 z3 == computeZ3_point_add_seq (as_seq h0 z1) (as_seq h0 z2) (as_seq h0 h)
  )  

let computeZ3_point_add z3 z1 z2 h tempBuffer = 
  let z1z2 = sub tempBuffer (size 0) (size 4) in
  montgomery_multiplication_buffer z1 z2 z1z2;
  montgomery_multiplication_buffer h z1z2 z3


inline_for_extraction noextract 
val point_double_condition: u1: felem -> u2: felem -> s1: felem -> s2: felem ->z1: felem -> z2: felem -> Stack bool 
  (requires fun h -> live h u1 /\ live h u2 /\ live h s1 /\ live h s2 /\ live h z1 /\ live h z2 /\
    as_nat h u1 < prime /\ as_nat h u2 < prime /\ as_nat h s1 < prime /\ as_nat h s2 < prime /\
    as_nat h z1 < prime /\ as_nat h z2 < prime /\ 
    LowStar.Monotonic.Buffer.all_disjoint [loc u1; loc u2; loc s1; loc s2; loc z1; loc z2])
  (ensures fun h0 r h1 -> modifies0 h0 h1 /\ r == point_double_condition_seq (as_seq h0 u1) (as_seq h0 u2) (as_seq h0 s1) (as_seq h0 s2) (as_seq h0 z1) (as_seq h0 z2))   

let point_double_condition u1 u2 s1 s2 z1 z2 = 
  let one = compare_felem u1 u2 in 
  let two = compare_felem s1 s2 in 
  let z1notZero = isZero_uint64 z1 in 
  let z2notZero = isZero_uint64 z2 in 
  let pointsInf = logand (lognot z1notZero) (lognot z2notZero) in 
  let onetwo = logand one two in 
  let result = logand onetwo pointsInf in 
  eq_u64 result (u64 0xffffffffffffffff)


inline_for_extraction noextract 
val point_add_if_second_branch_impl: result: point -> p: point -> q: point -> u1: felem -> u2: felem -> s1: felem -> s2: felem -> r: felem -> h: felem -> uh: felem -> hCube: felem -> tempBuffer28 : lbuffer uint64 (size 28) -> 
  Stack unit (requires fun h0 -> live h0 result /\ live h0 p /\ live h0 q /\ live h0 u1 /\ live h0 u2 /\ live h0 s1 /\ live h0 s2 /\ live h0 r /\ live h0 h /\ live h0 uh /\ live h0 hCube /\ live h0 tempBuffer28 /\
  as_nat h0 u1 < prime  /\ as_nat h0 u2 < prime  /\ as_nat h0 s1 < prime /\ as_nat h0 s2 < prime /\ as_nat h0 r < prime /\
  as_nat h0 h < prime /\ as_nat h0 uh < prime /\ as_nat h0 hCube < prime /\
  eq_or_disjoint p result /\
  LowStar.Monotonic.Buffer.all_disjoint [loc p; loc q; loc u1; loc u2; loc s1; loc s2; loc r; loc h; loc uh; loc hCube; loc tempBuffer28] /\ disjoint result tempBuffer28 /\
    as_nat h0 (gsub p (size 8) (size 4)) < prime /\ 
    as_nat h0 (gsub p (size 0) (size 4)) < prime /\ 
    as_nat h0 (gsub p (size 4) (size 4)) < prime /\
    as_nat h0 (gsub q (size 8) (size 4)) < prime /\ 
    as_nat h0 (gsub q (size 0) (size 4)) < prime /\  
    as_nat h0 (gsub q (size 4) (size 4)) < prime /\
    (let u1_, u2_, s1_, s2_ = move_from_jacobian_coordinates_seq (as_seq h0 p) (as_seq h0 q) in 
    u1_ == (as_seq h0 u1) /\ u2_ == (as_seq h0 u2) /\ s1_ == (as_seq h0 s1) /\ s2_ == (as_seq h0 s2)) /\
    (let h_, r_, uh_, hCube_ = compute_common_params_point_add_seq (as_seq h0 u1) (as_seq h0 u2) (as_seq h0 s1) (as_seq h0 s2) in h_ == (as_seq h0 h) /\ r_ == (as_seq h0 r) /\ uh_ == (as_seq h0 uh) /\ hCube_ == (as_seq h0 hCube)))
  (ensures fun h0 _ h1 -> modifies (loc tempBuffer28 |+| loc result) h0 h1 /\ 
    as_seq h1 result == point_add_if_second_branch_seq (as_seq h0 p) (as_seq h0 q) (as_seq h0 u1) (as_seq h0 u2) (as_seq h0 s1) (as_seq h0 s2) (as_seq h0 r) (as_seq h0 h) (as_seq h0 uh) (as_seq h0 hCube))

let point_add_if_second_branch_impl result p q u1 u2 s1 s2 r h uh hCube tempBuffer28 = 
    let h0 = ST.get() in 

  let z1 = sub p (size 8) (size 4) in 
  let z2 = sub q (size 8) (size 4) in 

  let tempBuffer16 = sub tempBuffer28 (size 0) (size 16) in 
  let x3_out = Lib.Buffer.sub tempBuffer28 (size 16) (size 4) in 
  let y3_out = Lib.Buffer.sub tempBuffer28 (size 20) (size 4) in 
  let z3_out = Lib.Buffer.sub tempBuffer28 (size 24) (size 4) in 

  computeX3_point_add x3_out hCube uh r tempBuffer16; 
    let h1 = ST.get() in 
    assert(modifies1 tempBuffer28 h0 h1);
  computeY3_point_add y3_out s1 hCube uh x3_out r tempBuffer16; 
    let h2 = ST.get() in 
    assert(modifies1 tempBuffer28 h1 h2);
  computeZ3_point_add z3_out z1 z2 h tempBuffer16;
    let h3 = ST.get() in 
    assert(modifies1 tempBuffer28 h2 h3);

  copy_point_conditional x3_out y3_out z3_out q p;
    let h4 = ST.get() in 
    assert(modifies1 tempBuffer28 h3 h4);
  copy_point_conditional x3_out y3_out z3_out p q;
    let h5 = ST.get() in 
    assert(modifies1 tempBuffer28 h4 h5);
    assert(modifies1 tempBuffer28 h0 h5);

  concat3 (size 4) x3_out (size 4) y3_out (size 4) z3_out result; 
    let h6 = ST.get() in 
    assert(modifies1 result h5 h6);
    assert(modifies2 tempBuffer28 result h0 h6);
    assert(Lib.Sequence.equal (as_seq h6 result) (point_add_if_second_branch_seq (as_seq h0 p) (as_seq h0 q) (as_seq h0 u1) (as_seq h0 u2) (as_seq h0 s1) (as_seq h0 s2) (as_seq h0 r) (as_seq h0 h) (as_seq h0 uh) (as_seq h0 hCube)))
    
 
#reset-options "--z3rlimit 200"

let point_add p q result tempBuffer = 
    let h0 = ST.get() in 
    
   let z1 = sub p (size 8) (size 4) in 
   let z2 = sub q (size 8) (size 4) in 

   let tempBuffer16 = sub tempBuffer (size 0) (size 16) in 
   
   let u1 = sub tempBuffer (size 16) (size 4) in 
   let u2 = sub tempBuffer (size 20) (size 4) in 
   let s1 = sub tempBuffer (size 24) (size 4) in 
   let s2 = sub tempBuffer (size 28) (size 4) in 

   let h = sub tempBuffer (size 32) (size 4) in 
   let r = sub tempBuffer (size 36) (size 4) in 
   let uh = sub tempBuffer (size 40) (size 4) in 

   let hCube = sub tempBuffer (size 44) (size 4) in 

   let x3_out = sub tempBuffer (size 48) (size 4) in 
   let y3_out = sub tempBuffer (size 52) (size 4) in 
   let z3_out = sub tempBuffer (size 56) (size 4) in 

   let tempBuffer28 = sub tempBuffer (size 60) (size 28) in 

   move_from_jacobian_coordinates u1 u2 s1 s2 p q tempBuffer16;
   let flag = point_double_condition u1 u2 s1 s2 z1 z2 in 

   if flag then
      begin
	let h0_1 = ST.get() in 
	assert(modifies1 tempBuffer h0 h0_1);
	point_double p result tempBuffer;
	let h0_2 = ST.get() in 
	  assert(modifies2 tempBuffer result h0_1 h0_2);
	  assert(modifies2 tempBuffer result h0 h0_2);
	  assert(Lib.Sequence.equal (as_seq h0_2 result) (point_add_seq (as_seq h0 p) (as_seq h0 q)))
     end	   
   else
     begin
       let h1_1 = ST.get() in 
	   assert(modifies1 tempBuffer h0 h1_1);
	 compute_common_params_point_add h r uh hCube u1 u2 s1 s2 tempBuffer16;
	   let h1_2 = ST.get() in 
	   assert (modifies1 tempBuffer h1_1 h1_2);  
	 point_add_if_second_branch_impl result p q u1 u2 s1 s2 r h uh hCube tempBuffer28; 
	   let h1_3 = ST.get() in  
	   assert(modifies2 tempBuffer result h1_2 h1_3)
     end; 
   let hend = ST.get() in   
   assert(modifies2 tempBuffer result h0 hend);
   assert(Lib.Sequence.equal (as_seq hend result) (point_add_seq (as_seq h0 p) (as_seq h0 q)))


inline_for_extraction noextract 
val uploadOneImpl: f: felem -> Stack unit
  (requires fun h -> live h f)
  (ensures fun h0 _ h1 -> as_nat h1 f == 1 /\ modifies (loc f) h0 h1)
  
let uploadOneImpl f = 
  upd f (size 0) (u64 1);
  upd f (size 1) (u64 0);
  upd f (size 2) (u64 0);
  upd f (size 3) (u64 0)

val lemma_pointAtInfInDomain: x: nat -> y: nat -> z: nat -> 
  Lemma (isPointAtInfinity (x, y, z)== isPointAtInfinity ((fromDomain_ x), (fromDomain_ y), (fromDomain_ z)))

let lemma_pointAtInfInDomain x y z = admit()

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


inline_for_extraction noextract
val normalisation_update: z2x: felem -> z3y: felem ->p: point ->  resultPoint: point -> Stack unit 
  (requires fun h -> live h z2x /\ live h z3y /\ live h resultPoint /\ 
    as_nat h z2x < prime256 /\ as_nat h z3y < prime /\
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
	if Hacl.Spec.P256.isPointAtInfinity (fromDomain_ x0, fromDomain_ y0, fromDomain_ z0) then  z1 == 0 else z1 == 1
      ))
  )

#reset-options "--z3rlimit 400"

let normalisation_update z2x z3y p resultPoint = 
  push_frame(); 
    let zeroBuffer = create (size 4) (u64 0) in 
    
  let resultX = sub resultPoint (size 0) (size 4) in 
  let resultY = sub resultPoint (size 4) (size 4) in 
  let resultZ = sub resultPoint (size 8) (size 4) in 
    let h0 = ST.get() in 
  let bit = isPointAtInfinityPrivate resultPoint in
  fromDomain z2x resultX;
  fromDomain z3y resultY;
  uploadOneImpl resultZ;
    let h1 = ST.get() in 
  copy_conditional resultZ zeroBuffer bit;
    let h2 = ST.get() in 
  pop_frame()
  
 
#reset-options "--z3refresh --z3rlimit 500" 
let norm p resultPoint tempBuffer = 
  let xf = sub p (size 0) (size 4) in 
  let yf = sub p (size 4) (size 4) in 
  let zf = sub p (size 8) (size 4) in 

  
  let z2f = sub tempBuffer (size 4) (size 4) in 
  let z3f = sub tempBuffer (size 8) (size 4) in
  let tempBuffer20 = sub tempBuffer (size 12) (size 20) in 

    let h0 = ST.get() in 
  Hacl.Spec.P256.MontgomeryMultiplication.montgomery_multiplication_buffer zf zf z2f;
  Hacl.Spec.P256.MontgomeryMultiplication.montgomery_multiplication_buffer z2f zf z3f;

  Hacl.Spec.P256.MontgomeryMultiplication.exponent z2f z2f tempBuffer20;
  Hacl.Spec.P256.MontgomeryMultiplication.exponent z3f z3f tempBuffer20;
     
  Hacl.Spec.P256.MontgomeryMultiplication.montgomery_multiplication_buffer xf z2f z2f;
  Hacl.Spec.P256.MontgomeryMultiplication.montgomery_multiplication_buffer yf z3f z3f;

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


(* this piece of code is taken from Hacl.Curve25519 *)
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
  mod_mask_lemma ((Lib.Sequence.index (as_seq h0 s) (v n / 8)) >>. (n %. 8ul)) 1ul;
  assert_norm (1 = pow2 1 - 1);
  assert (v (mod_mask #U8 #SEC 1ul) == v (u8 1));
  to_u64 ((s.(n /. 8ul) >>. (n %. 8ul)) &. u8 1)


val lemma_modifies3: a: LowStar.Monotonic.Buffer.loc -> b: LowStar.Monotonic.Buffer.loc -> c: LowStar.Monotonic.Buffer.loc -> 
  Lemma (ensures ((a |+| b |+| c) == (c |+| b |+| a)))

let lemma_modifies3 a b c = 
  LowStar.Monotonic.Buffer.loc_union_comm a b;
  LowStar.Monotonic.Buffer.loc_union_assoc b a c;
  LowStar.Monotonic.Buffer.loc_union_comm a c;
  LowStar.Monotonic.Buffer.loc_union_assoc b c a;
  LowStar.Monotonic.Buffer.loc_union_comm b c


val lemma_modifies3_1: a: LowStar.Monotonic.Buffer.loc -> b: LowStar.Monotonic.Buffer.loc -> c: LowStar.Monotonic.Buffer.loc -> 
  Lemma (ensures ((a |+| b |+| c) == (a |+| c |+| b)))

let lemma_modifies3_1 a b c = 
  LowStar.Monotonic.Buffer.loc_union_assoc a b c;
  LowStar.Monotonic.Buffer.loc_union_comm b c;
  LowStar.Monotonic.Buffer.loc_union_assoc a c b

val lemma_modifies_3_two_parts: 
  (#a0: Type0) ->
  (#a1: Type0) -> 
  (#a2: Type0) -> 
  a: buffer_t MUT a0 ->
  b: buffer_t MUT a1 ->
  c: buffer_t MUT a2 ->
  h0: FStar.HyperStack.mem ->
  h1: FStar.HyperStack.mem -> 
  h2: FStar.HyperStack.mem -> 
  Lemma (requires (modifies3 a b c h0 h1 /\ modifies3 a c b h1 h2))
  (ensures (modifies3  c b a h0 h2))

let lemma_modifies_3_two_parts #a0 #a1 #a2 a b c h0 h1 h2 = ()


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
      let p1 = as_seq h1 p in let q1 = as_seq h1 q in 
      let pN, qN = Hacl.Spec.P256.Ladder.montgomery_ladder_step1_seq (as_seq h0 p) (as_seq h0 q) in 
      pN == p1 /\ qN == q1 ) 
    )


let montgomery_ladder_step1 r0 r1 tempBuffer = 
    let h0 = ST.get() in 
  point_add r0 r1 r1 tempBuffer;
    let h1 = ST.get() in 
  point_double r0 r0 tempBuffer; 
    let h2 = ST.get() in 
    
  modifies2_is_modifies3 tempBuffer r1 r0 h0 h1; 
  modifies2_is_modifies3 tempBuffer r0 r1 h1 h2;
  lemma_modifies_3_two_parts tempBuffer r1 r0 h0 h1 h2;
  assert(modifies3 r0 r1 tempBuffer h0 h2);
  assert(let pN, qN = Hacl.Spec.P256.Ladder.montgomery_ladder_step1_seq (as_seq h0 r0) (as_seq h0 r1) in 
      Lib.Sequence.equal (as_seq h2 r0) pN /\ Lib.Sequence.equal (as_seq h2 r1) qN)
      

val lemma_step: i: size_t {uint_v i < 256} -> Lemma  (uint_v ((size 255) -. i) == 255 - (uint_v i))
let lemma_step i = ()

val lemma_to_point_buffer: h: mem -> b: lbuffer uint64 (size 12) {
    as_nat h (gsub b (size 0) (size 4)) < prime /\ 
    as_nat h (gsub b (size 4) (size 4)) < prime /\
    as_nat h (gsub b (size 8) (size 4)) < prime} -> 
    Lemma (ensures (let b_seq = as_seq h b in 
      let x = Lib.Sequence.sub b_seq 0 4 in 
      let y = Lib.Sequence.sub b_seq 4 4 in 
      let z = Lib.Sequence.sub b_seq 8 4 in 
      felem_seq_as_nat x < prime /\ felem_seq_as_nat y < prime /\ felem_seq_as_nat z < prime))

let lemma_to_point_buffer h b = ()


#reset-options "--z3refresh --z3rlimit 100" 
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
  (ensures fun h0 _ h1 -> modifies3 p q tempBuffer h0 h1 /\ 
    (
      let p1 = as_seq h1 p in let q1 = as_seq h1 q in 
      let pN, qN = Hacl.Spec.P256.Ladder.montgomery_ladder_step_swap (as_seq h0 p) (as_seq h0 q) (as_seq h0 scalar) (uint_v i) in 
      pN == p1 /\ qN == q1 /\

      as_nat h1 (gsub p (size 0) (size 4)) < prime /\ 
      as_nat h1 (gsub p (size 4) (size 4)) < prime /\
      as_nat h1 (gsub p (size 8) (size 4)) < prime /\
	     
      as_nat h1 (gsub q (size 0) (size 4)) < prime /\  
      as_nat h1 (gsub q (size 4) (size 4)) < prime /\
      as_nat h1 (gsub q (size 8) (size 4)) < prime
    )
  )

val lemma_test: h: mem -> r0: point -> 
  Lemma 
  (requires (
     let x = Lib.Sequence.sub (as_seq h r0) 0 4 in 
    let y = Lib.Sequence.sub (as_seq h r0) 4 4 in
    let z = Lib.Sequence.sub (as_seq h r0) 8 4 in 
    felem_seq_as_nat x < prime /\ felem_seq_as_nat y < prime /\ felem_seq_as_nat z < prime))
  (ensures 
    (
      as_nat h (gsub r0 (size 0) (size 4)) < prime /\ 
      as_nat h (gsub r0 (size 4) (size 4)) < prime /\
      as_nat h (gsub r0 (size 8) (size 4)) < prime)
  )

let lemma_test h r0 = ()


let montgomery_ladder_step #buf_type r0 r1 tempBuffer scalar i = 
    let h0 = ST.get() in 
    
  let bit0 = (size 255) -. i in 
  let bit = scalar_bit scalar bit0 in 

  cswap bit r0 r1; 
    let h1 = ST.get () in 
  montgomery_ladder_step1 r0 r1 tempBuffer; 
   let h2 = ST.get() in 
  cswap bit r0 r1; 
  let h3 = ST.get() in 

  lemma_to_point_buffer h0 r0;
  lemma_to_point_buffer h0 r1;
  lemma_step i; 

  assert(let pN, qN = Hacl.Spec.P256.Ladder.montgomery_ladder_step_swap (as_seq h0 r0) (as_seq h0 r1) (as_seq h0 scalar) (uint_v i) in Lib.Sequence.equal pN (as_seq h3 r0));

  assert(
    let x = Lib.Sequence.sub (as_seq h3 r0) 0 4 in 
    let y = Lib.Sequence.sub (as_seq h3 r0) 4 4 in
    let z = Lib.Sequence.sub (as_seq h3 r0) 8 4 in 
    felem_seq_as_nat x < prime /\ felem_seq_as_nat y < prime /\ felem_seq_as_nat z < prime
 );

   lemma_test h3 r0; 
   
   assert(let pN, qN = 
     Hacl.Spec.P256.Ladder.montgomery_ladder_step_swap (as_seq h0 r0) (as_seq h0 r1) (as_seq h0 scalar) (uint_v i) in Lib.Sequence.equal qN (as_seq h3 r1));
   assert(
       let x = Lib.Sequence.sub (as_seq h3 r1) 0 4 in 
       let y = Lib.Sequence.sub (as_seq h3 r1) 4 4 in
       let z = Lib.Sequence.sub (as_seq h3 r1) 8 4 in 
      felem_seq_as_nat x < prime /\ felem_seq_as_nat y < prime /\ felem_seq_as_nat z < prime
 );

   lemma_test h3 r1; 

   assert(
      as_nat h3 (gsub r0 (size 0) (size 4)) < prime /\ 
      as_nat h3 (gsub r0 (size 4) (size 4)) < prime /\
      as_nat h3 (gsub r0 (size 8) (size 4)) < prime /\
	     
      as_nat h3 (gsub r1 (size 0) (size 4)) < prime /\  
      as_nat h3 (gsub r1 (size 4) (size 4)) < prime /\
      as_nat h3 (gsub r1 (size 8) (size 4)) < prime);
  modifies2_is_modifies3 r0 r1 tempBuffer h0 h1;
  modifies2_is_modifies3 r0 r1 tempBuffer h2 h3;
  assert(modifies3 r0 r1 tempBuffer h0 h1);
  assert(modifies3 r0 r1 tempBuffer h1 h2);
  assert(modifies3 r0 r1 tempBuffer h2 h3);
  assert(modifies3 r0 r1 tempBuffer h0 h2);
  assert(modifies3 r0 r1 tempBuffer h0 h3) 


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
  (ensures fun h0 _ h1 -> modifies3 p q tempBuffer h0 h1 /\
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

  modifies0_is_modifies3 p q tempBuffer h0 h0;

  [@inline_let]
  let spec_ml h0 = _ml_step (as_seq h0 scalar) in 

  [@inline_let] 
  let acc (h:mem) : GTot (tuple2 point_nat point_nat) = 
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
      assert(modifies3 p q tempBuffer h0 h2);
      montgomery_ladder_step p q tempBuffer scalar i;  
      let h3 = ST.get() in 
      assert(modifies3 p q tempBuffer h2 h3);
      assert(modifies3 p q tempBuffer h0 h3);

      assert(
	let p1 = as_seq h3 p in 
	let q1 = as_seq h3 q in 
        let pN, qN = Hacl.Spec.P256.Ladder.montgomery_ladder_step_swap 
	(as_seq h2 p) (as_seq h2 q) (as_seq h2 scalar) (uint_v i) in 
	pN == p1 /\ qN == q1);

       assert(acc h3 == _ml_step (as_seq h2 scalar) (uint_v i) (acc h2));
       Lib.LoopCombinators.unfold_repeati 256 (spec_ml h0) (acc h0) (uint_v i))

val zero_buffer: p: point -> 
  Stack unit
    (requires fun h -> live h p)
    (ensures fun h0 _ h1 ->     
      modifies (loc p) h0 h1 /\
      (
	let k = Lib.Sequence.create 12 (u64 0) in 
	as_nat h1 (gsub p (size 0) (size 4)) == 0 /\ 
	as_nat h1 (gsub p (size 4) (size 4)) == 0 /\
	as_nat h1 (gsub p (size 8) (size 4)) == 0 /\
	Lib.Sequence.equal (as_seq h1 p) k
    )
  )

let zero_buffer p = 
    let h0 = ST.get() in 
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
  upd p (size 11) (u64 0);
    let h1 = ST.get() in 
  assert(Lib.Sequence.equal (as_seq h1 p) (Lib.Sequence.create 12 (u64 0)))


val lemma_point_to_domain: h0: mem -> h1: mem ->  p: point -> result: point ->  Lemma
   (requires (point_x_as_nat h0 p < prime /\ point_y_as_nat h0 p < prime /\ point_z_as_nat h0 p < prime /\
       point_x_as_nat h1 result == toDomain_ (point_x_as_nat h0 p) /\
       point_y_as_nat h1 result == toDomain_ (point_y_as_nat h0 p) /\
       point_z_as_nat h1 result == toDomain_ (point_z_as_nat h0 p) 
     )
   )
   (ensures (fromDomainPoint(point_prime_to_coordinates (as_seq h1 result)) == point_prime_to_coordinates (as_seq h0 p)))

let lemma_point_to_domain h0 h1 p result = 
  let x0, y0, z0 = point_x_as_nat h0 p, point_y_as_nat h0 p, point_z_as_nat h0 p in 
  let (x, y, z) = point_prime_to_coordinates (as_seq h1 result) in 
  assert(x == toDomain_ x0);
  assert(y == toDomain_ y0);
  assert(z == toDomain_ z0);
  
  let (x3, y3, z3) = fromDomainPoint (x, y, z) in 
  assert(x3 == fromDomain_ x /\ y3 == fromDomain_ y /\ z3 == fromDomain_ z);
  assert(x3 == fromDomain_ (toDomain_ x0) /\ y3 == fromDomain_ (toDomain_ y0) /\ z3 == fromDomain_ (toDomain_ z0))

val lemma_pif_to_domain: h: mem ->  p: point -> Lemma
  (requires (point_x_as_nat h p == 0 /\ point_y_as_nat h p == 0 /\ point_z_as_nat h p == 0))
  (ensures (fromDomainPoint (point_prime_to_coordinates (as_seq h p)) == point_prime_to_coordinates (as_seq h p)))

let lemma_pif_to_domain h p = 
  let (x, y, z) = point_prime_to_coordinates (as_seq h p) in 
  let (x3, y3, z3) = fromDomainPoint (x, y, z) in 
  assert(x == 0 /\ y == 0 /\ z == 0);
  assert(x3 == fromDomain_ x /\ y3 == fromDomain_ y /\ z3 == fromDomain_ z);
  lemmaFromDomain x;
  lemmaFromDomain y;
  lemmaFromDomain z;
  admit()


val lemma_coord: h3: mem -> q: point -> Lemma (
   let (r0, r1, r2) = fromDomainPoint(point_prime_to_coordinates (as_seq h3 q)) in 
	let xD = fromDomain_ (point_x_as_nat h3 q) in 
	let yD = fromDomain_ (point_y_as_nat h3 q) in 
	let zD = fromDomain_ (point_z_as_nat h3 q) in 
    r0 == xD /\ r1 == yD /\ r2 == zD)	

let lemma_coord h3 q = ()

val lemma_modifies3_ : h0: mem -> h1: mem -> p: point -> result: point ->  tempBuffer: lbuffer uint64 (size 100) ->  Lemma 
  (modifies3 p result tempBuffer h0 h1 ==>  modifies (loc p |+| loc result |+| loc tempBuffer) h0 h1)

let lemma_modifies3_ h0 h1 p result tempBuffer = ()

val scalarMultiplicationL: p: point -> result: point -> 
  scalar: lbuffer uint8 (size 32) -> 
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
    modifies3 p result tempBuffer h0 h1 /\ 
    modifies (loc p |+| loc result |+| loc tempBuffer) h0 h1 /\
    (
      let x3, y3, z3 = point_x_as_nat h1 result, point_y_as_nat h1 result, point_z_as_nat h1 result in 
      let (xN, yN, zN) = scalar_multiplication (as_seq h0 scalar) (point_prime_to_coordinates (as_seq h0 p)) in 
      x3 == xN /\ y3 == yN /\ z3 == zN 
  )
) 


let scalarMultiplicationL p result scalar tempBuffer  = 
    let h0 = ST.get() in 
  let q = sub tempBuffer (size 0) (size 12) in 
  zero_buffer q;
    let h1 = ST.get() in 
    modifies1_is_modifies3 p result tempBuffer h0 h1;
    assert(modifies3 p result tempBuffer h0 h1); 
  let buff = sub tempBuffer (size 12) (size 88) in 
  pointToDomain p result;
    let h2 = ST.get() in 
      modifies2_is_modifies3 p result tempBuffer h1 h2;
      assert(modifies3 p result tempBuffer h1 h2); 
  montgomery_ladder q result scalar buff;
    let h3 = ST.get() in 
    lemma_point_to_domain h0 h2 p result;
    lemma_pif_to_domain h2 q;
    assert(modifies3 p result tempBuffer h2 h3); 
  norm q result buff; 
    let h4 = ST.get() in 
      lemma_coord h3 q;
    let h4 = ST.get() in 
    modifies2_is_modifies3 p result tempBuffer h3 h4;
    assert(modifies3 p result tempBuffer h3 h4);

    assert(modifies3 p result tempBuffer h0 h2);
    assert(modifies3 p result tempBuffer h2 h4);
    assert(modifies3 p result tempBuffer h0 h4);
    lemma_modifies3_ h0 h4 p result tempBuffer


val scalarMultiplicationI: p: point -> result: point -> 
  scalar: ilbuffer uint8 (size 32) -> 
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
    modifies3 p result tempBuffer h0 h1 /\ 
    modifies (loc p |+| loc result |+| loc tempBuffer) h0 h1 /\
    (
      let x3, y3, z3 = point_x_as_nat h1 result, point_y_as_nat h1 result, point_z_as_nat h1 result in 
      let (xN, yN, zN) = scalar_multiplication (as_seq h0 scalar) (point_prime_to_coordinates (as_seq h0 p)) in 
      x3 == xN /\ y3 == yN /\ z3 == zN 
  )
) 


let scalarMultiplicationI p result scalar tempBuffer  = 
  let h0 = ST.get() in 
  let q = sub tempBuffer (size 0) (size 12) in 
  zero_buffer q;
    let h1 = ST.get() in 
    modifies1_is_modifies3 p result tempBuffer h0 h1;
    assert(modifies3 p result tempBuffer h0 h1); 
  let buff = sub tempBuffer (size 12) (size 88) in 
  pointToDomain p result;
    let h2 = ST.get() in 
      modifies2_is_modifies3 p result tempBuffer h1 h2;
      assert(modifies3 p result tempBuffer h1 h2); 
  montgomery_ladder q result scalar buff;
    let h3 = ST.get() in 
    lemma_point_to_domain h0 h2 p result;
    lemma_pif_to_domain h2 q;
    assert(modifies3 p result tempBuffer h2 h3); 
  norm q result buff; 
    let h4 = ST.get() in 
      lemma_coord h3 q;
    let h4 = ST.get() in 
    modifies2_is_modifies3 p result tempBuffer h3 h4;
    assert(modifies3 p result tempBuffer h3 h4);

    assert(modifies3 p result tempBuffer h0 h2);
    assert(modifies3 p result tempBuffer h2 h4);
    assert(modifies3 p result tempBuffer h0 h4);
    lemma_modifies3_ h0 h4 p result tempBuffer


let scalarMultiplication #buf_type p result scalar tempBuffer = 
  match buf_type with 
  |MUT -> scalarMultiplicationL p result scalar tempBuffer 
  |IMMUT -> scalarMultiplicationI p result scalar tempBuffer



val uploadBasePoint: p: point -> Stack unit 
  (requires fun h -> live h p)
  (ensures fun h0 _ h1 -> modifies1 p h0 h1 /\ 
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
    let h1 = ST.get() in 
    modifies1_is_modifies3 p result tempBuffer h0 h1;
    assert(modifies3 p result tempBuffer h0 h1); 
  let buff = sub tempBuffer (size 12) (size 88) in 
  pointToDomain p result;
    let h2 = ST.get() in 
      modifies2_is_modifies3 p result tempBuffer h1 h2;
      assert(modifies3 p result tempBuffer h1 h2); 
  montgomery_ladder q result scalar buff;
  copy_point q result;  
    let h3 = ST.get() in 
    lemma_point_to_domain h0 h2 p result;
    lemma_pif_to_domain h2 q;
    assert(modifies3 p result tempBuffer h2 h3);
    
    assert(
      point_x_as_nat h2 result == toDomain_ (point_x_as_nat h0 p) /\
      point_y_as_nat h2 result == toDomain_ (point_y_as_nat h0 p) /\
      point_z_as_nat h2 result == toDomain_ (point_z_as_nat h0 p));

    assert(	
      let p1 = fromDomainPoint(point_prime_to_coordinates (as_seq h3 q)) in 
      let rN, _ = montgomery_ladder_spec (as_seq h0 scalar) ((0, 0, 0),  point_prime_to_coordinates (as_seq h0 p)) in rN == p1)


let secretToPublic result scalar tempBuffer = 
  push_frame(); 
       let basePoint = create (size 12) (u64 0) in 
       let h0 = ST.get() in 
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
      let h0 = ST.get() in 
    uploadBasePoint basePoint;
      let q = sub tempBuffer (size 0) (size 12) in 
      let buff = sub tempBuffer (size 12) (size 88) in 
    zero_buffer q; 
      let h1 = ST.get() in 
      lemma_pif_to_domain h1 q; 
    montgomery_ladder q basePoint scalar buff; 
    copy_point q result;
  pop_frame()  



inline_for_extraction noextract
val y_2: y: felem -> r: felem -> Stack unit
  (requires fun h -> as_nat h y < prime /\  live h y /\ live h r /\ eq_or_disjoint y r)
  (ensures fun h0 _ h1 -> modifies1 r h0 h1 /\  as_nat h1 r == toDomain_ ((as_nat h0 y) * (as_nat h0 y) % prime))

let y_2 y r = 
    let h0 = ST.get() in 
  toDomain y r;
    let h1 = ST.get() in 
    assert(as_nat h1 r == toDomain_ (as_nat h0 y));
  montgomery_multiplication_buffer r r r;
    let h2 = ST.get() in  
    assert(as_nat h2 r == toDomain_ ((as_nat h0 y) *  (as_nat h0 y) % prime))

inline_for_extraction noextract
val upload_p256_point_on_curve_constant: x: felem -> Stack unit
  (requires fun h -> live h x)
  (ensures fun h0 _ h1 -> modifies1 x h0 h1 /\ 
    as_nat h1 x == toDomain_ (41058363725152142129326129780047268409114441015993725554835256314039467401291) /\
    as_nat h1 x < prime
 )

let upload_p256_point_on_curve_constant x = 
  upd x (size 0) (u64 15608596021259845087);
  upd x (size 1) (u64 12461466548982526096);
  upd x (size 2) (u64 16546823903870267094);
  upd x (size 3) (u64 15866188208926050356);
    let h1 = ST.get() in 
  assert_norm (
    15608596021259845087 + 12461466548982526096 * pow2 64 + 
    16546823903870267094 * pow2 64 * pow2 64 + 
    15866188208926050356 * pow2 64 * pow2 64 * pow2 64 == (41058363725152142129326129780047268409114441015993725554835256314039467401291 * pow2 256) % prime);
  assert(as_nat h1 x == toDomain_ (41058363725152142129326129780047268409114441015993725554835256314039467401291))

val lemma_xcube: x_: nat {x_ < prime} -> Lemma 
  (((x_ * x_ * x_ % prime) - (3 * x_ % prime)) % prime == (x_ * x_ * x_ - 3* x_) % prime)

let lemma_xcube x_ = 
  lemma_mod_add_distr (- (3 * x_ % prime)) (x_ * x_ * x_) prime;
  lemma_mod_sub_distr (x_ * x_ * x_ ) (3 * x_) prime

val lemma_xcube2: x_ : nat {x_ < prime} -> Lemma 
  (toDomain_ ((((((x_ * x_ * x_) - (3 * x_)) % prime)) + 41058363725152142129326129780047268409114441015993725554835256314039467401291) % prime) == 
    toDomain_ ((x_ * x_ * x_ - 3 * x_ + 41058363725152142129326129780047268409114441015993725554835256314039467401291) % prime))

let lemma_xcube2 x_ = 
  lemma_mod_add_distr 41058363725152142129326129780047268409114441015993725554835256314039467401291 ((x_ * x_ * x_) - (3 * x_)) prime;
  assert(((((x_ * x_ * x_) - (3 * x_)) % prime) + 41058363725152142129326129780047268409114441015993725554835256314039467401291) % prime == (x_ * x_ * x_ - 3 * x_ + 41058363725152142129326129780047268409114441015993725554835256314039467401291) % prime)

inline_for_extraction noextract
val xcube_minus_x: x: felem ->r: felem -> Stack unit 
  (requires fun h -> as_nat h x < prime /\ live h x  /\ live h r /\ eq_or_disjoint x r)
  (ensures fun h0 _ h1 -> 
    modifies1 r h0 h1 /\
    (
      let x_ = as_nat h0 x in 
      as_nat h1 r =  toDomain_((x_ * x_ * x_ - 3 * x_ + 41058363725152142129326129780047268409114441015993725554835256314039467401291) % prime))
  )

let xcube_minus_x x r = 
  push_frame();
    let xToDomainBuffer = create (size 4) (u64 0) in 
    let minusThreeXBuffer = create (size 4) (u64 0) in 
    let p256_constant = create (size 4) (u64 0) in 
    let h0 = ST.get() in 
  toDomain x xToDomainBuffer;
    let h1 = ST.get() in 
    assert(as_nat h1 xToDomainBuffer == toDomain_ (as_nat h0 x));
  montgomery_multiplication_buffer xToDomainBuffer xToDomainBuffer r;
    let h2 = ST.get() in 
    assert(as_nat h2 r == toDomain_ ((as_nat h0 x) * (as_nat h0 x) % prime));
  montgomery_multiplication_buffer r xToDomainBuffer r;
    let h3 = ST.get() in 
    lemma_mod_mul_distr_l ((as_nat h0 x) * (as_nat h0 x)) (as_nat h0 x) prime;
    assert(as_nat h3 r == toDomain_ ((as_nat h0 x) * (as_nat h0 x) * (as_nat h0 x) % prime));
  multByThree xToDomainBuffer minusThreeXBuffer;
    let h4 = ST.get() in 
    assert(as_nat h4 minusThreeXBuffer == toDomain_ (3 * (as_nat h0 x) % prime));
  p256_sub r minusThreeXBuffer r;
    let h5 = ST.get() in 
  upload_p256_point_on_curve_constant p256_constant;
    let h6 = ST.get() in 
  p256_add r p256_constant r;
    let h7 = ST.get() in 
  pop_frame(); 
  
    let x_ = as_nat h0 x in 
    assert_norm (41058363725152142129326129780047268409114441015993725554835256314039467401291 < prime);
    lemma_xcube x_;
    lemma_mod_add_distr 41058363725152142129326129780047268409114441015993725554835256314039467401291 ((x_ * x_ * x_) - (3 * x_)) prime;
    lemma_xcube2 x_



val lemma_modular_multiplication_p256_2: a: nat{a < prime} -> b: nat{b < prime} -> 
  Lemma 
  (a * pow2 256 % prime = b * pow2 256 % prime  <==> a == b)

(*If k a ≡ k b (mod n) and k is coprime with n, then a ≡ b (mod n) *)
(* if a ≡ b (mod n), then k a ≡ k b (mod n) for any integer k (compatibility with scaling) *)
(*p = 2^256 - 2^224 + 2^192 + 2^96 - 1 

gcd(2^256, p) = 1*)

let lemma_modular_multiplication_p256_2 a b = admit()


val lemma_modular_multiplication_p256_2_d: a: nat{a < prime} -> b: nat {b < prime} -> 
  Lemma 
    (toDomain_ a = toDomain_ b <==> a == b)

let lemma_modular_multiplication_p256_2_d a b = 
   lemmaToDomain a;
     assert(toDomain_ a = a * pow2 256 % prime);
   lemmaToDomain b;
     assert(toDomain_ b = b * pow2 256 % prime);
   lemma_modular_multiplication_p256_2 a b;
     assert(toDomain_ a = toDomain_ b ==> a == b)


let isPointAtInfinity p =  
  let z0 = index p (size 8) in 
  let z1 = index p (size 9) in 
  let z2 = index p (size 10) in 
  let z3 = index p (size 11) in 
  let z0_zero = eq_0_u64 z0 in 
  let z1_zero = eq_0_u64 z1 in 
  let z2_zero = eq_0_u64 z2 in 
  let z3_zero = eq_0_u64 z3 in 
  z0_zero && z1_zero && z2_zero && z3_zero


let isPointOnCurve p = 
   push_frame(); 
     let y2Buffer = create (size 4) (u64 0) in 
     let xBuffer = create (size 4) (u64 0) in 
       let h0 = ST.get() in 
     let x = sub p (size 0) (size 4) in 
     let y = sub p (size 4) (size 4) in 
     y_2 y y2Buffer;
     xcube_minus_x x xBuffer;
       let h1 = ST.get() in 
     let r = compare_felem y2Buffer xBuffer in 
     let z = eq_0_u64 r in 
     assert(if uint_v r = pow2 64 -1 then as_nat h1 y2Buffer == as_nat h1 xBuffer else as_nat h1 y2Buffer <> as_nat h1 xBuffer);
     lemma_modular_multiplication_p256_2_d ((as_nat h0 y) * (as_nat h0 y) % prime) 
       (let x_ = as_nat h0 x in (x_ * x_ * x_ - 3 * x_ + 41058363725152142129326129780047268409114441015993725554835256314039467401291) % prime);
     assert(let x_ = as_nat h0 x in 
       if uint_v r = pow2 64 - 1 then   
	  (as_nat h0 y) * (as_nat h0 y) % prime ==  (x_ * x_ * x_ - 3 * x_ + 41058363725152142129326129780047268409114441015993725554835256314039467401291) % prime else 	  
	  (as_nat h0 y) * (as_nat h0 y) % prime <>  (x_ * x_ * x_ - 3 * x_ + 41058363725152142129326129780047268409114441015993725554835256314039467401291) % prime);
     let z = not(eq_0_u64 r) in 
     pop_frame();
     z

