module Hacl.Impl.ScalarMultiplication.WNAF

open FStar.HyperStack.All
open FStar.HyperStack

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes

open Lib.Buffer

open Lib.IntTypes.Intrinsics
open Hacl.Impl.P256.Q.PrimitivesMasking


open Spec.P256.Definitions
open Hacl.Impl.P256.LowLevel.PrimeSpecific
open Hacl.Impl.P256.PointDouble
open Hacl.Impl.P256.PointAdd
open Hacl.Impl.P256.MixedPointAdd

open Hacl.Impl.ScalarMultiplication.RWNAF


inline_for_extraction noextract
val copy_point: p: point -> result: point -> Stack unit 
  (requires fun h -> live h p /\ live h result /\ disjoint p result) 
  (ensures fun h0 _ h1 -> modifies (loc result) h0 h1 /\ as_seq h1 result == as_seq h0 p)

let copy_point p result = copy result p


val precomputePoints: b: lbuffer uint64 (size 192) -> publicKey: point ->
  tempBuffer: lbuffer uint64 (size 88) -> Stack unit  
  (requires fun h -> True)
  (ensures fun h0 _ h1 -> True)

let precomputePoints b publicKey tempBuffer = 
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

  copy_point publicKey point0;
  point_double point0 point15 tempBuffer;

  point_add point0 point15 point1 tempBuffer;
  point_add point1 point15 point2 tempBuffer;
  point_add point2 point15 point3 tempBuffer;
  point_add point3 point15 point4 tempBuffer;
  point_add point4 point15 point5 tempBuffer;
  point_add point5 point15 point6 tempBuffer;
  point_add point6 point15 point7 tempBuffer;
  point_add point7 point15 point8 tempBuffer;
  point_add point8 point15 point9 tempBuffer;
  point_add point9 point15 point10 tempBuffer;
  point_add point10 point15 point11 tempBuffer;
  point_add point11 point15 point12 tempBuffer;
  point_add point12 point15 point13 tempBuffer;
  point_add point13 point15 point14 tempBuffer;
  point_add point14 point15 point15 tempBuffer


val scalar_bit:
    s:lbuffer_t MUT uint8 (size 32)
  -> n:size_t{v n < 256}
  -> Stack uint64
    (requires fun h0 -> live h0 s)
    (ensures  fun h0 r h1 -> h0 == h1 /\  v r <= 1)

let scalar_bit s n =
  let h0 = ST.get () in
  mod_mask_lemma ((Lib.Sequence.index (as_seq h0 s) (31 - v n / 8)) >>. (n %. 8ul)) 1ul;
  assert_norm (1 = pow2 1 - 1);
  assert (v (mod_mask #U8 #SEC 1ul) == v (u8 1)); 
  to_u64 ((s.(31ul -. n /. 8ul) >>. (n %. 8ul)) &. u8 1)



inline_for_extraction noextract
let dradix_wnaf = (u64 64)
inline_for_extraction noextract
let dradix = (u64 32)
inline_for_extraction noextract
let radix = (u64 5)


inline_for_extraction
type pointAffine = lbuffer uint64 (size 8)


val loopK: result: pointAffine -> d: uint64 -> point: pointAffine
  -> precomputedPoints: lbuffer uint64 (size 192) 
  -> Stack unit 
  (requires fun h -> True)
  (ensures fun h0 _ h1 -> True)

let loopK result d point precomputedPoints = 
  let invK h (k: nat) = True in 
  Lib.Loops.for 0ul 16ul invK
    (fun k -> 
      let mask = eq_mask d (to_u64 k) in 
        eq_mask_lemma d (to_u64 k);
	
	let precomputedPoint = sub precomputedPoints (size 12 *! k) (size 12) in 
	copy_point_conditional_mask_u64_2 result precomputedPoint mask
    )



val conditional_substraction: result: point -> p: point -> scalar: lbuffer uint8 (size 32)
  -> precomputedPoints: lbuffer uint64 (size 192) 
  -> tempBuffer: lbuffer uint64 (size 88) ->
  Stack unit 
    (requires fun h -> live h result /\ live h p /\ live h scalar /\ live h tempBuffer)
    (ensures fun h0 _ h1 -> True)


let conditional_substraction result p scalar precomputedPoints tempBuffer = 
  push_frame();

  let bpMinus = create (size 12) (u64 0) in 
    let bpMinusY = sub bpMinus (size 4) (size 4) in 
    

  (* mask == 0 <==> scalar last bit == 0 *)

  let i0 = index scalar (size 31) in 
  let mask = lognot((u64 0) -. to_u64 (logand i0 (u8 1))) in 

  copy_point (sub precomputedPoints (size 0) (size 12)) bpMinus; 
  p256_neg bpMinusY bpMinusY;

  point_add p bpMinus bpMinus tempBuffer;

  copy_point_conditional_mask_u64_2 result bpMinus mask;
  pop_frame()


val scalar_multiplication_cmb:  #buf_type: buftype -> result: point -> 
  scalar: lbuffer_t buf_type uint8 (size 32) -> 
  pk: point ->
  tempBuffer:  lbuffer uint64 (size 88)  -> 
  Stack unit
  (requires fun h -> True )
  (ensures fun h0 _ h1 -> modifies (loc result |+| loc tempBuffer) h0 h1)


let scalar_multiplication_cmb #buf_type result scalar pk tempBuffer = 
  push_frame();
    let rnaf2 = create (size 104) (u64 0) in 
    let lut:pointAffine = create (size 12) (u64 0) in 
    let temp4 = sub tempBuffer (size 0) (size 4) in 

    let precomputedPoints = create (size 192) (u64 0) in 
    scalar_rwnaf rnaf2 scalar;
    precomputePoints precomputedPoints pk tempBuffer;

    let d = shift_right (index rnaf2 (size 102) -. (u64 1)) (size 1) in 

    let invK h1 (j:nat) = True in  

    Lib.Loops.for 0ul 16ul invK
    (fun j -> 
      let mask = eq_mask d (to_u64 j) in 
        eq_mask_lemma d (to_u64 j);
	
	let precomputedPoint = sub precomputedPoints (size 12 *! j) (size 12) in 
	copy_point_conditional_mask_u64_2 result precomputedPoint mask
    );


    Lib.Loops.for 0ul 51ul invK (fun j ->
      let i = size 50 -. j in 

      let invPointDouble h (j: nat) = True in 
	Lib.Loops.for 0ul radix invPointDouble 
	  (fun j -> point_double result result tempBuffer);

      


      let d = index rnaf2 (size 2 *! i) in
      let is_neg = index rnaf2 (size 2 *! i +! (size 1)) in 
      let d = shift_right (d -! size 1) (size 1) in 

      loopK lut d lut precomputedPoints;

      let yLut = sub lut (size 4) (size 4) in 
      p256_neg yLut temp4;
      copy_conditional yLut temp4 is_neg;
      point_add result lut result tempBuffer
      
    );



    conditional_substraction result result scalar precomputedPoints tempBuffer;
  

  pop_frame()
