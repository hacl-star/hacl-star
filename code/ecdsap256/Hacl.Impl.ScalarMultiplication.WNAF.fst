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
open Hacl.Impl.P256.MixedPointAdd


open Hacl.Impl.ScalarMultiplication.WNAF.Table.Ext

(* Originally lives in P256.Core *)
(* this piece of code is taken from Hacl.Curve25519 *)
(* changed Endian for Scalar Bit access *)

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

(* I work *)
val scalar_rwnaf : out: lbuffer uint64 (size 104) -> scalar: lbuffer uint8 (size 32) -> 
  Stack unit 
    (requires fun h -> live h out /\ live h scalar)
    (ensures fun h0 _ h1 -> True)


let scalar_rwnaf out scalar = 
  push_frame();

  let in0 = index scalar (size 31) in 
  let windowStartValue =  (logor (u64 1) (logand (to_u64 in0) (dradix_wnaf -! (u64 1))))  in 
  
 let window = create (size 1) windowStartValue in 

 let r = create (size 1) (u64 0) in 
 let r1 = create (size 1) (u64 0) in 

 let h0 = ST.get() in 
 let inv h1 (i:nat) = live h1 window /\ live h1 out in  

  Lib.Loops.for 0ul 51ul inv
    (fun i ->

      let h0 = ST.get() in 

      let wVar : uint64 = index window (size 0) in 
      
      let w = logand wVar  (dradix_wnaf -! (u64 1)) in 
      
      let d = logand wVar (dradix_wnaf -! (u64 1)) -! dradix in 

      let c = sub_borrow_u64 (u64 0) w dradix r in 
      let c1 = sub_borrow_u64 (u64 0) (u64 0) (index r (size 0)) r1 in 
      
      let cAsFlag = (u64 0xffffffff) +! c in 
      let r3 = logand (cmovznz2 (index r (size 0)) (index r1 (size 0)) cAsFlag) (u64 0xff) in 
      
      upd out (size 2 *! i) r3;
      upd out (size 2 *! i +! 1) c;


      let wStart = shift_right (wVar -! d) radix in 
      let w0 = wStart +! (shift_left (scalar_bit scalar ((size 1 +! i) *! radix +! (size 1))) (size 1)) in 
      let w0 = w0 +! (shift_left (scalar_bit scalar ((size 1 +! i) *! radix +! (size 2))) (size 2)) in 
      let w0 = w0 +! (shift_left (scalar_bit scalar ((size 1 +! i) *! radix +! (size 3))) (size 3)) in 
      let w0 = w0 +! (shift_left (scalar_bit scalar ((size 1 +! i) *! radix +! (size 4))) (size 4)) in 
      let w0 = w0 +! (shift_left (scalar_bit scalar ((size 1 +! i) *! radix +! (size 5))) (size 5)) in

      upd window (size 0) w0


    );

    upd out (size 102) (index window (size 0));

pop_frame()



inline_for_extraction
type pointAffine = lbuffer uint64 (size 8)


val loopK: result: pointAffine -> d: uint64 -> point: pointAffine -> j: size_t -> Stack unit 
  (requires fun h -> True)
  (ensures fun h0 _ h1 -> True)

let loopK result d point j = 
  let invK h (k: nat) = True in 
  Lib.Loops.for 0ul 16ul invK
    (fun k -> 
      let mask = eq_mask d (to_u64 k) in 
        eq_mask_lemma d (to_u64 k); 

	(* 
	let lut_cmb_x = const_to_lbuffer (sub points_cmb ((j *! size 16 +! k) *! 8) (size 4)) in 
	let lut_cmb_y = const_to_lbuffer (sub points_cmb ((j *! size 16 +! k) *! 8 +! (size 4)) (size 4)) in *)
	
	let lut_cmb_x = getUInt64 ((j *! size 16 +! k) *! 8) in 
	let lut_cmb_y = getUInt64 ((j *! size 16 +! k) *! 8 +! (size 4))  in

	copy_conditional (sub point (size 0) (size 4)) lut_cmb_x mask;
	copy_conditional (sub point (size 4) (size 4)) lut_cmb_y mask 
    )



val conditional_substraction: result: point -> p: point -> scalar: lbuffer uint8 (size 32) -> 
  tempBuffer: lbuffer uint64 (size 88) ->
  Stack unit 
    (requires fun h -> live h result /\ live h p /\ live h scalar /\ live h tempBuffer)
    (ensures fun h0 _ h1 -> True)


let conditional_substraction result p scalar tempBuffer = 
  push_frame();

  let tempPoint = create (size 12) (u64 0) in 
  let bpMinus = create (size 8) (u64 0) in 
    let bpMinusX = sub bpMinus (size 0) (size 4) in 
    let bpMinusY = sub bpMinus (size 4) (size 4) in 

  (* mask == 0 <==> scalar last bit == 0 *)

  let i0 = index scalar (size 0) in 
  let mask = (u64 0) -. to_u64 (logand i0 (u8 1)) in 

  let bpX = getUInt64 (size 0) in 
  let bpY = getUInt64 (size 4) in 

    copy bpMinusX bpX;
    p256_neg bpY bpMinusY;

  point_add_mixed p bpMinus tempPoint tempBuffer;

  copy_point_conditional_mask_u64_2 result tempPoint mask;

(*   let bpX = const_to_lbuffer (sub points_cmb (size 0) (size 4)) in
    copy bpMinusX bpX;
  let bpY = const_to_lbuffer (sub points_cmb (size 4) (size 4)) in
    p256_neg bpY bpMinusY;

  point_add_mixed p bpMinus tempPoint tempBuffer;

  copy_point_conditional_mask_u64_2 result tempPoint mask;  *)
  


  pop_frame()


(* r = ZZ.random_element(qq)
basePoint = r * EC(gx, gy)
minusBasePoint = (basePoint[0], (Integer(p256 - basePoint[1]) % p256))

baseX, baseY = basePoint.xy()
fakeBP = toFakeAffine((toD(baseX), toD(baseY)))
fakeBP = (fakeBP[0], (p256 - fakeBP[1]) % p256)
x, y, z = norm((fromD(fakeBP[0]), fromD(fakeBP[1]), fromD (1)))

print((minusBasePoint[1] == y))

*)

val scalar_multiplication_cmb:  #buf_type: buftype -> result: point -> 
  scalar: lbuffer_t buf_type uint8 (size 32) -> 
  tempBuffer:  lbuffer uint64 (size 88)  -> 
  Stack unit
  (requires fun h -> True )
  (ensures fun h0 _ h1 -> modifies (loc result |+| loc tempBuffer) h0 h1)


let scalar_multiplication_cmb #buf_type result scalar tempBuffer = 
  push_frame();
    let rnaf2 = create (size 104) (u64 0) in 
    let lut:pointAffine = create (size 8) (u64 0) in 
    let temp4 = sub tempBuffer (size 0) (size 4) in 

    scalar_rwnaf rnaf2 scalar;

    let i = size 1 in 

    let invJ h1 (j:nat) = True in  

    Lib.Loops.for 0ul 26ul invJ (fun j ->
      let d = index rnaf2 (size 2 *! (j *! (size 2) +! i)) in
      let is_neg = (u64 0) -. (index rnaf2 (size 2 *! (j *! (size 2) +! i) +! (size 1))) in 
      let d = shift_right (d -! size 1) (size 1) in 

      loopK lut d lut j;

      let yLut = sub lut (size 4) (size 4) in 
      p256_neg yLut temp4;

      copy_conditional yLut temp4 is_neg;
      point_add_mixed result lut result tempBuffer
    );
     
    let i = size 0 in 

    let invPointDouble h (j: nat) = True in 
    Lib.Loops.for 0ul radix invPointDouble 
    (fun j -> point_double result result tempBuffer);

    Lib.Loops.for 0ul 26ul invJ (fun j ->
      let d = index rnaf2 (size 2 *! (j *! (size 2) +! i)) in 
      let is_neg = (u64 0) -. (index rnaf2 (size 2 *! (j *! (size 2) +! i) +! (size 1))) in 
      let d = shift_right (d -! size 1) (size 1) in 

      loopK lut d lut j;

    	let yLut = sub lut (size 4) (size 4) in 
    	p256_neg yLut temp4;

	
    	copy_conditional yLut temp4  is_neg;
    	point_add_mixed result lut result tempBuffer
    );


    conditional_substraction result result scalar tempBuffer;
  

  pop_frame()
