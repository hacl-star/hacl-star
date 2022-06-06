module Hacl.Impl.EC.ScalarMultiplication.WNAF

open FStar.HyperStack.All
open FStar.HyperStack

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes

open Lib.Buffer

open Spec.ECC.Curves
open Spec.ECC


open Hacl.Impl.EC.LowLevel
open Hacl.Spec.EC.Definition


open Hacl.Spec.MontgomeryMultiplication

open FStar.Mul



(*  https://www.usenix.org/system/files/conference/usenixsecurity18/sec18-alam.pdf
 *)

val scalar_bit:
    s:lbuffer_t MUT uint8 (size 32)
  -> n:size_t{v n < 256}
  -> Stack uint64
    (requires fun h0 -> live h0 s)
    (ensures  fun h0 r h1 -> h0 == h1 /\ v r <= 1)

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

open FStar.Mul

#set-options "--z3rlimit 200" 

val subborrow_u64: x:uint64 -> y:uint64 -> r:lbuffer uint64 (size 1) ->
  Stack uint64
    (requires fun h -> live h r)
    (ensures  fun h0 c h1 ->
      modifies1 r h0 h1 /\
      (let r = Seq.index (as_seq h1 r) 0 in
       v r - v c * pow2 64 == v x - v y))

let subborrow_u64 x y r = 
  let x1 = to_u128 x -. to_u128 y in 
  let x2 = logand x1 (u128 0xffffffffffffffff) in 
  let x3 = shift_right x1 (size 64) in 

  upd r (size 0) (to_u64 x2);
  (u64 0) -. (to_u64 x3)


inline_for_extraction noextract
val cmovznz2: #t:inttype{unsigned t} -> #l:secrecy_level ->
  a: uint_t t l  -> b: uint_t t l -> mask: uint_t t l -> Tot (r: uint_t t l)

let cmovznz2 a b mask = 
  logor (logand a mask) (logand b (lognot mask))



val scalar_rwnaf : out: lbuffer uint64 (size 104) -> scalar: lbuffer uint8 (size 32) -> 
  Stack unit 
    (requires fun h -> live h out /\ live h scalar)
    (ensures fun h0 _ h1 -> True)


let scalar_rwnaf out scalar = 
  push_frame();

  let in0 = to_u64 (index scalar (size 31)) in 
  let mask = dradix_wnaf -! (u64 1) in 
  let windowStartValue = logor (u64 1) (logand in0 mask) in 
  
  let window = create (size 1) windowStartValue in 

  let r = create (size 1) (u64 0) in 
  let r1 = create (size 1) (u64 0) in 

  let h0 = ST.get() in 
  let inv h1 (i:nat) = live h1 window /\ live h1 out in  


  admit();

  Lib.Loops.for 0ul 50ul inv
    (fun i ->
  
      let h0 = ST.get() in 
      let wVar = to_u64 (index window (size 0)) in 
      let w = logand wVar mask in 
      let c = subborrow_u64 w dradix r in 

      let r0 = index r (size 0) in 
      let r2 = (u64 0) -. index r (size 0) in 


      let cAsFlag = (u64 0) -. c in 
      let r3 = cmovznz2 r2 r0 cAsFlag in 

      upd out (size 2 *! i) r3;
      upd out (size 2 *! i +! size 1) cAsFlag;


      let d = w -! dradix in 
      let wStart = shift_right (wVar -! d) radix in 

      let w0 = wStart +! (shift_left (scalar_bit scalar ((size 1 +! i) *! radix +! (size 1))) (size 1)) in 
      let w0 = w0 +! (shift_left (scalar_bit scalar ((size 1 +! i) *! radix +! (size 2))) (size 2)) in 
      let w0 = w0 +! (shift_left (scalar_bit scalar ((size 1 +! i) *! radix +! (size 3))) (size 3)) in 
      let w0 = w0 +! (shift_left (scalar_bit scalar ((size 1 +! i) *! radix +! (size 4))) (size 4)) in 
      let w0 = w0 +! (shift_left (scalar_bit scalar ((size 1 +! i) *! radix +! (size 5))) (size 5)) in

      upd window (size 0) w0
  );

  let i = size 50 in 
  
  let wVar = index window (size 0) in 
  let w = logand wVar mask in 
  let c = subborrow_u64 w dradix r in 

  let r0 = index r (size 0) in 
  let r2 = (u64 0) -. index r (size 0) in 

  let cAsFlag = (u64 0) -. c in 
  let r3 = cmovznz2 r2 r0 cAsFlag in 

  upd out (size 2 *! i) r3;
  upd out (size 2 *! i +! size 1) cAsFlag;

  let d = w -! dradix in 

  let wStart = shift_right (wVar -! d) radix in 
  upd out (size 102) wStart; 

  pop_frame()



inline_for_extraction
type pointAffine = lbuffer uint64 (size 8)

assume val getUInt64: index: size_t {v index < 3456 - 4} -> Stack (lbuffer uint64 (size 4))
  (requires fun h -> True)
  (ensures fun h0 _ h1 -> modifies0 h0 h1)

[@CInline]
val copy_conditional: #c: curve -> out: felem c -> x: felem c -> mask: uint64{uint_v mask = 0 \/ uint_v mask = pow2 64 - 1} -> Stack unit 
  (requires fun h -> live h out /\ live h x)
  (ensures fun h0 _ h1 -> modifies (loc out) h0 h1 (* /\ 
    (if uint_v mask = 0 then as_seq h1 out == as_seq h0 out else as_seq h1 out == as_seq h0 x) /\
    (if uint_v mask = 0 then as_nat h1 out == as_nat h0 out else as_nat h1 out == as_nat h0 x)
  ) 
*))

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

  let r_0 = logxor out_0 (logand mask (logxor out_0 x_0)) in 
  let r_1 = logxor out_1 (logand mask (logxor out_1 x_1)) in 
  let r_2 = logxor out_2 (logand mask (logxor out_2 x_2)) in 
  let r_3 = logxor out_3 (logand mask (logxor out_3 x_3)) in 

  (* lemma_xor_copy_cond out_0 x_0 mask;
  lemma_xor_copy_cond out_1 x_1 mask;
  lemma_xor_copy_cond out_2 x_2 mask;
  lemma_xor_copy_cond out_3 x_3 mask; *)

  upd out (size 0) r_0;
  upd out (size 1) r_1;
  upd out (size 2) r_2;
  upd out (size 3) r_3 (*;
    let h1 = ST.get() in 

  lemma_eq_funct_ (as_seq h1 out) (as_seq h0 out);
  lemma_eq_funct_ (as_seq h1 out) (as_seq h0 x) *)



val loopK:  result: pointAffine -> d: uint64 -> point: pointAffine -> j: size_t -> Stack unit 
  (requires fun h -> True)
  (ensures fun h0 _ h1 -> True)

let loopK result d point j = 
  let invK h (k: nat) = True in 
  Lib.Loops.for 0ul 16ul invK (fun k -> 
 
    let mask = eq_mask d (to_u64 k) in 
    eq_mask_lemma d (to_u64 k); 
    

    let lut_cmb_x = getUInt64 ((j *! size 16 +! k) *! 8) in 
    let lut_cmb_y = getUInt64 ((j *! size 16 +! k) *! 8 +! (size 4))  in

    copy_conditional #P256 (sub point (size 0) (size 4)) lut_cmb_x mask;
    copy_conditional #P256 (sub point (size 4) (size 4)) lut_cmb_y mask)


open Lib.IntTypes.Intrinsics

inline_for_extraction noextract
val sub4_0: y:felem P256 -> result: felem P256 -> 
  Stack uint64
    (requires fun h -> live h y /\ live h result /\ eq_or_disjoint y result)
    (ensures fun h0 c h1 -> modifies1 result h0 h1 /\ v c <= 1 /\ as_nat P256 h1 result - v c * pow2 256 == 0 - as_nat P256 h0 y)

let sub4_0 y result = 
  let h0 = ST.get() in 
  
  let r0 = sub result (size 0) (size 1) in 
  let r1 = sub result (size 1) (size 1) in 
  let r2 = sub result (size 2) (size 1) in 
  let r3 = sub result (size 3) (size 1) in 
      
  let cc = sub_borrow_u64 (u64 0) (u64 0) y.(size 0) r0 in 
  let cc = sub_borrow_u64 cc (u64 0) y.(size 1) r1 in 
  let cc = sub_borrow_u64 cc (u64 0) y.(size 2) r2 in 
  let cc = sub_borrow_u64 cc (u64 0) y.(size 3) r3 in 
    
    assert(let r1_0 = as_seq h0 r1 in let r0_ = as_seq h0 result in Seq.index r0_ 1 == Seq.index r1_0 0);
    assert(let r2_0 = as_seq h0 r2 in let r0_ = as_seq h0 result in Seq.index r0_ 2 == Seq.index r2_0 0);
    assert(let r3_0 = as_seq h0 r3 in let r0_ = as_seq h0 result in Seq.index r0_ 3 == Seq.index r3_0 0);

    assert_norm (pow2 64 * pow2 64 = pow2 128);
    assert_norm (pow2 64 * pow2 64 * pow2 64 = pow2 192);
    assert_norm (pow2 64 * pow2 64 * pow2 64 * pow2 64 = pow2 256);
    
  cc


inline_for_extraction noextract
val add4_variables_void: x: felem P256 -> cin: uint64 {uint_v cin <=1} ->  y0: uint64 -> y1: uint64 -> y2: uint64 
  -> y3: uint64 -> 
  result: felem P256 -> 
  Stack unit
    (requires fun h -> live h x /\ live h result /\ eq_or_disjoint x result )
    (ensures fun h0 c h1 -> modifies (loc result) h0 h1  /\  
      as_nat P256 h1 result == (as_nat P256 h0 x + uint_v y0 + uint_v y1 * pow2 64 + uint_v y2 * pow2 128 + uint_v y3 * pow2 192 + uint_v cin) % pow2 256)   

let add4_variables_void x cin y0 y1 y2 y3 result = 
  let h0 = ST.get() in 
    
  let r0 = sub result (size 0) (size 1) in      
  let r1 = sub result (size 1) (size 1) in 
  let r2 = sub result (size 2) (size 1) in 
  let r3 = sub result (size 3) (size 1) in 

  let cc0 = add_carry_u64 cin x.(0ul) y0 r0 in 
  let cc1 = add_carry_u64 cc0 x.(1ul) y1 r1 in 
  let cc2 = add_carry_u64 cc1 x.(2ul) y2 r2 in 
  add_carry_u64 cc2 x.(3ul) y3 r3;
  
    assert_norm (pow2 64 * pow2 64 = pow2 128);
    assert_norm (pow2 64 * pow2 64 * pow2 64 = pow2 192);
    assert_norm (pow2 64 * pow2 64 * pow2 64 * pow2 64 = pow2 256);
    
    assert(let r1_0 = as_seq h0 r1 in let r0_ = as_seq h0 result in Seq.index r0_ 1 == Seq.index r1_0 0);
    assert(let r2_0 = as_seq h0 r2 in let r0_ = as_seq h0 result in Seq.index r0_ 2 == Seq.index r2_0 0);
    assert(let r3_0 = as_seq h0 r3 in let r0_ = as_seq h0 result in Seq.index r0_ 3 == Seq.index r3_0 0);

    let h1 = ST.get() in 

    let x0 = Lib.Sequence.index (as_seq h0 x) 0 in 
    let x1 = Lib.Sequence.index (as_seq h0 x) 1 in 
    let x2 = Lib.Sequence.index (as_seq h0 x) 2 in 
    let x3 = Lib.Sequence.index (as_seq h0 x) 3 in 


    let r0 = Lib.Sequence.index (as_seq h1 r0) 0 in 
    let r1 = Lib.Sequence.index (as_seq h1 r1) 0 in 
    let r2 = Lib.Sequence.index (as_seq h1 r2) 0 in 
    let r3 = Lib.Sequence.index (as_seq h1 r3) 0 in 
(*

  calc (==) {((v x3 + v y3 + v cc2) % pow2 64 * pow2 192) % pow2 256;
  (==) {lemma_mod_mul_distr_l ((v x3 + v y3 + v cc2) % pow2 64) (pow2 192) (pow2 256)}
  ((v x3 + v y3 + v cc2) % pow2 64 % pow2 256 * pow2 192) % pow2 256;
  (==) {pow2_modulo_modulo_lemma_2 (v x3 + v y3 + v cc2) 256 64}
  ((v x3 + v y3 + v cc2) % pow2 256 * pow2 192) % pow2 256;
  (==) {lemma_mod_mul_distr_l (v x3 + v y3 + v cc2) (pow2 192) (pow2 256)}
  ((v x3 + v y3 + v cc2) * pow2 192) % pow2 256;
  };


  calc (==) {
  (v x0 + v y0 + v cin +  v x1 * pow2 64 + v y1 * pow2 64 +  v x2 * pow2 128 + v y2 * pow2 128 + (v x3 + v y3 + v cc2) % pow2 64 * pow2 192 - v cc2 * pow2 192) % pow2 256;
  (==) {}
  (v x0 + v y0 + v cin +  v x1 * pow2 64 + v y1 * pow2 64 +  v x2 * pow2 128 + v y2 * pow2 128 - v cc2 * pow2 192 + (v x3 + v y3 + v cc2) % pow2 64 * pow2 192 ) % pow2 256;
  (==) {lemma_mod_add_distr (v x0 + v y0 + v cin +  v x1 * pow2 64 + v y1 * pow2 64 +  v x2 * pow2 128 + v y2 * pow2 128 - v cc2 * pow2 192) ((v x3 + v y3 + v cc2) % pow2 64 * pow2 192) (pow2 256)}
  (v x0 + v y0 + v cin +  v x1 * pow2 64 + v y1 * pow2 64 +  v x2 * pow2 128 + v y2 * pow2 128 + ((v x3 + v y3 + v cc2) % pow2 64 * pow2 192) % pow2 256 - v cc2 * pow2 192) % pow2 256;
  (==) {}
  (v x0 + v y0 + v cin +  v x1 * pow2 64 + v y1 * pow2 64 +  v x2 * pow2 128 + v y2 * pow2 128  - v cc2 * pow2 192 + ((v x3 + v y3 + v cc2) * pow2 192) % pow2 256) % pow2 256; 
  (==) {lemma_mod_add_distr (v x0 + v y0 + v cin + v x1 * pow2 64 + v y1 * pow2 64 +  v x2 * pow2 128 + v y2 * pow2 128 - v cc2 * pow2 192) ((v x3 + v y3 + v cc2) * pow2 192) (pow2 256)}
  (v x0 + v y0 + v cin +  v x1 * pow2 64 + v y1 * pow2 64 +  v x2 * pow2 128 + v y2 * pow2 128 - v cc2 * pow2 192 + (v x3 + v y3 + v cc2) * pow2 192 ) % pow2 256;
  (==) {}
  (v x0 + v y0 + v cin +  v x1 * pow2 64 + v y1 * pow2 64 +  v x2 * pow2 128 + v y2 * pow2 128 + v x3 * pow2 192 + v y3 * pow2 192) % pow2 256;
  (==) {}
  (as_nat h0 x +  uint_v y0 + uint_v y1 * pow2 64 + uint_v y2 * pow2 128 + uint_v y3 * pow2 192 + uint_v cin) % pow2 256; };

  
  small_mod (v r0 + v r1 * pow2 64 + v r2 * pow2 128  + v r3 * pow2 192) (pow2 256)

*) ()

val p256_neg: arg2: felem P256 -> out: felem P256 -> Stack unit 
  (requires fun h0 -> live h0 out /\ live h0 arg2 /\ eq_or_disjoint arg2 out /\ as_nat P256 h0 arg2 < prime256)
  (ensures (fun h0 _ h1 -> modifies (loc out) h0 h1 (* /\ 
	as_nat P256 h1 out == (0 - as_nat P256 h0 arg2) % prime256 /\
	as_nat P256 h1 out == toDomain_ ((fromDomain_ 0 - fromDomain_ (as_nat P256 h0 arg2)) % prime256) *)
    )
)    

let p256_neg arg2 out =     
  assert_norm (pow2 64 * pow2 64 * pow2 64 * pow2 64 = pow2 256);
    let h0 = ST.get() in 
  let t = sub4_0 arg2 out in 

    let h1 = ST.get() in 
    (* lemma_t_computation2 t; *)
  let t0 = (u64 0) -. t in 
  let t1 = ((u64 0) -. t) >>. (size 32) in 
  let t2 = u64 0 in 
  let t3 = t -. (t <<. (size 32)) in 
    (* modulo_addition_lemma  (0 - as_nat h0 arg2) prime256 1; *)
  add4_variables_void out (u64 0)  t0 t1 t2 t3 out;
    let h2 = ST.get() in 
  
  (* small_mod (as_nat h2 out) (pow2 256);
  small_mod (as_nat h1 out) (pow2 256);

    let h2 = ST.get() in 
      assert(
      if 0 - as_nat h0 arg2 >= 0 then 
	begin
	  modulo_lemma (0 - as_nat h0 arg2) prime256;
	  as_nat h2 out == (0 - as_nat h0 arg2) % prime256
	end
      else
          begin
	    modulo_lemma (as_nat h2 out) prime256;
            as_nat h2 out == (0 - as_nat h0 arg2) % prime256
	  end);
    substractionInDomain 0 (felem_seq_as_nat (as_seq h0 arg2));
    inDomain_mod_is_not_mod (fromDomain_ 0 - fromDomain_ (felem_seq_as_nat (as_seq h0 arg2))) *) ()


inline_for_extraction noextract
val copy_point_conditional_mask_u64_2:  result: point P256
  -> x: point P256 -> mask: uint64 {uint_v mask == 0 \/ uint_v mask == pow2 64 - 1}  
  -> Stack unit
  (requires fun h -> live h result /\ live h x /\ disjoint result x)
  (ensures fun h0 _ h1 -> modifies (loc result) h0 h1 ) (*  /\ (
    if uint_v mask = 0
    then 
      as_nat h1 (gsub result (size 0) (size 4)) == as_nat h0 (gsub result (size 0) (size 4)) /\
      as_nat h1 (gsub result (size 4) (size 4)) == as_nat h0 (gsub result (size 4) (size 4)) /\
      as_nat h1 (gsub result (size 8) (size 4)) == as_nat h0 (gsub result (size 8) (size 4)) 
    else
      as_nat h1 (gsub result (size 0) (size 4)) == as_nat h0 (gsub x (size 0) (size 4)) /\
      as_nat h1 (gsub result (size 4) (size 4)) == as_nat h0 (gsub x (size 4) (size 4)) /\
      as_nat h1 (gsub result (size 8) (size 4)) == as_nat h0 (gsub x (size 8) (size 4)))
  )

*)


let copy_point_conditional_mask_u64_2  result x mask = 
  let h0 = ST.get() in 

  let x_x = sub x (size 0) (size 4) in 
  let x_y = sub x (size 4) (size 4) in 
  let x_z = sub x (size 8) (size 4) in 

  let result_x = sub result (size 0) (size 4) in 
  let result_y = sub result (size 4) (size 4) in 
  let result_z = sub result (size 8) (size 4) in 

  copy_conditional #P256 result_x x_x mask;
  copy_conditional #P256 result_y x_y mask;
  copy_conditional #P256 result_z x_z mask


val conditional_substraction: result: point P256 -> p: point P256 -> scalar: lbuffer uint8 (size 32) -> 
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

  let i0 = index scalar (size 31) in 
  let mask = lognot((u64 0) -. to_u64 (logand i0 (u8 1))) in 

  let bpX = getUInt64 (size 0) in 
  let bpY = getUInt64 (size 4) in 

    copy bpMinusX bpX;
    p256_neg bpY bpMinusY;

  Hacl.Impl.EC.PointAddMixed.point_add_mixed p bpMinus tempPoint tempBuffer;

  copy_point_conditional_mask_u64_2 result tempPoint mask;
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

val scalar_multiplication_cmb:  #buf_type: buftype -> result: point P256 -> 
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
      let is_neg = index rnaf2 (size 2 *! (j *! (size 2) +! i) +! (size 1)) in 
      let d = shift_right (d -! size 1) (size 1) in 

      loopK lut d lut j;

      let yLut = sub lut (size 4) (size 4) in 
      p256_neg yLut temp4;

      copy_conditional #P256 yLut temp4 is_neg;
      Hacl.Impl.EC.PointAddMixed.point_add_mixed result lut result tempBuffer
    );
     
    let i = size 0 in 

    let invPointDouble h (j: nat) = True in 
    Lib.Loops.for 0ul radix invPointDouble 
    (fun j -> Hacl.Impl.EC.PointDouble.point_double result result tempBuffer);

    Lib.Loops.for 0ul 26ul invJ (fun j ->
      let d = index rnaf2 (size 2 *! (j *! (size 2) +! i)) in 
      let is_neg = index rnaf2 (size 2 *! (j *! (size 2) +! i) +! (size 1)) in 
      let d = shift_right (d -! size 1) (size 1) in 

      loopK lut d lut j;

    	let yLut = sub lut (size 4) (size 4) in 
    	p256_neg yLut temp4;

	
    	copy_conditional #P256 yLut temp4  is_neg;
    	Hacl.Impl.EC.PointAddMixed.point_add_mixed result lut result tempBuffer
    );


    conditional_substraction result result scalar tempBuffer;
  

  pop_frame()
