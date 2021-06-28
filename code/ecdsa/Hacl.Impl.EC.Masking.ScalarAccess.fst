module Hacl.Impl.EC.Masking.ScalarAccess

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer
open Lib.ByteBuffer
open Lib.Loops

open Spec.ECC
open Spec.ECC.Curves
open Hacl.Impl.EC.Masking

open Hacl.Spec.EC.Definition
open Hacl.Impl.EC.PointDouble

open FStar.Mul

module BV = FStar.BitVector


#set-options "--fuel 0 --ifuel 0 --z3rlimit 200"

val getScalarBit_leftEndian: #c: curve 
  -> #buf_type: buftype 
  -> s:lbuffer_t buf_type uint8 (getScalarLenBytes c) 
  -> n:size_t{v n < v (getScalarLen c)}
  -> Stack uint64
    (requires fun h0 -> live h0 s)
    (ensures  fun h0 r h1 -> h0 == h1 /\ r == ith_bit #c (as_seq h0 s) (v n) /\ v r <= 1)

let getScalarBit_leftEndian #c #buf_type s n =
  let h0 = ST.get () in
  assert_norm (1 = pow2 1 - 1);
  assert (v (mod_mask #U8 #SEC 1ul) == v (u8 1)); 
  to_u64 ((s.(getScalarLenBytes c -. 1ul -. n /. 8ul) >>. (n %. 8ul)) &. u8 1)


inline_for_extraction noextract
val getScalarBit_l: #c: curve 
  -> #buf_type: buftype 
  -> s:lbuffer_t buf_type uint8 (getScalarLenBytes c) 
  -> n:size_t{v n < v (getScalarLen c)}
  -> Stack uint64
    (requires fun h0 -> live h0 s)
    (ensures  fun h0 r h1 -> modifies0 h0 h1 /\ r == ith_bit #c (as_seq h0 s) (v n) /\ v r <= 1)

let getScalarBit_l #c #b s n = 
  push_frame();
    let temp = create (size 1) (u64 0) in 
    let h0 = ST.get() in 
    let inv h i = modifies (loc temp) h0 h /\ live h0 temp /\ (
      let temp0 = Lib.Sequence.index (as_seq h temp) 0 in v temp0 <= 1 /\ (
      if i > v n then v temp0 == v (ith_bit (as_seq h0 s) (v n)) else True)) in 

  for 0ul (getScalarLen c) inv (fun i -> 
    let h0_ = ST.get() in 
    
    let bit = getScalarBit_leftEndian s n in 
    assert(bit == ith_bit (as_seq h0 s) (v n));
      
    let mask = eq_mask (size_to_uint64 n) (size_to_uint64 i) in 
      eq_mask_lemma (size_to_uint64 n) (size_to_uint64 i);
    copy_conditional_u64 bit temp mask
  );

  let result = index temp (size 0) in
  let h1 = ST.get() in 
  pop_frame();
  result


inline_for_extraction noextract
val get_high_part: a:uint64 -> r:uint32{uint_v r == uint_v a / pow2 32}
let get_high_part a = to_u32 (shift_right a (size 32))

inline_for_extraction noextract
val get_low_part: a:uint64 -> r:uint32{uint_v r == uint_v a % pow2 32}
let get_low_part a = to_u32 a

val append_uint: #n1:nat -> #n2:nat
  -> num1:UInt.uint_t n1 -> num2:UInt.uint_t n2 -> UInt.uint_t (n1 + n2)

val shift_bound: #n:nat -> num:UInt.uint_t n -> n':nat ->
  Lemma (num * pow2 n' <= pow2 (n' + n) - pow2 n')

let shift_bound #n num n' =
  Math.Lemmas.lemma_mult_le_right (pow2 n') num (pow2 n - 1);
  Math.Lemmas.distributivity_sub_left (pow2 n) 1 (pow2 n');
  Math.Lemmas.pow2_plus n' n


let append_uint #n1 #n2 num1 num2 =
  shift_bound num2 n1;
  num1 + num2 * pow2 n1

val to_vec_append : #n1:pos-> #n2:pos -> num1:UInt.uint_t n1 -> num2:UInt.uint_t n2 ->
  Lemma (UInt.to_vec (append_uint num1 num2) ==
         Seq.append (UInt.to_vec num2) (UInt.to_vec num1))

let to_vec_append #n1 #n2 num1 num2 =
  UInt.append_lemma (UInt.to_vec num2) (UInt.to_vec num1)

val to_vec_low_high: a:UInt.uint_t 64 -> Lemma
  (UInt.to_vec a ==
   Seq.append (UInt.to_vec #32 (a / pow2 32)) (UInt.to_vec #32 (a % pow2 32)))

let to_vec_low_high a =
  assert (a == append_uint #32 #32 (a % pow2 32) (a / pow2 32));
  to_vec_append #32 #32 (a % pow2 32) (a / pow2 32)


val logand_vec_append (#n1 #n2: pos) (a1 b1: BV.bv_t n1) (a2 b2: BV.bv_t n2) :
  Lemma (Seq.append (BV.logand_vec a1 b1) (BV.logand_vec a2 b2) ==
         BV.logand_vec #(n1 + n2) (FStar.Seq.append a1 a2) (FStar.Seq.append b1 b2))

let logand_vec_append #n1 #n2 a1 b1 a2 b2 =
  Seq.lemma_eq_intro (Seq.append (BV.logand_vec a1 b1) (BV.logand_vec a2 b2))
                     (BV.logand_vec #(n1 + n2) (Seq.append a1 a2) (Seq.append b1 b2))

val lemma_and_both_parts: a: uint64 -> b: uint64 -> Lemma (
  let a0, a1 = get_low_part a, get_high_part a in 
  let b0, b1 = get_low_part b, get_high_part b in 
  v (logand a1 b1) * pow2 32 + v (logand a0 b0) == v (logand a b))

let lemma_and_both_parts a b = 
  to_vec_low_high (v a);
  to_vec_low_high (v b);
    let a0, a1 = get_low_part a, get_high_part a in 
    let b0, b1 = get_low_part b, get_high_part b in 


  let a0_ = UInt.to_vec #32 (v a0) in
  let a1_ = UInt.to_vec #32 (v a1) in


  let b0_ = UInt.to_vec #32 (v b0) in
  let b1_ = UInt.to_vec #32 (v b1) in
  
  assert(UInt.to_vec #64 (v a) == Seq.append a1_ a0_);
  assert(UInt.to_vec #64 (v b) == Seq.append b1_ b0_);
  

  logand_vec_append a1_ b1_ a0_ b0_;

  assert(Seq.append (BV.logand_vec a1_ b1_) (BV.logand_vec a0_ b0_) ==
         BV.logand_vec #64  (FStar.Seq.append a1_ a0_) (FStar.Seq.append b1_ b0_));

  UInt.append_lemma a1_ a0_;
  UInt.append_lemma b1_ b0_;
  assert( (Seq.append a1_ a0_) == UInt.to_vec #64 (v a));
  assert(UInt.from_vec #64 (Seq.append b1_ b0_) == v b);


  assert( (Seq.append (BV.logand_vec a1_ b1_) (BV.logand_vec a0_ b0_)) ==
          (BV.logand_vec #64 (UInt.to_vec #64 (v a)) (UInt.to_vec #64 (v b))));


  logand_spec a b;
  assert(UInt.from_vec (BV.logand_vec #64 (UInt.to_vec #64 (v a)) (UInt.to_vec #64 (v b))) == v (logand a b));
  
  logand_spec a1 b1;
  assert(UInt.from_vec (BV.logand_vec #32 (UInt.to_vec #32 (v a1)) (UInt.to_vec #32 (v b1))) == v (logand a1 b1));
  logand_spec a0 b0;
  assert(UInt.from_vec (BV.logand_vec #32 (UInt.to_vec #32 (v a0)) (UInt.to_vec #32 (v b0))) == v (logand a0 b0));
  

  UInt.append_lemma (BV.logand_vec a1_ b1_) (BV.logand_vec a0_ b0_);
  assert(v (logand a1 b1) * pow2 32 + v (logand a0 b0) == v (logand a b))



val getScalar_4: #c: curve
  -> #buf_type: buftype 
  -> s: scalar_t #buf_type #c
  -> i: size_t {v i < v (getScalarLenBytes c) * 2} -> 
  Stack uint32
  (requires fun h -> live h s)
  (ensures fun h0 r h1 -> 
    let radix = 4 in 
    let s = as_seq h0 s in 
    v r == FStar.Math.Lib.arithmetic_shift_right (scalar_as_nat #c s) (radix * v i) % pow2 radix)

let getScalar_4 #a scalar i = 
  let h0 = ST.get() in
  
  let half = shift_right i 1ul in 
    shift_right_lemma i 1ul;
  let word = to_u32 (index scalar half) in 
  let bitShift = logand i (size 1) in 
    logand_mask i (size 1) 1; 
  let bitShiftAsPrivate = size_to_uint32 bitShift in 
  
  let mask = cmovznz01 (u32 0xf0) (u32 0x0f) bitShiftAsPrivate in  
  let shiftMask = cmovznz01 (size 0x4) (size 0x0) bitShift in
  
  let result0 = logand word mask in 
  let result = shift_right result0 shiftMask in 

  let index = v i in 
  assert(v half = index / 2);
  assert(v word = v (Lib.Sequence.index (as_seq h0 scalar) (index / 2)));
  
  assert(if index % 2 = 0 then v mask = 0xf0 else v mask = 0x0f);
  assert(if index % 2 = 0 then v shiftMask = 4 else v shiftMask = 0);

  if index % 2 = 0 then 
    begin
      logand_spec word mask;
      assert(v result0 = logand_v (v word) (v mask));
      assert(v mask = 0xf0);
      assert(v result = v result0 / pow2 4)
    end
  else
    begin
      assert(v mask = 0x0f);
      logand_mask word mask 4;
      assert(v result0 = v word % pow2 4);
      assert(v result = v (Lib.Sequence.index (as_seq h0 scalar) (index / 2)) % pow2 4)
    end;

  admit();
  result


inline_for_extraction noextract
val getScalar_4_byBit: #c: curve
  -> #buf_type: buftype 
  -> s: scalar_t #buf_type #c
  -> i: size_t {v i < v (getScalarLenBytes c) * 2} -> 
  Stack uint64
    (requires fun h -> live h s)
    (ensures fun h0 _ h1 -> True)


let getScalar_4_byBit #c s i = 
  let bit = getScalarLen c -! 1ul -! (shift_left i 2ul) in 
  
  let bit0 = shift_left (getScalarBit_leftEndian s bit) 3ul in 
  let bit1 = shift_left (getScalarBit_leftEndian s (bit -! 1ul)) 2ul in 
  let bit2 = shift_left (getScalarBit_leftEndian s (bit -! 2ul)) 1ul in 
  let bit3 = shift_left (getScalarBit_leftEndian s (bit -! 3ul)) 0ul in 
  logxor (logxor bit0 bit1) (logxor bit2 bit3)



open Hacl.Impl.EC.Precomputed

inline_for_extraction noextract
val getPointPrecomputedMixed_: #c: curve -> scalar: scalar_t #MUT #c -> 
  i:size_t{v i < 64} -> pointToAdd: lbuffer uint64 (size 8) ->
  Stack unit 
  (requires fun h -> live h scalar /\ live h pointToAdd)
  (ensures fun h0 _ h1 -> True)

let getPointPrecomputedMixed_ #c scalar i pointToAdd = 
  push_frame();
    let bits = getScalar_4_byBit scalar i in 
  (*   let r =  shift_right (to_u64 bits) 18ul in 
    let bits = getScalar_4 #c scalar i in *)
    let invK h (k: nat) = True in 
    Lib.Loops.for 0ul 16ul invK
    (fun k -> 
      recall_contents points_radix_16 (Lib.Sequence.of_list points_radix_16_list_p256);
      let mask = eq_mask (to_u64 bits) (to_u64 k) in 
      let lut_cmb_x = sub points_radix_16 (k *! 8ul) (size 4) in 
      let lut_cmb_y = sub points_radix_16 (k *! 8ul +! (size 4)) (size 4) in 

      admit();
      copy_conditional #c (sub pointToAdd (size 0) (size 4)) lut_cmb_x mask;
      copy_conditional #c (sub pointToAdd (size 4) (size 4)) lut_cmb_y mask);
  pop_frame()


let getPointPrecomputedMixed_p256 = getPointPrecomputedMixed_ #P256


inline_for_extraction noextract
val getPointPrecomputedMixed: #c: curve -> scalar: lbuffer uint8 (size 32) -> 
  i:size_t{v i < 64} -> pointToAdd: lbuffer uint64 (size 8) ->
  Stack unit 
  (requires fun h -> live h scalar /\ live h pointToAdd)
  (ensures fun h0 _ h1 -> True)

let getPointPrecomputedMixed scalar i pointToAdd = getPointPrecomputedMixed_p256 scalar i pointToAdd


