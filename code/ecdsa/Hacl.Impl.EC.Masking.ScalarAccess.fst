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

open FStar.Math.Lemmas
open Hacl.Impl.EC.Masking.ScalarAccess.Lemmas


#set-options "--fuel 0 --ifuel 0 --z3rlimit 200"

inline_for_extraction
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


inline_for_extraction
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
    let bit = getScalarBit_leftEndian s n in 
    let mask = eq_mask (size_to_uint64 n) (size_to_uint64 i) in 
      eq_mask_lemma (size_to_uint64 n) (size_to_uint64 i);
    copy_conditional_u64 bit temp mask);

  let result = index temp (size 0) in
  let h1 = ST.get() in 
  pop_frame();
  result

inline_for_extraction
val getScalar_4: #c: curve
  -> #buf_type: buftype 
  -> s: scalar_t #buf_type #c
  -> i: size_t {v i < v (getScalarLenBytes c) * 2} -> 
  Stack uint32
  (requires fun h -> live h s)
  (ensures fun h0 r h1 -> modifies0 h0 h1 /\ (
    let radix = 4 in 
    v r == FStar.Math.Lib.arithmetic_shift_right (scalar_as_nat #c (as_seq h0 s)) (v (getScalarLen c) - (v i + 1) * radix) % pow2 radix))


let getScalar_4 #c scalar i = 
  let h0 = ST.get() in
  
  let half = shift_right i 1ul in 
    shift_right_lemma i 1ul;
  let word = to_u32 (index scalar half) in 
  let bitShift = logand i (size 1) in 
    logand_mask i (size 1) 1; 
  let bitShiftAsPrivate = size_to_uint32 bitShift in 

  let leftWord = shift_right word (size 0x4) in 
  let rightWord = logand word (u32 0x0f) in 
  
  let result = cmovznz01 leftWord rightWord bitShiftAsPrivate in 
 
  if v i % 2 = 0 then 
    begin
      assert (v result ==  (v (Lib.Sequence.index (as_seq h0 scalar) (v i / 2)) / pow2 4) % pow2 4);
      let s = as_seq h0 scalar in 
      calc (==) {
	v result;
	   (==) {lemma_index_scalar_as_nat #c s (v i / 2)}
	((scalar_as_nat #c s / pow2 (v (getScalarLen c) - (v i  + 2) * 4) % pow2 8) / pow2 4) % pow2 4; 
	  (==) {pow2_modulo_division_lemma_1 (scalar_as_nat #c s / pow2 (v (getScalarLen c) - (v i  + 2) * 4)) 4 8}
	((scalar_as_nat #c s / pow2 (v (getScalarLen c) - (v i  + 2) * 4) / pow2 4) % pow2 4) % pow2 4;
	  (==) {lemma_mod_twice ((scalar_as_nat #c s / pow2 (v (getScalarLen c) - (v i + 2) * 4) / pow2 4)) (pow2 4)}
	(scalar_as_nat #c s / pow2 (v (getScalarLen c) - (v i + 2) * 4) / pow2 4) % pow2 4; };
	
      calc (==) {
	(scalar_as_nat #c s / pow2 (v (getScalarLen c) - (v i + 2) * 4) / pow2 4);
	(==) {division_multiplication_lemma (scalar_as_nat #c s) (pow2 (v (getScalarLen c) - (v i  + 2) * 4)) (pow2 4)}
	scalar_as_nat #c s / (pow2 (v (getScalarLen c) - (v i + 2) * 4) * pow2 4);
	(==) {pow2_plus (v (getScalarLen c) - (v i + 2) * 4) 4} 
	scalar_as_nat #c s / (pow2 (v (getScalarLen c) - (v i + 1) * 4));}

      end
  else
    begin
      logand_mask word (u32 0x0f) 4;
      assert(v result = v (Lib.Sequence.index (as_seq h0 scalar) (v i  / 2)) % pow2 4);
      let s = as_seq h0 scalar in 

      calc (==) {
	v result;
      (==) {}
	v (Lib.Sequence.index (as_seq h0 scalar) (v i  / 2)) % pow2 4;
      (==) {lemma_index_scalar_as_nat #c s (v i  / 2)}
	(scalar_as_nat #c s / pow2 (v (getScalarLen c) - (v i  / 2 + 1) * 8) % pow2 8) % pow2 4;
      (==) {euclidean_division_definition (v i)  2}
	(scalar_as_nat #c s / pow2 (v (getScalarLen c) - (v i  + 1) * 4) % pow2 8) % pow2 4;
      (==) {pow2_modulo_modulo_lemma_1 (scalar_as_nat #c s / pow2 (v (getScalarLen c) - (v i + 1) * 4)) 4 8}
      	scalar_as_nat #c s / pow2 (v (getScalarLen c) - (v i + 1) * 4) % pow2 4; }
    end;
  
  result


inline_for_extraction noextract
val getScalar_byBit_oneBit: #c: curve
  -> #buf_type: buftype 
  -> s: scalar_t #MUT #c
  -> bit: size_t {v bit < v (getScalarLen c)}
  -> j: size_t {v j < 4} -> 
  Stack uint64 
  (requires fun h -> live h s)
  (ensures fun h0 r h1 -> modifies0 h0 h1 /\ 
    v r == v (ith_bit (as_seq h0 s) (v bit)) * pow2 (v j))

let getScalar_byBit_oneBit #c s bit j = shift_left (getScalarBit_leftEndian s bit) j



val computeBit: #c: curve -> i: size_t {v i < v (getScalarLenBytes c) * 2} -> 
  Tot (bit: size_t {v bit == v (getScalarLen c) - 1 - 4 * v i})

let computeBit #c i = getScalarLen c -! 1ul -! (shift_left i 2ul)


inline_for_extraction
val getScalar_4_byBit: #c: curve
  -> #buf_type: buftype 
  -> s: scalar_t #buf_type #c
  -> i: size_t {v i < v (getScalarLenBytes c) * 2} -> 
  Stack uint64
  (requires fun h -> live h s)
  (ensures fun h0 r h1 -> modifies0 h0 h1 /\ (
    let radix = 4 in 
    v r == FStar.Math.Lib.arithmetic_shift_right (scalar_as_nat #c (as_seq h0 s)) (v (getScalarLen c) - (v i + 1) * radix) % pow2 radix))

let getScalar_4_byBit #c #b s i = 
  let h0 = ST.get() in 
  
  let bit = computeBit #c i in 
  
  let bit0 = getScalar_byBit_oneBit #c #b s bit 3ul in 
  let bit1 = getScalar_byBit_oneBit #c #b s (bit -! 1ul) 2ul in 
  let bit2 = getScalar_byBit_oneBit #c #b s (bit -! 2ul) 1ul in 
  let bit3 = getScalar_byBit_oneBit #c #b s (bit -! 3ul) 0ul in 

  let r = logxor (logxor bit0 bit1) (logxor bit2 bit3) in 
  
  assert(v bit0 = v (ith_bit (as_seq h0 s) (v (getScalarLen c) - 1 - 4 * v i)) * pow2 3);
  assert(v bit1 = v (ith_bit (as_seq h0 s) (v (getScalarLen c) - 1 - 4 * v i - 1)) * pow2 2);
  assert(v bit2 = v (ith_bit (as_seq h0 s) (v (getScalarLen c) - 1 - 4 * v i - 2)) * pow2 1);
  assert(v bit3 = v (ith_bit (as_seq h0 s) (v (getScalarLen c) - 1 - 4 * v i - 3)));

  logxor_spec bit0 bit1;
  logxor_spec bit2 bit3;
  logxor_spec (logxor bit0 bit1) (logxor bit2 bit3);
  lemma_xor_of_4 
    (ith_bit (as_seq h0 s) (v (getScalarLen c) - 1 - 4 * v i))
    (ith_bit (as_seq h0 s) (v (getScalarLen c) - 1 - 4 * v i - 1)) 
    (ith_bit (as_seq h0 s) (v (getScalarLen c) - 1 - 4 * v i - 2))
    (ith_bit (as_seq h0 s) (v (getScalarLen c) - 1 - 4 * v i - 3)); 

  scalar_as_nat_def #c (as_seq h0 s) (4 * v i + 1);
  scalar_as_nat_def #c (as_seq h0 s) (4 * v i + 2);
  scalar_as_nat_def #c (as_seq h0 s) (4 * v i + 3);
  scalar_as_nat_def #c (as_seq h0 s) (4 * v i + 4);

  scalar_as_sub_radix4 (as_seq h0 s) (v i);

  r
