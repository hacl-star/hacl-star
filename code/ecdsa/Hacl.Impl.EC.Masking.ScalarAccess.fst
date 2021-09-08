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

open Hacl.Spec.MontgomeryMultiplication


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


let getScalar_4_byBit #c s i = 
  let h0 = ST.get() in 
  let bit = getScalarLen c -! 1ul -! (shift_left i 2ul) in 
  
  let bit0 = shift_left (getScalarBit_leftEndian s bit) 3ul in 
  let bit1 = shift_left (getScalarBit_leftEndian s (bit -! 1ul)) 2ul in 
  let bit2 = shift_left (getScalarBit_leftEndian s (bit -! 2ul)) 1ul in 
  let bit3 = shift_left (getScalarBit_leftEndian s (bit -! 3ul)) 0ul in 

  let r = logxor (logxor bit0 bit1) (logxor bit2 bit3) in 
  
  assert(v bit0 = v (ith_bit (as_seq h0 s) (v (getScalarLen c) - 1 - 4 * v i)) * 8);
  assert(v bit1 = v (ith_bit (as_seq h0 s) (v (getScalarLen c) - 1 - 4 * v i - 1)) * 4);
  assert(v bit2 = v (ith_bit (as_seq h0 s) (v (getScalarLen c) - 1 - 4 * v i - 2)) * 2);
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


open Hacl.Impl.EC.Precomputed


inline_for_extraction noextract
val copy_point_conditional_precomputed_mixed_private: #c: curve -> result: pointAffine c 
  -> k: size_t {v k < pow2 4} -> mask : uint64 {v mask = 0 \/ v mask = pow2 64 - 1}
  -> Stack unit 
  (requires fun h -> live h result /\ point_aff_eval c h result)
  (ensures fun h0 _ h1 -> modifies (loc result) h0 h1 /\ point_aff_eval c h1 result /\ (
    if v mask = 0 then 
      point_affine_as_nat c h1 result == point_affine_as_nat c h0 result 
    else 
      pointEqual (fromDomainPoint #c #DH (toJacobianCoordinates (point_affine_as_nat c h1 result))) 
	(point_mult (v k) (basePoint #c))))


let copy_point_conditional_precomputed_mixed_private #c result k mask =
  recall_contents (points_radix_16_buffer #c) (Lib.Sequence.of_list (points_radix_16_list c));
  
  let lenCoordinate = getCoordinateLenU64 c in 
  let pointLen = 2ul *! lenCoordinate in 

  let lut_cmb_x = sub (points_radix_16_buffer #c) (k *! pointLen) lenCoordinate in 
  let lut_cmb_y = sub (points_radix_16_buffer #c) (k *! pointLen +! lenCoordinate) lenCoordinate in 

  copy_conditional #c (sub result (size 0) lenCoordinate) lut_cmb_x mask;
  copy_conditional #c (sub result lenCoordinate lenCoordinate) lut_cmb_y mask


inline_for_extraction noextract
val copy_point_conditional_precomputed_jac_private: #c: curve -> result: point c 
  -> precomputedPoints: lbuffer uint64 (size ((pow2 4) * 3 * v (getCoordinateLenU64 c)))
  -> k: size_t {v k < pow2 4} -> mask : uint64 {v mask = 0 \/ v mask = pow2 64 - 1}
  -> Stack unit 
  (requires fun h -> live h result /\ live h precomputedPoints /\ disjoint precomputedPoints result /\ (
    forall (i: nat {i < 16}). 
    let pointLen = 3ul *! getCoordinateLenU64 c in 
    let point = gsub precomputedPoints (size i *! pointLen) pointLen in 
    point_eval c h point /\ (
    let pointNat = point_as_nat c h point in 
    pointEqual (fromDomainPoint #c #DH pointNat) (point_mult i (basePoint #c)))))
  (ensures fun h0 _ h1 -> modifies (loc result) h0 h1)

let copy_point_conditional_precomputed_jac_private #c result precomputedPoints k mask =
  let lenCoordinate = getCoordinateLenU64 c in 
  let pointLen = 3ul *! lenCoordinate in 

  assume (v (k *! pointLen) + v lenCoordinate <= v ( (size ((pow2 4) * 3 * v (getCoordinateLenU64 c)))));
  assume (v (k *! pointLen +! lenCoordinate) + v lenCoordinate <= v ( (size ((pow2 4) * 3 * v (getCoordinateLenU64 c)))));
  assume (v (k *! pointLen +! lenCoordinate +! lenCoordinate) + v lenCoordinate <= v ( (size ((pow2 4) * 3 * v (getCoordinateLenU64 c)))));

  let lut_cmb_x = sub precomputedPoints (k *! pointLen) lenCoordinate in 
  let lut_cmb_y = sub precomputedPoints (k *! pointLen +! lenCoordinate) lenCoordinate in 
  let lut_cmb_z = sub precomputedPoints (k *! pointLen +! lenCoordinate +! lenCoordinate) lenCoordinate in 
    admit();

  let result_x = sub result (size 0) lenCoordinate in 
  let result_y = sub result lenCoordinate lenCoordinate in 
  let result_z = sub result (2ul *! lenCoordinate) lenCoordinate in 

  copy_conditional #c result_x lut_cmb_x mask;
  copy_conditional #c result_y lut_cmb_y mask;
  copy_conditional #c result_z lut_cmb_z mask;
  admit()
  


inline_for_extraction noextract
val getPointPrecomputedMixed_: #c: curve -> scalar: scalar_t #MUT #c -> 
  i:size_t{v i < v (getScalarLen c) / 4} -> pointToAdd: pointAffine c ->
  Stack unit 
  (requires fun h -> live h scalar /\ live h pointToAdd)
  (ensures fun h0 _ h1 -> True)

let getPointPrecomputedMixed_ #c scalar i pointToAdd = 
  let bits = getScalar_4 scalar i in 
  let invK h (k: nat) = True in 
  (* the size of the precomputed table is equal to pow2 4 = 16 *)
  Lib.Loops.for 0ul 16ul invK
    (fun k -> 
      admit();
      let mask = eq_mask (to_u64 bits) (to_u64 k) in
      let lenPoint = 2ul *! getCoordinateLenU64 c in 
	    
      copy_point_conditional_precomputed_mixed_private #c pointToAdd (k *! lenPoint) mask
      
      )


let getPointPrecomputedMixed_p256 = getPointPrecomputedMixed_ #P256


inline_for_extraction noextract
val getPointPrecomputedMixed: #c: curve -> scalar: lbuffer uint8 (size 32) -> 
  i:size_t{v i < 64} -> pointToAdd: lbuffer uint64 (size 8) ->
  Stack unit 
  (requires fun h -> live h scalar /\ live h pointToAdd)
  (ensures fun h0 _ h1 -> True)

let getPointPrecomputedMixed scalar i pointToAdd = getPointPrecomputedMixed_p256 scalar i pointToAdd


