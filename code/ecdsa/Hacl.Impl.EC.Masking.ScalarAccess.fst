module Hacl.Impl.EC.Masking.ScalarAccess


open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer
open Lib.Loops

open Spec.ECC
open Spec.ECC.Curves
open Hacl.Impl.EC.Masking

open Hacl.Spec.EC.Definition
open Hacl.Impl.EC.PointDouble


#set-options " --z3rlimit 200"


inline_for_extraction noextract
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
    (ensures  fun h0 r h1 -> h0 == h1 /\ r == ith_bit #c (as_seq h0 s) (v n) /\ v r <= 1)

let getScalarBit_l #c #b s n = 
  push_frame();
    let h0 = ST.get() in 
    let temp = create (size 1) (u64 0) in 
    let inv h i = modifies (loc temp) h0 h /\ live h temp in 
    for 0ul (getScalarLen c) inv (fun i -> 
      let bit = getScalarBit_leftEndian s n in 
      assert(bit == ith_bit (as_seq h0 s) (v n));
      
      let mask = neq_mask (size_to_uint64 n) (size_to_uint64 i) in 
	neq_mask_lemma (size_to_uint64 n) (size_to_uint64 i);
      copy_conditional_u64 bit temp mask);
  let result = index temp (size 0) in
  admit();
  pop_frame();
  result
    

[@ CInline]
inline_for_extraction noextract  
val getScalar_4: #buf_type: buftype 
  -> scalar: lbuffer_t buf_type uint8 (size 32) -> i: size_t {v i < 64} -> 
  Stack uint32 
    (requires fun h -> live h scalar)
    (ensures fun h0 _ h1 -> True)

let getScalar_4 #a scalar i = 
  let half = shift_right i 1ul in 
    shift_right_lemma i 1ul;
  let word = to_u32 (index scalar half) in 
  let bitShift : size_t = logand i (size 1) in 
    logand_mask i (size 1) 1; 
  let bitShiftAsPrivate = size_to_uint32 bitShift in 
  let mask : uint32 = cmovznz01 (u32 0xf0) (u32 0x0f) bitShiftAsPrivate in  
  let shiftMask = cmovznz01 (size 0x4) (size 0x0) bitShift in
  let result : uint32 = logand word mask in 
  let result : uint32 = shift_right result shiftMask in 
  result


open Hacl.Impl.EC.Precomputed

inline_for_extraction noextract
val getPointPrecomputedMixed_: #c: curve -> scalar: lbuffer uint8 (size 32) -> 
  i:size_t{v i < 64} -> pointToAdd: lbuffer uint64 (size 8) ->
  Stack unit 
  (requires fun h -> live h scalar /\ live h pointToAdd)
  (ensures fun h0 _ h1 -> True)

let getPointPrecomputedMixed_ #c scalar i pointToAdd = 
  push_frame();
    let bits: uint32 = getScalar_4 scalar i in
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


