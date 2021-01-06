module Hacl.Keccak

open FStar.HyperStack.All

open LowStar.Buffer

open Lib.IntTypes
open Lib.Buffer

module S = Spec.SHA3

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

val shake128_4x:
    input_len:size_t
  -> input0:lbuffer uint8 input_len
  -> input1:lbuffer uint8 input_len
  -> input2:lbuffer uint8 input_len
  -> input3:lbuffer uint8 input_len
  -> output_len:size_t
  -> output0:lbuffer uint8 output_len
  -> output1:lbuffer uint8 output_len
  -> output2:lbuffer uint8 output_len
  -> output3:lbuffer uint8 output_len
  -> Stack unit
    (requires fun h ->
      live h input0 /\ live h input1 /\ live h input2 /\ live h input3 /\
      live h output0 /\ live h output1 /\ live h output2 /\ live h output3 /\
      loc_pairwise_disjoint
        [loc input0; loc input1; loc input2; loc input3;
        loc output0; loc output1; loc output2; loc output3])
    (ensures  fun h0 _ h1 ->
      modifies (loc_union (loc_union (loc output0) (loc output1))
                          (loc_union (loc output2) (loc output3))) h0 h1 /\
      as_seq h1 output0 == S.shake128 (v input_len) (as_seq h0 input0) (v output_len) /\
      as_seq h1 output1 == S.shake128 (v input_len) (as_seq h0 input1) (v output_len) /\
      as_seq h1 output2 == S.shake128 (v input_len) (as_seq h0 input2) (v output_len) /\
      as_seq h1 output3 == S.shake128 (v input_len) (as_seq h0 input3) (v output_len))


val shake256_4x:
    input_len:size_t
  -> input0:lbuffer uint8 input_len
  -> input1:lbuffer uint8 input_len
  -> input2:lbuffer uint8 input_len
  -> input3:lbuffer uint8 input_len
  -> output_len:size_t
  -> output0:lbuffer uint8 output_len
  -> output1:lbuffer uint8 output_len
  -> output2:lbuffer uint8 output_len
  -> output3:lbuffer uint8 output_len
  -> Stack unit
    (requires fun h ->
      live h input0 /\ live h input1 /\ live h input2 /\ live h input3 /\
      live h output0 /\ live h output1 /\ live h output2 /\ live h output3 /\
      loc_pairwise_disjoint
        [loc input0; loc input1; loc input2; loc input3;
         loc output0; loc output1; loc output2; loc output3])
    (ensures  fun h0 _ h1 ->
      modifies (loc_union (loc_union (loc output0) (loc output1))
                          (loc_union (loc output2) (loc output3))) h0 h1 /\
      as_seq h1 output0 == S.shake256 (v input_len) (as_seq h0 input0) (v output_len) /\
      as_seq h1 output1 == S.shake256 (v input_len) (as_seq h0 input1) (v output_len) /\
      as_seq h1 output2 == S.shake256 (v input_len) (as_seq h0 input2) (v output_len) /\
      as_seq h1 output3 == S.shake256 (v input_len) (as_seq h0 input3) (v output_len))
