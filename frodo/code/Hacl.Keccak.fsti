module Hacl.Keccak

open FStar.HyperStack.All

open LowStar.Buffer

open Lib.IntTypes
open Lib.Buffer

module B = LowStar.Buffer
module S = Spec.SHA3

val cshake128_frodo_4x:
    input_len:size_t
  -> input:lbuffer uint8 (v input_len)
  -> cstm0:uint16
  -> cstm1:uint16
  -> cstm2:uint16
  -> cstm3:uint16
  -> output_len:size_t
  -> output0:lbuffer uint8 (v output_len)
  -> output1:lbuffer uint8 (v output_len)
  -> output2:lbuffer uint8 (v output_len)
  -> output3:lbuffer uint8 (v output_len)
  -> Stack unit
    (requires fun h -> 
      B.live h input /\ 
      B.live h output0 /\
      B.live h output1 /\
      B.live h output2 /\
      B.live h output3 /\
      B.loc_pairwise_disjoint 
        [loc_buffer input; loc_buffer output0; loc_buffer output1; 
         loc_buffer output2; loc_buffer output3])
    (ensures  fun h0 _ h1 ->
      modifies (loc_union (loc_union (loc_buffer output0)
                                     (loc_buffer output1))
                          (loc_union (loc_buffer output2)
                                     (loc_buffer output3)))
                                   h0 h1 /\
      B.as_seq h1 output0 ==
      S.cshake128_frodo (v input_len) (B.as_seq h0 input) cstm0 (v output_len) /\
      B.as_seq h1 output1 ==
      S.cshake128_frodo (v input_len) (B.as_seq h0 input) cstm1 (v output_len) /\
      B.as_seq h1 output2 ==
      S.cshake128_frodo (v input_len) (B.as_seq h0 input) cstm2 (v output_len) /\
      B.as_seq h1 output3 ==
      S.cshake128_frodo (v input_len) (B.as_seq h0 input) cstm3 (v output_len))

val cshake256_frodo_4x:
    input_len:size_t
  -> input:lbuffer uint8 (v input_len)
  -> cstm0:uint16
  -> cstm1:uint16
  -> cstm2:uint16
  -> cstm3:uint16
  -> output_len:size_t
  -> output0:lbuffer uint8 (v output_len)
  -> output1:lbuffer uint8 (v output_len)
  -> output2:lbuffer uint8 (v output_len)
  -> output3:lbuffer uint8 (v output_len)
  -> Stack unit
    (requires fun h -> 
      B.live h input /\ 
      B.live h output0 /\
      B.live h output1 /\
      B.live h output2 /\
      B.live h output3 /\
      B.loc_pairwise_disjoint 
        [loc_buffer input; loc_buffer output0; loc_buffer output1; 
         loc_buffer output2; loc_buffer output3])
    (ensures  fun h0 _ h1 ->
      modifies (loc_union (loc_union (loc_buffer output0)
                                     (loc_buffer output1))
                          (loc_union (loc_buffer output2)
                                     (loc_buffer output3)))
                                   h0 h1 /\
      B.as_seq h1 output0 ==
      S.cshake256_frodo (v input_len) (B.as_seq h0 input) cstm0 (v output_len) /\
      B.as_seq h1 output1 ==
      S.cshake256_frodo (v input_len) (B.as_seq h0 input) cstm1 (v output_len) /\
      B.as_seq h1 output2 ==
      S.cshake256_frodo (v input_len) (B.as_seq h0 input) cstm2 (v output_len) /\
      B.as_seq h1 output3 ==
      S.cshake256_frodo (v input_len) (B.as_seq h0 input) cstm3 (v output_len))
