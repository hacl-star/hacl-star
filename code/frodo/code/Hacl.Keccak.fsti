module Hacl.Keccak

open FStar.HyperStack.All

open LowStar.Buffer

open Lib.IntTypes
open Lib.Buffer

module S = Spec.SHA3

val cshake128_frodo_4x:
    input_len:size_t
  -> input:lbuffer uint8 input_len
  -> cstm0:uint16
  -> cstm1:uint16
  -> cstm2:uint16
  -> cstm3:uint16
  -> output_len:size_t
  -> output0:lbuffer uint8 output_len
  -> output1:lbuffer uint8 output_len
  -> output2:lbuffer uint8 output_len
  -> output3:lbuffer uint8 output_len
  -> Stack unit
    (requires fun h ->
      live h input /\
      live h output0 /\
      live h output1 /\
      live h output2 /\
      live h output3 /\
      loc_pairwise_disjoint
        [loc input; loc output0; loc output1; loc output2; loc output3])
    (ensures  fun h0 _ h1 ->
      modifies (loc_union (loc_union (loc output0) (loc output1))
                          (loc_union (loc output2) (loc output3)))
               h0 h1 /\
      as_seq h1 output0 ==
      S.cshake128_frodo (v input_len) (as_seq h0 input) cstm0 (v output_len) /\
      as_seq h1 output1 ==
      S.cshake128_frodo (v input_len) (as_seq h0 input) cstm1 (v output_len) /\
      as_seq h1 output2 ==
      S.cshake128_frodo (v input_len) (as_seq h0 input) cstm2 (v output_len) /\
      as_seq h1 output3 ==
      S.cshake128_frodo (v input_len) (as_seq h0 input) cstm3 (v output_len))

val cshake256_frodo_4x:
    input_len:size_t
  -> input:lbuffer uint8 input_len
  -> cstm0:uint16
  -> cstm1:uint16
  -> cstm2:uint16
  -> cstm3:uint16
  -> output_len:size_t
  -> output0:lbuffer uint8 output_len
  -> output1:lbuffer uint8 output_len
  -> output2:lbuffer uint8 output_len
  -> output3:lbuffer uint8 output_len
  -> Stack unit
    (requires fun h ->
      live h input /\
      live h output0 /\
      live h output1 /\
      live h output2 /\
      live h output3 /\
      loc_pairwise_disjoint
        [loc input; loc output0; loc output1; loc output2; loc output3])
    (ensures  fun h0 _ h1 ->
      modifies (loc_union (loc_union (loc output0) (loc output1))
                          (loc_union (loc output2) (loc output3)))
               h0 h1 /\
      as_seq h1 output0 ==
      S.cshake256_frodo (v input_len) (as_seq h0 input) cstm0 (v output_len) /\
      as_seq h1 output1 ==
      S.cshake256_frodo (v input_len) (as_seq h0 input) cstm1 (v output_len) /\
      as_seq h1 output2 ==
      S.cshake256_frodo (v input_len) (as_seq h0 input) cstm2 (v output_len) /\
      as_seq h1 output3 ==
      S.cshake256_frodo (v input_len) (as_seq h0 input) cstm3 (v output_len))
