module Hacl.Keccak

open FStar.HyperStack.All

open LowStar.Buffer

open Lib.IntTypes
open Lib.PQ.Buffer
open Hacl.Impl.SHA3

module B = LowStar.Buffer
module S = Spec.Frodo.Keccak
module ST  = FStar.HyperStack.ST

#reset-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0"

let cshake128_frodo input_len input cstm output_len output =
  let h0 = ST.get () in
  push_frame ();
  let s = create (size 25) (u64 0) in
  s.(size 0) <- u64 0x10010001a801 |. (to_u64 cstm <<. u32 48);
  state_permute s;
  absorb s (size 168) input_len input (u8 0x04);
  squeeze s (size 168) output_len output;
  pop_frame ();
  let h1 = ST.get () in
  assume (B.as_seq h1 output == S.cshake128_frodo (v input_len) (B.as_seq h0 input) cstm (v output_len))

let cshake256_frodo input_len input cstm output_len output =
  let h0 = ST.get () in
  push_frame ();
  let s = create (size 25) (u64 0) in
  s.(size 0) <- u64 0x100100018801 |. (to_u64 cstm <<. u32 48);
  state_permute s;
  absorb s (size 136) input_len input (u8 0x04);
  squeeze s (size 136) output_len output;
  pop_frame ();
  let h1 = ST.get () in
  assume (B.as_seq h1 output == S.cshake256_frodo (v input_len) (B.as_seq h0 input) cstm (v output_len))

let cshake128_frodo_4x input_len input cstm0 cstm1 cstm2 cstm3
		       output_len output0 output1 output2 output3 = admit ()

let cshake256_frodo_4x input_len input cstm0 cstm1 cstm2 cstm3
		       output_len output0 output1 output2 output3 = admit ()
