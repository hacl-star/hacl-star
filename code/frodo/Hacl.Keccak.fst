module Hacl.Keccak

open FStar.HyperStack.All

open LowStar.Buffer

open Lib.IntTypes
open Lib.Buffer

module SHA3 = Hacl.SHA3

#set-options "--max_fuel 0 --max_ifuel 0 --z3rlimit 100"

(* This is a stub non-vectorized implementation intended to be replaced by a real 
   vectorized implementation like the one in fips202.c for x64
*)

let cshake128_frodo_4x input_len input cstm0 cstm1 cstm2 cstm3
  output_len output0 output1 output2 output3 =
  SHA3.cshake128_frodo input_len input (to_u16 cstm0) output_len output0;  
  SHA3.cshake128_frodo input_len input (to_u16 cstm1) output_len output1;  
  SHA3.cshake128_frodo input_len input (to_u16 cstm2) output_len output2;
  SHA3.cshake128_frodo input_len input (to_u16 cstm3) output_len output3

let cshake256_frodo_4x input_len input cstm0 cstm1 cstm2 cstm3
  output_len output0 output1 output2 output3 =
  SHA3.cshake256_frodo input_len input (to_u16 cstm0) output_len output0;  
  SHA3.cshake256_frodo input_len input (to_u16 cstm1) output_len output1;  
  SHA3.cshake256_frodo input_len input (to_u16 cstm2) output_len output2;
  SHA3.cshake256_frodo input_len input (to_u16 cstm3) output_len output3
