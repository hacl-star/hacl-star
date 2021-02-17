module Hacl.Keccak

open FStar.HyperStack.All

open LowStar.Buffer

open Lib.IntTypes
open Lib.Buffer

module SHA3 = Hacl.SHA3

#set-options "--fuel 0 --ifuel 0 --z3rlimit 100"

(* This is a stub non-vectorized implementation intended to be replaced by a real
   vectorized implementation like the one in fips202.c for x64
*)

let shake128_4x input_len input0 input1 input2 input3 output_len output0 output1 output2 output3 =
  SHA3.shake128_hacl input_len input0 output_len output0;
  SHA3.shake128_hacl input_len input1 output_len output1;
  SHA3.shake128_hacl input_len input2 output_len output2;
  SHA3.shake128_hacl input_len input3 output_len output3


let shake256_4x input_len input0 input1 input2 input3 output_len output0 output1 output2 output3 =
  SHA3.shake256_hacl input_len input0 output_len output0;
  SHA3.shake256_hacl input_len input1 output_len output1;
  SHA3.shake256_hacl input_len input2 output_len output2;
  SHA3.shake256_hacl input_len input3 output_len output3
