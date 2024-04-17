module Hacl.Keccak

open FStar.HyperStack.All

open LowStar.Buffer

open Lib.IntTypes
open Lib.Buffer

module SHA3 = Hacl.Hash.SHA3.Scalar

#set-options "--fuel 0 --ifuel 0 --z3rlimit 100"

(* This is a stub non-vectorized implementation intended to be replaced by a real
   vectorized implementation like the one in fips202.c for x64
*)

let shake128_4x input_len input0 input1 input2 input3 output_len output0 output1 output2 output3 =
  SHA3.shake128 output0 output_len input0 input_len;
  SHA3.shake128 output1 output_len input1 input_len;
  SHA3.shake128 output2 output_len input2 input_len;
  SHA3.shake128 output3 output_len input3 input_len


let shake256_4x input_len input0 input1 input2 input3 output_len output0 output1 output2 output3 =
  SHA3.shake256 output0 output_len input0 input_len;
  SHA3.shake256 output1 output_len input1 input_len;
  SHA3.shake256 output2 output_len input2 input_len;
  SHA3.shake256 output3 output_len input3 input_len
