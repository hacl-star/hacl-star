module Hacl.Impl.P384.LowLevel

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer

open Hacl.Spec.P384.Definition

open Hacl.Impl.LowLevel

open FStar.Math.Lemmas

open FStar.Mul
open Lib.IntTypes.Intrinsics

#set-options " --z3rlimit 200"

inline_for_extraction
let prime384_buffer: x: ilbuffer uint64 (size 6) {witnessed #uint64 #(size 6) x (Lib.Sequence.of_list p384_prime_list) /\ recallable x /\ seq_as_nat6 (Lib.Sequence.of_list (p384_prime_list)) == prime384} = 
  assert_norm (seq_as_nat6 (Lib.Sequence.of_list (p384_prime_list)) == prime384);
  createL_global p384_prime_list
