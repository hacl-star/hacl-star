module Hacl.Impl.P256.Core

open FStar.Mul
open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer

open Hacl.Impl.P256.SolinasReduction
open Hacl.Impl.P256.Bignum
open Hacl.Impl.P256.Field

open Spec.P256.MontgomeryMultiplication
friend Spec.P256.MontgomeryMultiplication

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

let toDomain f res =
  push_frame ();
  let multBuffer = create (size 8) (u64 0) in
  bn_lshift256 f multBuffer;
  solinas_reduction_impl multBuffer res;
  pop_frame()


let fromDomain f res =
  montgomery_multiplication_buffer_by_one f res
