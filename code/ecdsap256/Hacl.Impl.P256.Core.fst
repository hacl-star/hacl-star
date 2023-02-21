module Hacl.Impl.P256.Core

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open FStar.Mul
open FStar.Math.Lemmas

open Lib.IntTypes
open Lib.Buffer

open Hacl.Impl.SolinasReduction
open Hacl.Impl.P256.Bignum
open Hacl.Impl.P256.Field

open Spec.P256.MontgomeryMultiplication
friend Spec.P256.MontgomeryMultiplication

#set-options "--z3rlimit 100 --fuel 0 --ifuel 0"

let toDomain value result =
  push_frame();
    let multBuffer = create (size 8) (u64 0) in
    shift_256_impl value multBuffer;
    solinas_reduction_impl multBuffer result;
  pop_frame()


let fromDomain f result =
  montgomery_multiplication_buffer_by_one f result
