module Hacl.Impl.EC.Reduction

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open FStar.Math.Lemmas
open FStar.Math.Lib
open Lib.Buffer

open Hacl.SolinasReduction.Lemmas
open Spec.P256
open Hacl.Impl.EC.LowLevel

open Hacl.Impl.SolinasReduction.P384
open Hacl.Impl.SolinasReduction.P256
open Hacl.Impl.EC.P521.Reduction

open Hacl.Spec.P256.Definition
open FStar.Mul

module BV = FStar.BitVector
module Seq = FStar.Seq

#reset-options "--fuel 0 --ifuel 0 --z3rlimit 50"

let reduction #c i o =
  match c with 
    |P256 -> solinas_reduction_impl_p256 i o 
    |P384 -> solinas_reduction_impl_p384 i o
    |Default -> reduction_p521 i o
