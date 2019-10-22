module Hacl.Curve25519.Finv.Field51

open FStar.HyperStack
open FStar.HyperStack.All
open FStar.Mul

open Lib.IntTypes
open Lib.Buffer
open Lib.ByteBuffer

open Hacl.Impl.Curve25519.Fields
open Hacl.Curve25519_51

friend Hacl.Curve25519_51

module ST = FStar.HyperStack.ST

module S = Hacl.Spec.Curve25519.Finv
module P = Spec.Curve25519

#reset-options "--max_fuel 0 --using_facts_from '* -FStar.Seq'"

let fsquare_times_51 o inp tmp n =
  fsquare_times o inp tmp n

let finv_51 o i tmp =
  finv o i tmp
