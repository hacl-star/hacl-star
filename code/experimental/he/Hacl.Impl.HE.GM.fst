module Hacl.Impl.HE.GM

open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Mul

open LowStar.Buffer

open Lib.IntTypes
open Lib.Buffer
open Lib.PrintBuffer

open Hacl.Impl.Bignum.Addition
open Hacl.Impl.Bignum.Core

val testfunc : lbytes 5ul -> lbytes 6ul
let testfunc _ = admit()
