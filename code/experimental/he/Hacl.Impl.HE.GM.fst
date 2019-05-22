module Hacl.Impl.HE.GM

open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Mul

open LowStar.Buffer

open Lib.IntTypes
open Lib.Buffer
open Lib.PrintBuffer

open Hacl.Impl.Addition
open Hacl.Impl.Lib

val testfunc : lbytes 5ul -> lbytes 6ul
let testfunc _ = admit()
