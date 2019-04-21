module Hacl.Test.Argmax

open FStar.HyperStack.All
open FStar.Mul

open LowStar.Buffer

open Lib.IntTypes
open Lib.Buffer
open Lib.PrintBuffer

open Hacl.Argmax.Paillier


val main: unit -> St C.exit_code
let main () =
  C.String.print (C.String.of_literal "\nNo argmax tests are written yet\n");
  C.EXIT_SUCCESS
