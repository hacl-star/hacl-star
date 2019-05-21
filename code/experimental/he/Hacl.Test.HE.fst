module Hacl.Test.HE

open FStar.HyperStack.All
open FStar.Mul

open LowStar.Buffer

open Lib.IntTypes
open Lib.Buffer
open Lib.PrintBuffer


val main: unit -> St C.exit_code
let main () =
  C.String.print
    (C.String.of_literal "\n\n ====== No argmax tests are written yet ====== \n\n\n");
  C.EXIT_SUCCESS
