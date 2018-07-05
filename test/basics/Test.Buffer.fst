module Test.Buffer

open FStar.HyperStack.All
open FStar.Mul
open Lib.IntTypes
open Lib.RawIntTypes
open Lib.Buffer
open Lib.ByteBuffer

val main: unit -> Stack C.exit_code (requires (fun h -> True)) (ensures (fun h0 _ h1 -> True))
let main () =

  let ffs = create #uint8 (size 32) (u8 0xFF) in
  Lib.Print.print_bytes (size 32) ffs;

  C.EXIT_SUCCESS

