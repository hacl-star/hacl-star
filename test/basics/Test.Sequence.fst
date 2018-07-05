module Test.Sequence

open FStar.Mul
open Lib.IntTypes
open Lib.RawIntTypes
open Lib.Sequence
open Lib.ByteSequence


let test () =
  let buf = create 32 (u8 0xFF) in

  IO.print_string "Buffer: ";
  List.iter (fun a -> IO.print_uint8 (u8_to_UInt8 a)) (as_list buf);
  IO.print_string "\n"
