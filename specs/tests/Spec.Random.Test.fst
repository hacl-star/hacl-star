module Spec.Random.Test

open Lib.IntTypes
open Lib.RawIntTypes
open Lib.Sequence
open Lib.ByteSequence

open Lib.RandomSequence

let test () =
  let len: size_nat = 32 in
  let output = generate len in
  IO.print_string "\nBuffer after [generate len]: \n";
  List.iter (fun a -> IO.print_uint8 (u8_to_UInt8 a)) (as_list output);
  IO.print_string "\n"
  (* let result = write len output in *)
  (* IO.print_string "\nBuffer after [write len output]: "; *)
  (* List.iter (fun a -> IO.print_uint8 (u8_to_UInt8 a)) (as_list output); *)
  (* if result then IO.print_string "\nRandom write: Success!\n" *)
  (* else IO.print_string "\nRandom write: Failure :(\n" *)
