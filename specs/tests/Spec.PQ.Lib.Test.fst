module Spec.PQ.Lib.Test

open FStar.Mul
open Lib.IntTypes
open Lib.RawIntTypes
open Lib.Sequence
open Lib.ByteSequence

open Spec.PQ.Lib

let test () =
  let q = 100 in
  let n = 5 in
  let m = 2 in
  let k = 3 in
  let a1 = List.Tot.map (zqelem #q) [1; 2; 3; 4; 5] in
  let a1:zqvector_t q 5 = createL a1 in
  let a2 = List.Tot.map (zqelem #q) [2; 3; 4; 5; 6] in
  let a2:zqvector_t q 5 = createL a2 in
  let aM:zqmatrix_t q n m = createL [a1; a2] in
  let b1 = List.Tot.map (zqelem #q) [1; 2] in
  let b1:zqvector_t q 2 = createL b1 in
  let b2 = List.Tot.map (zqelem #q) [5; 6] in
  let b2:zqvector_t q 2 = createL b2 in
  let b3 = List.Tot.map (zqelem #q) [7; 10] in
  let b3:zqvector_t q 2 = createL b3 in

  let bM:zqmatrix_t q m k = createL [b1; b2; b3] in

  IO.print_string "\nTest 1. Vector addition \n";
  let aV = zqvector_add a1 a2 in
  List.iter (fun a -> IO.print_string (UInt8.to_string (u8_to_UInt8 (u8 a))); IO.print_string " ") (as_list aV);

  IO.print_string "\nTest 2. Matrix addition \n";
  let res = zqmatrix_add aM aM in
  List.iter (fun a -> IO.print_string (UInt8.to_string (u8_to_UInt8 (u8 a))); IO.print_string " ") (as_list res.[0]);
  IO.print_string "\n";
  List.iter (fun a -> IO.print_string (UInt8.to_string (u8_to_UInt8 (u8 a))); IO.print_string " ") (as_list res.[1]);

  IO.print_string "\nTest 2. Matrix multiplication \n";
  let res = zqmatrix_mul aM bM in
  List.iter (fun a -> IO.print_string (UInt8.to_string (u8_to_UInt8 (u8 a))); IO.print_string " ") (as_list res.[0]);
  IO.print_string "\n";
  List.iter (fun a -> IO.print_string (UInt8.to_string (u8_to_UInt8 (u8 a))); IO.print_string " ") (as_list res.[1]);
  IO.print_string "\n";
  List.iter (fun a -> IO.print_string (UInt8.to_string (u8_to_UInt8 (u8 a))); IO.print_string " ") (as_list res.[2]);

  IO.print_string "\nEnd\n"
