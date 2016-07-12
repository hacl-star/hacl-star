open Curve_Parameters
open Hacl_UInt64
open Big_int
open Stdint
open Hacl_SBuffer
open Curve_Bignum
open Curve_Point

let scalar1 = "a546e36bf0527c9d3b16154b82465edd62144c0ac1fc5a18506a2244ba449ac4"
let scalar2 = "4b66e9d4d1b4673c5ad22691957d6af5c11b6421e0ea01d42ca4169e7918ba0d"

let input1 = "e6db6867583030db3594c1a424b15f7c726624ec26b3353b10a903a6d0ab1c4c"
let input2 = "e5210f12786811d3f4b7959d0538ae2c31dbe7106fc03c3efc4cd549c715a493"

let expected1 = "c3da55379de9c6908e94ea4df28d084f32eccf03491c71f754b4075577a28552"
let expected2 = "95cbde9476e8907d7aade45cb4b873f88b595a68799fa152e6f8f7647aac7957"

let import_from_string scalar_string =
  let bytes = Array.init 32 (fun i -> Hacl_UInt8.of_string ("0x" ^ (String.sub scalar_string (2*i) 2))) in
  {content = bytes; idx=0; length = 32}

let print_bytes b =
  Array.iter (fun x -> print_string ((Hacl_UInt8.to_string_hex x))) (b.content);
  print_string "\n"

let _ =
  print_string "Testing scalar 1 and input 1:\n";
  let scalar = import_from_string scalar1 in
  let qx = import_from_string input1 in
  let output = {content = Array.create 32 (Hacl_UInt8.of_string "0"); idx=0; length = 32} in
  Curve_Curve25519.exp output qx scalar;
  print_string "Got:\n";
  print_bytes output;
  print_string ("Expected:\n" ^ expected1 ^ "\n");
  for i = 0 to 31 do
    if not(Hacl_UInt8.to_string_hex (index output i) = String.sub expected1 (2*i) 2) then
      failwith (Printf.sprintf "Ciphertext differs at byte %d: %s %s\n" i (Hacl_UInt8.to_string_hex (index output i)) (String.sub expected1 (2*i) 2)) 
  done;
  print_string "Testing scalar 2 and input 2:\n";
  let scalar = import_from_string scalar2 in
  let qx = import_from_string input2 in
  Curve_Curve25519.exp output qx scalar;
  print_string "Got:\n";
  print_bytes output;
  print_string ("Expected:\n" ^ expected2 ^ "\n");
  for i = 0 to 31 do
    if not(Hacl_UInt8.to_string_hex (index output i) = String.sub expected2 (2*i) 2) then
      failwith (Printf.sprintf "Ciphertext differs at byte %d: %s %s\n" i (Hacl_UInt8.to_string_hex (index output i)) (String.sub expected2 (2*i) 2)) 
  done;

