open Curve_Parameters
open Hacl_UInt64
open Big_int
open Stdint
open Hacl_SBuffer
open Curve_Bignum
open Curve_Point
      
let scalar1 = "3d262fddf9ec8e88495266fea19a34d28882acef045104d0d1aae121700a779c984c24f8cdd78fbff44943eba368f54b29259a4f1c600ad3"
let scalar2 = "203d494428b8399352665ddca42f9de8fef600908e0d461cb021f8c538345dd77c3e4806e25f46d3315c44e0a5b4371282dd2c8d5be3095f"
let input1 = "06fce640fa3487bfda5f6cf2d5263f8aad88334cbd07437f020f08f9814dc031ddbdc38c19c6da2583fa5429db94ada18aa7a7fb4ef8a086"
let input2 = "0fbcc2f993cd56d3305b0b7d9e55d4c1a8fb5dbb52f8e9a1e9b6201b165d015894e56c4d3570bee52fe205e28a78b91cdfbde71ce8d157db"

let expected1 = "ce3e4ff95a60dc6697da1db1d85e6afbdf79b50a2412d7546d5f239fe14fbaadeb445fc66a01b0779d98223961111e21766282f73dd96b6f"
let expected2 = "884a02576239ff7a2f2f63b2db6a9ff37047ac13568e1e30fe63c4a7ad1b3ee3a5700df34321d62077e63633c575c1c954514e99da7c179d"

let import_from_string scalar_string =
  let bytes = Array.init 56 (fun i -> Hacl_UInt8.of_string ("0x" ^ (String.sub scalar_string (2*i) 2))) in
  {content = bytes; idx=0; length = 56}

let print_bytes b =
  Array.iter (fun x -> print_string ((Hacl_UInt8.to_string_hex x))) (b.content);
  print_string "\n"

let print_bigint b =
  Array.iter (fun x -> print_string (Hacl_UInt64.to_string x)) (b.content);
  print_string "\n"
               
let _ =
  print_string "Testing scalar 1 and input 1:\n";
  let scalar = import_from_string scalar1 in
  let qx = import_from_string input1 in
  let output = {content = Array.create 56 (Hacl_UInt8.of_string "0"); idx=0; length = 56} in
  (* let bigi = {content = Array.create 8 (Hacl_UInt64.of_string "0"); idx = 0; length = 56} in *)
  (* Curve_Curve448.expand bigi qx; *)
  (* print_bigint bigi; *)
  (* Curve_Curve448.contract output bigi; *)
  (* print_bytes output *)
  
  Curve_Curve448.exp output qx scalar;
  print_string "Got:\n";
  print_bytes output;
  print_string ("Expected:\n" ^ expected1 ^ "\n");
  for i = 0 to 55 do
    if not(Hacl_UInt8.to_string_hex (index output i) = String.sub expected1 (2*i) 2) then
      failwith (Printf.sprintf "Ciphertext differs at byte %d: %s %s\n" i (Hacl_UInt8.to_string_hex (index output i)) (String.sub expected1 (2*i) 2))
  done;
  print_string "Testing scalar 2 and input 2:\n";
  let scalar = import_from_string scalar2 in
  let qx = import_from_string input2 in
  Curve_Curve448.exp output qx scalar;
  print_string "Got:\n";
  print_bytes output;
  print_string ("Expected:\n" ^ expected2 ^ "\n");
  for i = 0 to 55 do
    if not(Hacl_UInt8.to_string_hex (index output i) = String.sub expected2 (2*i) 2) then
      failwith (Printf.sprintf "Ciphertext differs at byte %d: %s %s\n" i (Hacl_UInt8.to_string_hex (index output i)) (String.sub expected2 (2*i) 2))
  done
