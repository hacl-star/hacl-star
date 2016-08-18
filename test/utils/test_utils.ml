open Char
open Hacl_SBuffer
open Hacl_Cast



(* Helper functions *)

let from_string s l =
  let b = create (Hacl_UInt8.of_string "0") l in
  for i = 0 to (String.length s - 1) do
    upd b i (uint8_to_sint8 (code (String.get s i)))
  done;
  b

let from_bytestring s =
  let b = create (Hacl_UInt8.of_string "0") ((String.length s) / 2) in
  for i = 0 to ((String.length s / 2) - 1) do
    upd b i (uint8_to_sint8 (int_of_string ("0x" ^ (String.sub s (2*i) 2))))
  done;
  b

let print_bytes (s:Hacl_UInt8.uint8 Hacl_SBuffer.buffer) : unit =
  for i = 0 to Array.length s.content - 1 do
    print_string (Hacl_UInt8.to_string_hex (Hacl_SBuffer.index s i))
  done;
  print_string "\n"

let print_uint32s (s:Hacl_UInt32.uint32 Hacl_SBuffer.buffer) : unit =
  for i = 0 to Array.length s.content - 1 do
    print_string (Hacl_UInt32.to_string_hex (index s i))
  done;
  print_string "\n"




let test_result () =


  Printf.printf "##############################\n";
  Printf.printf "   Hacl.Operations.copymask   \n";
  Printf.printf "##############################\n";

  let test_in = create (uint8_to_sint8 17) 10 in
  let test_out = create (uint8_to_sint8 0) 10 in
  print_bytes test_in;
  Hacl_Operations.copymask test_in (uint32_to_sint32 0) (uint32_to_sint32 32) test_out 0;
  print_bytes test_out;

  let test_in = create (uint8_to_sint8 17) 10 in
  let test_out = create (uint8_to_sint8 0) 10 in
  print_bytes test_in;
  Hacl_Operations.copymask test_in (uint32_to_sint32 0) (uint32_to_sint32 32) test_out 1;
  print_bytes test_out;

  let test_in = create (uint8_to_sint8 17) 10 in
  let test_out = create (uint8_to_sint8 0) 10 in
  print_bytes test_in;
  Hacl_Operations.copymask test_in (uint32_to_sint32 0) (uint32_to_sint32 32) test_out 2;
  print_bytes test_out;

  let test_in = create (uint8_to_sint8 17) 10 in
  let test_out = create (uint8_to_sint8 0) 10 in
  print_bytes test_in;
  Hacl_Operations.copymask test_in (uint32_to_sint32 0) (uint32_to_sint32 32) test_out 3;
  print_bytes test_out;

  let test_in = create (uint8_to_sint8 17) 10 in
  let test_out = create (uint8_to_sint8 0) 10 in
  print_bytes test_in;
  Hacl_Operations.copymask test_in (uint32_to_sint32 0) (uint32_to_sint32 32) test_out 4;
  print_bytes test_out;

  let test_in = create (uint8_to_sint8 17) 10 in
  let test_out = create (uint8_to_sint8 0) 10 in
  print_bytes test_in;
  Hacl_Operations.copymask test_in (uint32_to_sint32 0) (uint32_to_sint32 32) test_out 5;
  print_bytes test_out;

  let test_in = create (uint8_to_sint8 17) 10 in
  let test_out = create (uint8_to_sint8 0) 10 in
  print_bytes test_in;
  Hacl_Operations.copymask test_in (uint32_to_sint32 0) (uint32_to_sint32 32) test_out 6;
  print_bytes test_out;

  let test_in = create (uint8_to_sint8 17) 10 in
  let test_out = create (uint8_to_sint8 0) 10 in
  print_bytes test_in;
  Hacl_Operations.copymask test_in (uint32_to_sint32 0) (uint32_to_sint32 32) test_out 7;
  print_bytes test_out;

  let test_in = create (uint8_to_sint8 17) 10 in
  let test_out = create (uint8_to_sint8 0) 10 in
  print_bytes test_in;
  Hacl_Operations.copymask test_in (uint32_to_sint32 0) (uint32_to_sint32 32) test_out 8;
  print_bytes test_out;

  let test_in = create (uint8_to_sint8 17) 10 in
  let test_out = create (uint8_to_sint8 0) 10 in
  print_bytes test_in;
  Hacl_Operations.copymask test_in (uint32_to_sint32 0) (uint32_to_sint32 32) test_out 9;
  print_bytes test_out;

  let test_in = create (uint8_to_sint8 17) 10 in
  let test_out = create (uint8_to_sint8 0) 10 in
  print_bytes test_in;
  Hacl_Operations.copymask test_in (uint32_to_sint32 0) (uint32_to_sint32 32) test_out 10;
  print_bytes test_out;



  Printf.printf "\n\n";
  Printf.printf "##############################\n";
  Printf.printf "   Hacl.Operations.setmask1   \n";
  Printf.printf "##############################\n";

  let test_in = create (uint8_to_sint8 17) 10 in
  let test_out = create (uint8_to_sint8 0) 10 in
  print_bytes test_in;
  Hacl_Operations.setmask1 test_out 0 (uint8_to_sint8 17);
  print_bytes test_out;

  let test_in = create (uint8_to_sint8 17) 10 in
  let test_out = create (uint8_to_sint8 0) 10 in
  print_bytes test_in;
  Hacl_Operations.setmask1 test_out 1 (uint8_to_sint8 17);
  print_bytes test_out;

  let test_in = create (uint8_to_sint8 17) 10 in
  let test_out = create (uint8_to_sint8 0) 10 in
  print_bytes test_in;
  Hacl_Operations.setmask1 test_out 2 (uint8_to_sint8 17);
  print_bytes test_out;

  let test_in = create (uint8_to_sint8 17) 10 in
  let test_out = create (uint8_to_sint8 0) 10 in
  print_bytes test_in;
  Hacl_Operations.setmask1 test_out 3 (uint8_to_sint8 17);
  print_bytes test_out;

  let test_in = create (uint8_to_sint8 17) 10 in
  let test_out = create (uint8_to_sint8 0) 10 in
  print_bytes test_in;
  Hacl_Operations.setmask1 test_out 4 (uint8_to_sint8 17);
  print_bytes test_out;

  let test_in = create (uint8_to_sint8 17) 10 in
  let test_out = create (uint8_to_sint8 0) 10 in
  print_bytes test_in;
  Hacl_Operations.setmask1 test_out 5 (uint8_to_sint8 17);
  print_bytes test_out;

  let test_in = create (uint8_to_sint8 17) 10 in
  let test_out = create (uint8_to_sint8 0) 10 in
  print_bytes test_in;
  Hacl_Operations.setmask1 test_out 6 (uint8_to_sint8 17);
  print_bytes test_out;

  let test_in = create (uint8_to_sint8 17) 10 in
  let test_out = create (uint8_to_sint8 0) 10 in
  print_bytes test_in;
  Hacl_Operations.setmask1 test_out 7 (uint8_to_sint8 17);
  print_bytes test_out;

  let test_in = create (uint8_to_sint8 17) 10 in
  let test_out = create (uint8_to_sint8 0) 10 in
  print_bytes test_in;
  Hacl_Operations.setmask1 test_out 8 (uint8_to_sint8 17);
  print_bytes test_out;

  let test_in = create (uint8_to_sint8 17) 10 in
  let test_out = create (uint8_to_sint8 0) 10 in
  print_bytes test_in;
  Hacl_Operations.setmask1 test_out 9 (uint8_to_sint8 17);
  print_bytes test_out;

  let test_in = create (uint8_to_sint8 17) 10 in
  let test_out = create (uint8_to_sint8 0) 10 in
  print_bytes test_in;
  Hacl_Operations.setmask1 test_out 10 (uint8_to_sint8 17);
  print_bytes test_out;



  Printf.printf "\n\n";
  Printf.printf "##############################\n";
  Printf.printf "   Hacl.Operations.setmask2   \n";
  Printf.printf "##############################\n";

  let test_in = create (uint8_to_sint8 17) 10 in
  let test_out = create (uint8_to_sint8 0) 10 in
  print_bytes test_in;
  Hacl_Operations.setmask2 test_out 10 (uint8_to_sint8 17) (uint8_to_sint8 34) (uint32_to_sint32 0);
  print_bytes test_out;

  let test_in = create (uint8_to_sint8 17) 10 in
  let test_out = create (uint8_to_sint8 0) 10 in
  print_bytes test_in;
  Hacl_Operations.setmask2 test_out 10 (uint8_to_sint8 17) (uint8_to_sint8 34) (uint32_to_sint32 1);
  print_bytes test_out;

  let test_in = create (uint8_to_sint8 17) 10 in
  let test_out = create (uint8_to_sint8 0) 10 in
  print_bytes test_in;
  Hacl_Operations.setmask2 test_out 10 (uint8_to_sint8 17) (uint8_to_sint8 34) (uint32_to_sint32 2);
  print_bytes test_out;

  let test_in = create (uint8_to_sint8 17) 10 in
  let test_out = create (uint8_to_sint8 0) 10 in
  print_bytes test_in;
  Hacl_Operations.setmask2 test_out 10 (uint8_to_sint8 17) (uint8_to_sint8 34) (uint32_to_sint32 3);
  print_bytes test_out;

  let test_in = create (uint8_to_sint8 17) 10 in
  let test_out = create (uint8_to_sint8 0) 10 in
  print_bytes test_in;
  Hacl_Operations.setmask2 test_out 10 (uint8_to_sint8 17) (uint8_to_sint8 34) (uint32_to_sint32 4);
  print_bytes test_out;

  let test_in = create (uint8_to_sint8 17) 10 in
  let test_out = create (uint8_to_sint8 0) 10 in
  print_bytes test_in;
  Hacl_Operations.setmask2 test_out 10 (uint8_to_sint8 17) (uint8_to_sint8 34) (uint32_to_sint32 5) ;
  print_bytes test_out;

  let test_in = create (uint8_to_sint8 17) 10 in
  let test_out = create (uint8_to_sint8 0) 10 in
  print_bytes test_in;
  Hacl_Operations.setmask2 test_out 10 (uint8_to_sint8 17) (uint8_to_sint8 34) (uint32_to_sint32 6) ;
  print_bytes test_out;

  let test_in = create (uint8_to_sint8 17) 10 in
  let test_out = create (uint8_to_sint8 0) 10 in
  print_bytes test_in;
  Hacl_Operations.setmask2 test_out 10 (uint8_to_sint8 17) (uint8_to_sint8 34) (uint32_to_sint32 7);
  print_bytes test_out;

  let test_in = create (uint8_to_sint8 17) 10 in
  let test_out = create (uint8_to_sint8 0) 10 in
  print_bytes test_in;
  Hacl_Operations.setmask2 test_out 10 (uint8_to_sint8 17) (uint8_to_sint8 34) (uint32_to_sint32 8);
  print_bytes test_out;

  let test_in = create (uint8_to_sint8 17) 10 in
  let test_out = create (uint8_to_sint8 0) 10 in
  print_bytes test_in;
  Hacl_Operations.setmask2 test_out 10 (uint8_to_sint8 17) (uint8_to_sint8 34) (uint32_to_sint32 9);
  print_bytes test_out;

  let test_in = create (uint8_to_sint8 17) 10 in
  let test_out = create (uint8_to_sint8 0) 10 in
  print_bytes test_in;
  Hacl_Operations.setmask2 test_out 10 (uint8_to_sint8 17) (uint8_to_sint8 34) (uint32_to_sint32 10);
  print_bytes test_out;



  Printf.printf "\n\n";
  Printf.printf "##############################\n";
  Printf.printf "   Hacl.Operations.setmask3   \n";
  Printf.printf "##############################\n";

  let test_in = create (uint8_to_sint8 17) 10 in
  let test_out = create (uint8_to_sint8 0) 10 in
  print_bytes test_in;
  Hacl_Operations.setmask3 test_out 10 (uint8_to_sint8 17) (uint8_to_sint8 34) (uint8_to_sint8 51) (uint32_to_sint32 0) (uint32_to_sint32 2);
  print_bytes test_out;

  let test_in = create (uint8_to_sint8 17) 10 in
  let test_out = create (uint8_to_sint8 0) 10 in
  print_bytes test_in;
  Hacl_Operations.setmask3 test_out 10 (uint8_to_sint8 17) (uint8_to_sint8 34) (uint8_to_sint8 51) (uint32_to_sint32 1) (uint32_to_sint32 3);
  print_bytes test_out;

  let test_in = create (uint8_to_sint8 17) 10 in
  let test_out = create (uint8_to_sint8 0) 10 in
  print_bytes test_in;
  Hacl_Operations.setmask3 test_out 10 (uint8_to_sint8 17) (uint8_to_sint8 34) (uint8_to_sint8 51) (uint32_to_sint32 2) (uint32_to_sint32 4);
  print_bytes test_out;

  let test_in = create (uint8_to_sint8 17) 10 in
  let test_out = create (uint8_to_sint8 0) 10 in
  print_bytes test_in;
  Hacl_Operations.setmask3 test_out 10 (uint8_to_sint8 17) (uint8_to_sint8 34) (uint8_to_sint8 51) (uint32_to_sint32 3) (uint32_to_sint32 5);
  print_bytes test_out;

  let test_in = create (uint8_to_sint8 17) 10 in
  let test_out = create (uint8_to_sint8 0) 10 in
  print_bytes test_in;
  Hacl_Operations.setmask3 test_out 10 (uint8_to_sint8 17) (uint8_to_sint8 34) (uint8_to_sint8 51) (uint32_to_sint32 4) (uint32_to_sint32 6);
  print_bytes test_out;

  let test_in = create (uint8_to_sint8 17) 10 in
  let test_out = create (uint8_to_sint8 0) 10 in
  print_bytes test_in;
  Hacl_Operations.setmask3 test_out 10 (uint8_to_sint8 17) (uint8_to_sint8 34) (uint8_to_sint8 51) (uint32_to_sint32 5) (uint32_to_sint32 7);
  print_bytes test_out;

  let test_in = create (uint8_to_sint8 17) 10 in
  let test_out = create (uint8_to_sint8 0) 10 in
  print_bytes test_in;
  Hacl_Operations.setmask3 test_out 10 (uint8_to_sint8 17) (uint8_to_sint8 34) (uint8_to_sint8 51) (uint32_to_sint32 6) (uint32_to_sint32 8);
  print_bytes test_out;

  let test_in = create (uint8_to_sint8 17) 10 in
  let test_out = create (uint8_to_sint8 0) 10 in
  print_bytes test_in;
  Hacl_Operations.setmask3 test_out 10 (uint8_to_sint8 17) (uint8_to_sint8 34) (uint8_to_sint8 51) (uint32_to_sint32 7) (uint32_to_sint32 9);
  print_bytes test_out;

  let test_in = create (uint8_to_sint8 17) 10 in
  let test_out = create (uint8_to_sint8 0) 10 in
  print_bytes test_in;
  Hacl_Operations.setmask3 test_out 10 (uint8_to_sint8 17) (uint8_to_sint8 34) (uint8_to_sint8 51) (uint32_to_sint32 8) (uint32_to_sint32 10);
  print_bytes test_out;

  Printf.printf "\n\n"



(* Entry point *)
let _ =  test_result ()
