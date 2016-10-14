open Char
open Hacl_SBuffer
open Hacl_Cast



   
let from_string_block s =
  let b = create (Hacl_UInt8.of_string "0") (String.length s) in
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

let from_string_block s l =
  let b = create (Hacl_UInt8.of_string "0") l in
  for i = 0 to ((String.length s) - 1) do
    upd b i (uint8_to_sint8 (code (String.get s i)))
  done;
  b

let from_bytestring_block s l =
  let b = create (Hacl_UInt8.of_string "0") (l / 2) in
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

let print_l_bytes (s:Hacl_UInt8.uint8 Hacl_SBuffer.buffer) l : unit =
  for i = 0 to l - 1 do
    print_string (Hacl_UInt8.to_string_hex (Hacl_SBuffer.index s i))
  done;
  print_string "\n"

let print_l_uint32s (s:Hacl_UInt32.uint32 Hacl_SBuffer.buffer) l : unit =
  for i = 0 to l - 1 do
    print_string (Hacl_UInt32.to_string_hex (index s i))
  done;
  print_string "\n"
