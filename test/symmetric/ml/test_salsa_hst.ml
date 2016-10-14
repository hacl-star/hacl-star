open Hacl_Symmetric_Salsa20
open Char
(* open Hacl_SBuffer *)
open FStar_Buffer
open Hacl_Cast
       
let key = {content = Array.init 32 (fun x -> if x = 0 then (Hacl_UInt8.of_string "128")
                                             else (Hacl_UInt8.of_string "0")); idx = 0; length = 32 }
    
let nonce =
  let n = create (Hacl_UInt8.of_string "0") 8 in
  n

let counter = Hacl_UInt64.of_int (Prims.parse_int "0")

let from_string s =
  let b = create (Hacl_UInt8.of_string "0") (String.length s) in
  for i = 0 to (String.length s - 1) do
    upd b i (Hacl_UInt8.of_string (string_of_int (code (String.get s i))))
  done;
  b
                
let print (b:bytes) =
  let s = ref "" in
  for i = 0 to b.length - 1 do
    let s' = Printf.sprintf "%X" (int_of_string (Hacl_UInt8.to_string (index b i)))  in
    let s' = if String.length s' = 1 then "0" ^ s' else s' in 
    s := !s ^ s';
  done;
  !s

let max x y =
  if x > y then x else y
   
let print_array (a) =
  let s = ref "" in
  for i = 0 to a.length - 1 do
    let s' = Printf.sprintf "%X" (index a i)  in
    let s' = String.init (max (8 - String.length s') 0) (fun x -> '0')  ^ s' in
    let s' = if i mod 4 = 3 then s' ^ "\n" else s' ^ " " in
    s := !s ^ s';
  done;
  print_string !s; print_string "\n"

let print_bytes b =
  print_string (print b); print_string "\n"

let plaintext = create (Hacl_UInt8.of_string "0") 64
let ok = "e3be8fdd8beca2e3ea8ef9475b29a6e7003951e1097a5c38d23b7a5fad9f6844b22c97559e2723c7cbbd3fe4fc8d9a0744652a83e72a9c461876af4d7ef1a117"

let _ =
  let ciphertext = create (uint8_to_sint8 0) 64 in
  salsa20_encrypt ciphertext key nonce plaintext 64;
  print_string "Test key:\n";
  print_bytes key;
  print_string "Test nonce:\n";
  print_bytes nonce;
  print_string "Expected ciphertext:\n";
  print_string ok;
  print_string "Got ciphertext:\n";
  print_bytes ciphertext;
  for i = 0 to 63 do
    if not(Hacl_UInt8.to_string_hex (index ciphertext i) = String.sub ok (2*i) 2) then
      failwith (Printf.sprintf "Ciphertext differs at byte %d: %s %s\n" i (Hacl_UInt8.to_string_hex (index ciphertext i)) (String.sub ok (2*i) 2)) 
  done
