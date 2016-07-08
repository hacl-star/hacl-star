open Poly_Poly1305
open Char
open Hacl_SBuffer

type sbytes = u8s
       
let from_string s : sbytes =
  let b = create (Hacl_UInt8.of_string "0") (String.length s) in
  for i = 0 to (String.length s - 1) do
    upd b i (Hacl_Cast.uint8_to_sint8 (code (String.get s i)))
  done;
  b

let from_bytestring (s:string) : sbytes =
  let b = create (Hacl_UInt8.of_string "0") ((String.length s) / 2) in
  for i = 0 to ((String.length s / 2) - 1) do
    upd b i (Hacl_UInt8.of_string ("0x" ^ (String.sub s (2*i) 2)))
  done;
  b

let print (s:sbytes) (len:int) : unit =
  for i = 0 to len - 1 do
    print_string (Hacl_UInt8.to_string_hex (index s i));
    if i < len - 1 then print_string ":"
  done
    
let time f x s =
  let t = Sys.time() in
  let _ = f x in
  Printf.printf "Ellapsed time for %s : %fs\n" s (Sys.time() -. t)
  
let key = from_bytestring "85d6be7857556d337f4452fe42d506a80103808afb0db2fd4abff6af4149f51b"
let msg = from_string "Cryptographic Forum Research Group"
let expected = "a8:06:1d:c1:30:51:36:c6:c2:2b:8b:af:0c:01:27:a9"

let _ =
  print_string "Testing poly1305...\n";
  (* To store the hash *)
  let hash = create (Hacl_UInt8.of_string "0") 16 in
  (* Run hash computation *)
  time (fun () -> for i = 1 to 1 do poly1305_mac hash msg 34 key done) () "100.000 iterations of poly1305";
  (* Output result *)
  let ok = "a8061dc1305136c6c22b8baf0c0127a9" in
  for i = 0 to 15 do
    if not(Hacl_UInt8.to_string_hex (index hash i) = String.sub ok (2*i) 2) then
      failwith (Printf.sprintf "Ciphertext differs at byte %d: %s %s\n" i (Hacl_UInt8.to_string_hex (index hash i)) (String.sub ok (2*i) 2)) 
  done;
  print_string ("Expected: " ^ expected ^ "\n");
  print_string  "Got hash: ";
  print hash 16;
  print_string "\n"
