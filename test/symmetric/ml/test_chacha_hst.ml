open Hacl_Symmetric_Chacha20
open Char
(* open Hacl_SBuffer *)
open FStar_Buffer
open Hacl_Cast
       
let key = {content = Array.init 32 (fun x -> (Hacl_UInt8.of_string (string_of_int x))); idx = 0; length = 32 }
    
let nonce =
  let n = create (Hacl_UInt8.of_string "0") 12 in
  upd n 7 (Hacl_UInt8.of_string "0x4a");
  n

let counter = Hacl_UInt32.of_int (Prims.parse_int "1")

let from_string s =
  let b = create (Hacl_UInt8.of_string "0") (String.length s) in
  for i = 0 to (String.length s - 1) do
    upd b i (Hacl_UInt8.of_string (string_of_int (code (String.get s i))))
  done;
  b
                
let print (b:int buffer) =
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

let plaintext = from_string "Ladies and Gentlemen of the class of '99: If I could offer you only one tip for the future, sunscreen would be it."
                            
let expected = "6E2E359A2568F98041BA0728DD0D6981E97E7AEC1D4360C20A27AFCCFD9FAE0BF91B65C5524733AB8F593DABCD62B3571639D624E65152AB8F530C359F0861D807CA0DBF500D6A6156A38E088A22B65E52BC514D16CCF806818CE91AB77937365AF90BBF74A35BE6B40B8EEDF2785E42874D\n"

let _ =
  let len = 114 in
  let ciphertext = create (uint8_to_sint8 0) 114 in
  let ctx = create 0 32 in
  (* chacha20_encrypt ciphertext key counter nonce plaintext 114; *)
  chacha_keysetup ctx key;
  chacha_ietf_ivsetup ctx nonce counter;
  chacha_encrypt_bytes ctx plaintext ciphertext len;

  print_string "Test key:\n";
  print_bytes key;
  print_string "Test nonce:\n";
  print_bytes nonce;
  print_string "Expected ciphertext:\n";
  print_string expected;
  print_string "Got ciphertext:\n";
  print_bytes ciphertext;
  let ok = "6e2e359a2568f98041ba0728dd0d6981e97e7aec1d4360c20a27afccfd9fae0bf91b65c5524733ab8f593dabcd62b3571639d624e65152ab8f530c359f0861d807ca0dbf500d6a6156a38e088a22b65e52bc514d16ccf806818ce91ab77937365af90bbf74a35be6b40b8eedf2785e42874d" in
  for i = 0 to 113 do
    if not(Hacl_UInt8.to_string_hex (index ciphertext i) = String.sub ok (2*i) 2) then
      failwith (Printf.sprintf "Ciphertext differs at byte %d: %s %s\n" i (Hacl_UInt8.to_string_hex (index ciphertext i)) (String.sub ok (2*i) 2)) 
  done;
  Printf.printf "TESTS ARE PASSING\n";
  Random.self_init();
  let max_len = 600 * 1024 in
  let rounds = 1 in
  let plain = create 0 (max_len) in
  let cipher = create 0 (max_len) in
  for i = 0 to max_len - 1 do upd plain i (Random.int(256)) done;
  let t1 = Sys.time() in
  for i = 1 to rounds do
    let ctx = create 0 32 in
    chacha_keysetup ctx key;
    chacha_ietf_ivsetup ctx nonce counter;
    chacha_encrypt_bytes ctx plain cipher max_len
  done;
  let t2 = Sys.time() in
  Printf.printf "Ellapsed time for %s with %d rounds and %d bytes of random data : %fs\n"
                "Chacha20"
                rounds
                max_len
                (t2 -. t1)

