open Hacl_UInt8
open Hacl_SBuffer
open Symetric_AES

let print (b:u8s) =
  for i = 0 to (Array.length b.content - 1) do
    print_string (to_string_hex (index b i));
    if i mod 4 = 3 then print_string "\n"
  done;
  print_string "\n"
       
let _ =
  let zero = Hacl_Cast.uint8_to_sint8 0 in
  let plaintext = create zero 16 in
  let plaintext2 = create zero 16 in
  let key = create zero 32 in
  let ciphertext = create zero 16 in
  let w = create zero 240 in
  let sbox = create zero 256 in
  let inv_sbox = create zero 256 in
  (* Initialize the test vectors *)
  for i = 0 to 15 do
    upd plaintext i (Hacl_Cast.uint8_to_sint8 (i + (i lsl 4)));
    upd key (2*i) (Hacl_Cast.uint8_to_sint8 (2*i)); 
    upd key (2*i+1) (Hacl_Cast.uint8_to_sint8 (2*i+1))
  done;
  (* Initialize sboxes *)
  mk_sbox sbox;
  mk_inv_sbox inv_sbox;
  print_string "Initial plaintext:\n";
  print plaintext;
  keyExpansion key w sbox;
  cipher ciphertext plaintext w sbox;
  print_string "Resulting ciphertext:\n";  
  print ciphertext;
  inv_cipher plaintext2 ciphertext w inv_sbox;
  print_string "Decrypted plaintext:\n";  
  print plaintext2
  
