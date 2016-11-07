module Hacl.Test.Box

open FStar.Buffer

val main: unit -> ST FStar.Int32.t
  (requires (fun h -> True))
  (ensures  (fun h0 r h1 -> True))
let main () =
  push_frame();
  (* Sizes *)
  let len = 47ul in
  let len_64 = 47uL in
  let keysize = 32ul in
  let noncesize = 24ul in
  let macsize = 16ul in
  (* Storage buffers *)
  let pk1 = create 0uy keysize in
  let pk2 = create 0uy keysize in
  let nm1 = create 0uy keysize in
  let nm2 = create 0uy keysize in
  let ciphertext = create 0uy (FStar.UInt32 (len +^ 16ul)) in
  let ciphertext2 = create 0uy (FStar.UInt32 (len +^ 16ul)) in
  let mac = create 0uy macsize in

  let plaintext = create 0uy len in
  let result    = create 0uy len in
  let nonce = createL [
    0x00uy; 0x01uy; 0x02uy; 0x03uy;
    0x04uy; 0x05uy; 0x06uy; 0x07uy;
    0x08uy; 0x09uy; 0x10uy; 0x11uy;
    0x12uy; 0x13uy; 0x14uy; 0x15uy;
    0x16uy; 0x17uy; 0x18uy; 0x19uy;
    0x20uy; 0x21uy; 0x22uy; 0x23uy
    ] in
  let sk1 = createL [
    0x00uy; 0x01uy; 0x02uy; 0x03uy;
    0x04uy; 0x05uy; 0x06uy; 0x07uy;
    0x08uy; 0x09uy; 0x10uy; 0x11uy;
    0x12uy; 0x13uy; 0x14uy; 0x15uy;
    0x16uy; 0x17uy; 0x18uy; 0x19uy;
    0x20uy; 0x21uy; 0x22uy; 0x23uy;
    0x24uy; 0x25uy; 0x26uy; 0x27uy;
    0x28uy; 0x29uy; 0x30uy; 0x31uy
    ] in
  let sk2 = createL [
    0x31uy; 0x30uy; 0x29uy; 0x28uy;
    0x27uy; 0x26uy; 0x25uy; 0x24uy;
    0x23uy; 0x22uy; 0x21uy; 0x20uy;
    0x19uy; 0x18uy; 0x17uy; 0x16uy;
    0x15uy; 0x14uy; 0x13uy; 0x12uy;
    0x11uy; 0x10uy; 0x09uy; 0x08uy;
    0x07uy; 0x06uy; 0x05uy; 0x04uy;
    0x03uy; 0x02uy; 0x01uy; 0x00uy
    ] in
  let basepoint = create 0uy 32ul in
  basepoint.(0ul) <- 9uy;
  Hacl.EC.Curve25519.exp pk1 basepoint sk1;
  Hacl.EC.Curve25519.exp pk2 basepoint sk2;

  let _ = Hacl.Box.crypto_box_beforenm nm1 pk1 sk2 in
  let _ = Libsodium.crypto_box_beforenm nm2 pk2 sk1 in
  let _ = Hacl.Box.crypto_box_easy_afternm ciphertext plaintext len_64 nonce nm1 in
  let _ = Libsodium.crypto_box_easy_afternm ciphertext2 plaintext len_64 nonce nm2 in

  let str_encr1 = createL [ 0y ] in
  TestLib.compare_and_print str_encr1 ciphertext2 ciphertext len;

  let _ = Hacl.Box.crypto_box_easy ciphertext plaintext len_64 nonce pk1 sk2 in
  let _ = Libsodium.crypto_box_open_easy result ciphertext (FStar.UInt64 (len_64 +^ 16uL)) nonce pk2 sk1 in

  let str_encr2 = createL [ 0y ] in
  TestLib.compare_and_print str_encr2 plaintext result len;
  pop_frame();
  C.exit_success
