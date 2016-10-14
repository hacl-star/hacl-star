module AEAD.ChaCha20_Poly1305

open FStar.Ghost
open FStar.Heap
open SInt
open SInt.UInt8
open SInt.UInt32
open SBytes
open SBuffer

open Chacha
open Poly



//
// Helper function for padding
//

val pad_length_16: nat -> Tot nat
let pad_length_16 l = if l % 16 = 0 then 0 else 16 - (l % 16)

//
// Poly1305 key generation for the AEAD construction
//

val poly1305_generate_key: output:sbytes{length output = 64} -> key:sbytes{length key = 32 /\ disjoint output key} -> nonce:sbytes{length nonce = 8 /\ disjoint nonce output /\ disjoint nonce key} 
  -> ST unit
       (requires (fun h -> live h output /\ live h key /\ live h nonce))
       (ensures  (fun h0 r h1 -> live h1 output /\ live h1 key /\ live h1 nonce
                            /\ modifies_buf (only output) h0 h1))

let poly1305_generate_key output key nonce =
  (* Allocate the internal state *)
  let state = create #32 SInt.UInt32.zero 16  in
  (* Set the counter to zero *)
  let counter = SInt.UInt32.zero in
  (* Initialize the internal state *)
  initialize_state state key counter nonce;
  (* Call the Chacha block function to get the poly key *)
  chacha20_block output state key counter nonce


//
// AEAD construction
//

val aead_encrypt: ciphertext:sbytes -> tag:sbytes{length tag = 16 /\ disjoint tag ciphertext} -> key:sbytes{length key = 64 /\ disjoint key ciphertext /\ disjoint key tag} -> nonce:sbytes{length nonce = 12 /\ disjoint nonce ciphertext /\ disjoint nonce tag /\ disjoint nonce key} -> plaintext:sbytes{disjoint plaintext ciphertext /\ disjoint plaintext tag /\ disjoint plaintext key /\ disjoint plaintext nonce} -> plen:nat{plen = length plaintext} -> ad:sbytes{disjoint ad ciphertext /\ disjoint ad tag /\ disjoint ad key /\ disjoint ad nonce /\ disjoint ad plaintext} -> adlen:nat{adlen = length ad}
  -> ST unit
       (requires (fun h -> live h ciphertext /\ live h tag /\ live h key /\ live h nonce /\ live h plaintext /\ live h ad))
       (ensures  (fun h0 r h1 -> live h1 ciphertext /\ live h1 tag /\ live h1 key /\ live h1 nonce /\ live h1 plaintext /\ live h1 ad))

let aead_encrypt ciphertext tag key nonce plaintext plen ad adlen =
  (* Allocate the memory for the poly1305 one time key *)
  let otk = create #8 SInt.UInt8.zero 64 in
  (* Compute multiple lengths and perform required encodings *)
  let ciphertext_len = plen in
  let clen_64 = create #8 SInt.UInt8.zero 8 in
  let adlen_64 = create #8 SInt.UInt8.zero 8 in
  sbytes_of_uint64 clen_64 (SInt.UInt64.of_int ciphertext_len);
  sbytes_of_uint64 adlen_64 (SInt.UInt64.of_int adlen);
  let mac_data_len = adlen + (pad_length_16 adlen) + ciphertext_len + (pad_length_16 ciphertext_len) + 8 + 8 in
  (* Allocate the memory for the mac data *)
  let mac_data = create #8 SInt.UInt8.zero mac_data_len in
  (* Compute and store the poly1305 one time key *)
  poly1305_generate_key otk key nonce;
  (* Compute and store the ciphertext *)
  chacha20_encrypt ciphertext key (SInt.UInt32.one) nonce plaintext plen;
  (* Prepare the mac data *)
  blit ad 0 mac_data 0 adlen;
  let pos_after_ad = adlen + (pad_length_16 adlen) in
  blit ciphertext 0 mac_data pos_after_ad ciphertext_len;
  let pos_after_ctxt = pos_after_ad + ciphertext_len + (pad_length_16 ciphertext_len) in
  blit adlen_64 0 mac_data pos_after_ctxt 8;
  blit clen_64 0 mac_data (pos_after_ctxt + 8) 8;
  (* Compute and store the tag *)
  poly1305_mac tag mac_data mac_data_len otk


val aead_decrypt: plaintext:sbytes -> tag:sbytes{length tag = 16 /\ disjoint tag plaintext} -> key:sbytes{length key = 64 /\ disjoint key plaintext /\ disjoint key tag} -> nonce:sbytes{length nonce = 12 /\ disjoint nonce plaintext /\ disjoint nonce tag /\ disjoint nonce key} -> ciphertext:sbytes{disjoint ciphertext plaintext /\ disjoint ciphertext tag /\ disjoint ciphertext key /\ disjoint ciphertext nonce} -> clen:nat{clen = length ciphertext} -> ad:sbytes{disjoint ad plaintext /\ disjoint ad tag /\ disjoint ad key /\ disjoint ad nonce /\ disjoint ad ciphertext} -> adlen:nat{adlen = length ad}
  -> ST unit
       (requires (fun h -> live h plaintext /\ live h tag /\ live h key /\ live h nonce /\ live h ciphertext /\ live h ad))
       (ensures  (fun h0 r h1 -> live h1 plaintext /\ live h1 tag /\ live h1 key /\ live h1 nonce /\ live h1 ciphertext /\ live h1 ad))

let aead_decrypt plaintext tag key nonce ciphertext clen ad adlen =
  aead_encrypt plaintext tag key nonce ciphertext clen ad adlen
