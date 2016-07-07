module AEAD.AES256_GCM

open FStar.Ghost
open FStar.HyperStack
open FStar.HST
open Hacl.UInt8
open Hacl.Cast
open Hacl.SBuffer
open Symmetric.AES
open GCM

#set-options "--lax"

(* Block cipher function AES256 *)

private val aes256: key:u8s{length key = 32} ->
    input:u8s{length input = 16 /\ disjoint key input} ->
    out:u8s{length out = 16 /\ disjoint key out /\ disjoint input out} ->
    STL unit
    (requires (fun h -> live h key /\ live h input /\ live h out))
    (ensures (fun h0 r h1 -> live h1 key /\ live h1 input /\ live h1 out))	   
let aes256 key input out =
  let w = create (uint8_to_sint8 0uy) 240ul in
  let sbox = create (uint8_to_sint8 0uy) 256ul in
  let inv_sbox = create (uint8_to_sint8 0uy) 256ul in
  mk_sbox sbox;
  mk_inv_sbox inv_sbox;
  keyExpansion key w sbox;
  cipher out input w sbox

(* Main AEAD functions *)
val aead_encrypt: plaintext:u8s ->
    tag:u8s{length tag = 16 /\ disjoint plaintext tag} ->
    key:u8s{length tag = 32 /\ disjoint plaintext key /\ disjoint tag key} ->
    nonce:u8s{length nonce = 12 /\ disjoint plaintext nonce /\ disjoint tag nonce /\ disjoint key nonce} ->
    ciphertext:u8s{length ciphertext = length plaintext /\ disjoint plaintext ciphertext /\ disjoint tag ciphertext /\ disjoint key ciphertext /\ disjoint nonce ciphertext} ->
    clen:nat{length ciphertext = clen} ->
    ad:u8s{disjoint plaintext ad /\ disjoint tag ad /\ disjoint key ad /\ disjoint nonce ad /\ disjoint ciphertext ad} ->
    adlen:nat{length ad = adlen} ->
    STL unit
    (requires (fun h -> live h plaintext /\ live h tag /\ live h key /\ live h nonce /\ live h ciphertext /\ live h ad))
    (ensures (fun h0 r h1 -> live h1 plaintext /\ live h1 tag /\ live h1 key /\ live h1 nonce /\ live h1 ciphertext /\ live h1 ad))
let aead_encrypt plaintext tag key nonce ciphertext clen ad adlen =
    GCM.encrypt #32 aes256 key nonce ad adlen plaintext ciphertext clen tag

(* TODO: AEAD decrypt function *)
