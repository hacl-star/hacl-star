module AEAD.AES256_GCM

open FStar.Mul
open FStar.Ghost
open FStar.HyperStack
open FStar.HST
open Hacl.UInt8
open Hacl.Cast
open Hacl.SBuffer
open Symmetric.AES
open GCM

module U32 = FStar.UInt32

let lemma_aux_001 (w:u8s{length w >= 240}) : Lemma (length w >= 4 * U32.v nb * (U32.v nr+1)) = ()

(* Block cipher function AES256 *)
private val aes256: key:u8s{length key = 32} ->
    input:u8s{length input = 16 /\ disjoint key input} ->
    out:u8s{length out = 16 /\ disjoint key out /\ disjoint input out} ->
    STL unit
      (requires (fun h -> live h key /\ live h input /\ live h out))
      (ensures  (fun h0 _ h1 -> live h1 key /\ live h1 input /\ live h1 out
        /\ modifies_1 out h0 h1))
let aes256 key input out =
  let h0 = HST.get() in
  push_frame();
  let tmp = create (uint8_to_sint8 0uy) 752ul in
  let w = sub tmp 0ul 240ul in
  let sbox = sub tmp 240ul 256ul in
  let inv_sbox = sub tmp 496ul 256ul in
  lemma_aux_001 w;
  mk_sbox sbox;
  mk_inv_sbox inv_sbox;
  keyExpansion key w sbox;
  cipher out input w sbox;
  pop_frame();
  let h1 = HST.get() in
  assert(live h1 key /\ live h1 input /\ live h1 out /\ modifies_1 out h0 h1)

(* Main AEAD functions *)
val aead_encrypt: ciphertext:u8s ->
    tag:u8s{length tag = 16 /\ disjoint ciphertext tag} ->
    key:u8s{length key = 32 /\ disjoint ciphertext key /\ disjoint tag key} ->
    iv:u8s{length iv = 12 /\ disjoint ciphertext iv /\ disjoint tag iv /\ disjoint key iv} ->
    plaintext:u8s{length plaintext = length ciphertext /\ disjoint ciphertext plaintext /\ disjoint tag plaintext /\ disjoint key plaintext /\ disjoint iv plaintext} ->
    len:u32{length ciphertext = U32.v len} ->
    ad:u8s{disjoint ciphertext ad /\ disjoint tag ad /\ disjoint key ad /\ disjoint iv ad /\ disjoint plaintext ad} ->
    adlen:u32{length ad = U32.v adlen} ->
    STL unit
    (requires (fun h -> live h ciphertext /\ live h tag /\ live h key /\ live h iv /\ live h plaintext /\ live h ad))
    (ensures (fun h0 _ h1 -> live h1 ciphertext /\ live h1 tag /\ live h1 key /\ live h1 iv /\ live h1 plaintext /\ live h1 ad
      /\ modifies_2 ciphertext tag h0 h1))
let aead_encrypt ciphertext tag key iv plaintext len ad adlen =
    GCM.encrypt #32 aes256 ciphertext tag key iv ad adlen plaintext len

(* TODO: AEAD decrypt function *)
