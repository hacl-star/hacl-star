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

(* #set-options "--lax" *)

(* Block cipher function AES256 *)

private val aes256: key:u8s{length key = 32} -> input:u8s{length input = 16} ->
    out:u8s{length out = 16} -> STL unit
      (requires (fun h -> live h key /\ live h input /\ live h out 
	/\ disjoint key input /\ disjoint key out /\ disjoint input out))
      (ensures  (fun h0 _ h1 -> live h1 out /\ modifies_1 out h0 h1))

let lemma_aux_001 (w:u8s{length w >= 240}) : Lemma (length w >= 4 * UInt32.v Symmetric.AES.nb * (UInt32.v nr+1)) = ()

#reset-options "--z3timeout 5"

let aes256 key input out =
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
  pop_frame()

(* Main AEAD functions *)
val aead_encrypt: ciphertext:u8s -> tag:u8s{length tag = 16} ->
    key:u8s{length key = 32} -> nonce:u8s{length nonce = 12} ->
    plaintext:u8s{length plaintext = length ciphertext} ->
    len:u32{length ciphertext = U32.v len} ->
    ad:u8s -> adlen:u32{length ad = U32.v adlen} ->
    Stl unit
let aead_encrypt ciphertext tag key nonce plaintext len ad adlen =
    GCM.encrypt #32 aes256 ciphertext tag key nonce ad adlen plaintext len

(* TODO: AEAD decrypt function *)
