module AEAD.AES256_GCM

open FStar.Ghost
open FStar.HyperStack
open FStar.HST
open Hacl.UInt8
open Hacl.Cast
open Hacl.SBuffer
open Symmetric.AES
open GCM

module U32 = FStar.UInt32

#set-options "--lax"

(* Block cipher function AES256 *)

private val aes256: key:u8s{length key = 32} -> input:u8s{length input = 16} ->
    out:u8s{length out = 16} -> Stl unit

let aes256 key input out =
  push_frame();
  let w = create (uint8_to_sint8 0uy) 240ul in
  let sbox = create (uint8_to_sint8 0uy) 256ul in
  let inv_sbox = create (uint8_to_sint8 0uy) 256ul in
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
