module GCM

open FStar.Mul
open FStar.Ghost
open FStar.HyperStack
open FStar.HST
open Hacl.UInt8
open Hacl.Cast
open Hacl.SBuffer
open Symmetric.AES

#set-options "--lax"

(* Define a type for all 16-byte block cipher algorithm *)
type cipher_alg (k: pos) = key:u8s{length key = k} ->
    input:u8s{length input = 16 /\ disjoint key input} ->
    out:u8s{length out = 16 /\ disjoint key out /\ disjoint input out}
    -> STL unit
    (requires (fun h -> live h key /\ live h input /\ live h out))
    (ensures (fun h0 r h1 -> live h1 key /\ live h1 input /\ live h1 out
        /\ modifies_1 out h0 h1))

(* val u8s_to_gf128: block:u8s{length block = 16} -> St gf128 *)

val encrypt: #k:pos -> cipher_alg k -> key:u8s{length key = k} ->
    iv:u8s{length iv = 12 /\ disjoint key iv} ->
    aad:u8s{disjoint key aad /\ disjoint iv aad} ->
    aad_len:nat{length aad = aad_len} ->
    plaintext:u8s{disjoint key plaintext /\ disjoint iv plaintext /\ disjoint aad plaintext} ->
    ciphertext:u8s{length ciphertext = length plaintext /\ disjoint key ciphertext /\ disjoint iv ciphertext /\ disjoint aad ciphertext /\ disjoint plaintext ciphertext} ->
    c_len:nat{length ciphertext = c_len} ->
    tag:u8s{length tag = 16 /\ disjoint key tag /\ disjoint iv tag /\ disjoint aad tag /\ disjoint plaintext tag /\ disjoint ciphertext tag}
    -> STL unit
    (requires (fun h -> live h key /\ live h iv /\ live h aad /\ live h plaintext /\ live h ciphertext /\ live h tag))
    (ensures (fun h0 r h1 -> live h1 key /\ live h1 iv /\ live h1 aad /\ live h1 plaintext /\ live h1 ciphertext /\ live h1 tag))
let encrypt #k cipher key iv aad aad_len p c c_len tag =
    ()
    (*
    let len_a = length a in
    *)
