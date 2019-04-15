module AES_stdcalls

open X64.CPU_Features_s
open FStar.HyperStack.ST
module B = LowStar.Buffer
module HS = FStar.HyperStack
module DV = LowStar.BufferView.Down
module UV = LowStar.BufferView.Up
open FStar.Mul
open Words_s
open Words.Seq_s
open AES_s
open Interop.Base
open Types_s

unfold
let uint8_p = B.buffer UInt8.t

let length_aux (b:uint8_p) : Lemma
  (requires B.length b = 176)
  (ensures DV.length (get_downview b) % 16 = 0) = 
    let db = get_downview b in
    DV.length_eq db

let length_aux2 (b:uint8_p) : Lemma
  (requires B.length b = 240)
  (ensures DV.length (get_downview b) % 16 = 0) = 
    let db = get_downview b in
    DV.length_eq db

inline_for_extraction unfold
let key_offset (a: algorithm { a = AES_128 \/ a = AES_256 }) =
  match a with
  | AES_128 -> 176
  | AES_256 -> 240

inline_for_extraction unfold
let key_length (a: algorithm { a = AES_128 \/ a = AES_256 }) =
  match a with
  | AES_128 -> 16
  | AES_256 -> 32

inline_for_extraction
let key_expansion_st (a: algorithm { a = AES_128 \/ a = AES_256 }) =
  (input_key_b:uint8_p) ->
  (output_key_expansion_b:uint8_p) ->
  Stack unit
    (requires fun h0 ->
      B.disjoint input_key_b output_key_expansion_b /\

      B.live h0 input_key_b /\ B.live h0 output_key_expansion_b /\

      B.length input_key_b = key_length a /\
      B.length output_key_expansion_b = key_offset a /\

      aesni_enabled)
    (ensures fun h0 _ h1 ->
      B.modifies (B.loc_buffer output_key_expansion_b) h0 h1 /\

      (let key = seq_nat8_to_seq_nat32_LE (seq_uint8_to_seq_nat8 (B.as_seq h0 input_key_b)) in
      Seq.equal (B.as_seq h1 output_key_expansion_b)
         (seq_nat8_to_seq_uint8 (le_seq_quad32_to_bytes (key_to_round_keys_LE a key)))))

inline_for_extraction
val aes128_key_expansion_stdcall: key_expansion_st AES_128

inline_for_extraction
val aes256_key_expansion_stdcall: key_expansion_st AES_256
