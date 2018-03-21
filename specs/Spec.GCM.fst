module Spec.GCM

open FStar.Mul
open Spec.Lib.IntTypes
open Spec.Lib.IntSeq
open Spec.GF128

module GF = Spec.GF128

(* One-shot GCM interface *)

val ghash:
  text_len:size_nat ->
  text:lbytes text_len ->
  aad_len:size_nat ->
  aad:lbytes aad_len ->
  k:key -> Tot tag
let ghash text_len text aad_len aad k =
  (* gmul input: A || 0^v || C || 0^u || ceil(len(A))_64 || ceil(len(C))_64 *)
  let aad_padding:size_nat = (16 - (aad_len % 16)) % 16 in
  let text_padding:size_nat = (16 - (text_len % 16)) % 16 in
  (* Build ghash input *)
  let gmul_input_len = aad_len + aad_padding + text_len + text_padding + 16 in
  let gmul_input = create gmul_input_len (u8 0) in
  let gmul_input = update_slice gmul_input 0 aad_len aad  in
  (* padding is 0, so just skip those bytes *)
  let gmul_input = update_slice gmul_input (aad_len + aad_padding) (aad_len + aad_padding + text_len) text  in
  (* padding is 0, so just skip those bytes *)
  let aad_len_bytes = nat_to_bytes_be 8 (aad_len * 8) in
  let gmul_input = update_slice gmul_input (aad_len + aad_padding + text_len + text_padding) (aad_len + aad_padding + text_len + text_padding + 8) aad_len_bytes  in
  let text_len_bytes = nat_to_bytes_be 8 (text_len * 8) in
  let gmul_input = update_slice gmul_input (aad_len + aad_padding + text_len + text_padding + 8) (aad_len + aad_padding + text_len + text_padding + 16) text_len_bytes  in
  let h = GF.gmac gmul_input_len gmul_input k in
  h
