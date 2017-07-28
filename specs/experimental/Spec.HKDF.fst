module Spec.HKDF

module ST = FStar.HyperStack.ST

open FStar.Mul
open FStar.Seq
open FStar.UInt32

open Spec.Loops
open Spec.Lib

module U8 = FStar.UInt8

module Hash = Spec.SHA2
module HMAC = Spec.HMAC


(* Extraction function *)
val hkdf_extract:
  a    :Hash.hash_alg ->
  salt :bytes{Seq.length salt < Hash.max_input8 a} ->
  ikm  :bytes{Seq.length ikm + Hash.size_block a < Hash.max_input8 a} ->
  Tot (prk:bytes{Seq.length prk = Hash.size_hash a})

let hkdf_extract a salt ikm = HMAC.hmac a salt ikm


(* Core Expansion function *)
val hkdf_expand_core :
  a       :Hash.hash_alg ->
  prk     :bytes{Hash.size_hash a <= Seq.length prk /\ Seq.length prk < Hash.max_input8 a} ->
  info    :bytes{Hash.size_hash a + Seq.length info + 1 + Hash.size_block a < Hash.max_input8 a} ->
  len     :nat{len <= 255 * (Hash.size_hash a)} ->
  n       :nat{n <= 255} ->
  t0       :bytes{length t0 = n * (Hash.size_hash a)} ->
  Tot (t1:bytes{Seq.length t1 = Seq.length t0 + (Hash.size_hash a)})

let rec hkdf_expand_core a okm prk info len n t =
  if Seq.length t < len && n + 1 <= 255 then
    let n = n + 1 in
    let t = HMAC.hmac a prk (t @| info @| bytes_of_int 1 n) in
    let ti = hkdf_expand_core a prk info len n t in
    t @| ti
  else empty_bytes

(* Expansion function *)
val hkdf_expand :
  a       :Hash.hash_alg ->
  prk     :bytes{Hash.size_hash a <= Seq.length prk /\ Seq.length prk < Hash.max_input8 a} ->
  info    :bytes{Hash.size_hash a + Seq.length info + 1 + Hash.size_block a < Hash.max_input8 a} ->
  len     :nat{len <= 255 * (Hash.size_hash a)} ->
  Tot (okm:bytes{Seq.length okm = len})

let hkdf_expand a prk info len =
  let okm_raw = hkdf_expand_core a prk info len 0 empty_bytes in
  Seq.slice okm_raw 0 len
