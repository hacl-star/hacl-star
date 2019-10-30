module Spec.Agile.KDF

open FStar.Mul

open Lib.IntTypes
open Lib.Sequence
open Lib.ByteSequence
open Lib.LoopCombinators

module Hash = Spec.Agile.Hash
module HMAC = Spec.Agile.HMAC


let build_label secret label context len =
  let llen = length label in
  let clen = length context in
  let size_hkdf_label : size_nat = numbytes U16 + numbytes U8 + llen + numbytes U8 + clen in
  let kdf_label = create size_hkdf_label (u8 0) in
  let kdf_label = update_sub kdf_label 0 (numbytes U16) (uint_to_bytes_be (u16 len)) in
  let kdf_label = update_sub kdf_label (numbytes U16) (numbytes U8) (uint_to_bytes_be #U8 (u8 llen)) in
  let kdf_label = update_sub kdf_label (numbytes U16 + numbytes U8) llen label in
  let kdf_label = update_sub kdf_label (numbytes U16 + numbytes U8 + llen) (numbytes U8) (uint_to_bytes_be #U8 (u8 clen)) in
  let kdf_label = update_sub kdf_label (numbytes U16 + numbytes U8 + llen + numbytes U8) clen context in
  kdf_label


let expand_label a secret label context len =
  admit(); // Spec.Agile.HKDF changed interface
  let hkdf_label = build_label secret label context len in
  Spec.Agile.HKDF.expand a secret hkdf_label len


let expand_derive_secret a secret label context =
  admit(); // Spec.Agile.HKDF changed interface
  let loghash = Hash.hash a context in
  expand_label a secret label loghash (Hash.size_hash a)
