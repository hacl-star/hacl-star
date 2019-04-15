module Poly1305.Equiv

open FStar.Mul
open FStar.Seq.Base
module S = Spec.Poly1305
module V = Poly1305.Spec_s

unfold let nat128 = Words_s.nat128
unfold let secrecy_level = Lib.IntTypes.secrecy_level
unfold let bytes = Lib.ByteSequence.bytes
unfold let nat_from_bytes_le (#l:secrecy_level) = Lib.ByteSequence.nat_from_bytes_le #l
unfold let nat_to_bytes_le (#l:secrecy_level) = Lib.ByteSequence.nat_to_bytes_le #l
unfold let size_block = S.size_block
unfold let key = S.key

let block_fun (text:bytes) (i:int) : nat128 =
  let len = length text in
  let nb = len / size_block in
  if 0 <= i && i <= nb then (
    let j1 = i * size_block in
    let j2 = if i < nb then i * size_block + size_block else length text in
    Math.Lemmas.pow2_le_compat 128 (8 * (j2 - j1));
    nat_from_bytes_le (Seq.slice text j1 j2))
  else
    0

val lemma_poly1305_equiv (text:bytes) (k:key) : Lemma
  (ensures (
    let inp = block_fun text in
    let pad = pow2 (8 * size_block) in
    let len = length text in
    let key_bytes = slice k 0 16 in
    let key_r:nat128 = nat_from_bytes_le key_bytes in
    let key_s:nat128 = nat_from_bytes_le (slice k 16 32) in
    let v = V.poly1305_hash key_r key_s inp len in
    0 <= v /\ v < pow2 128 /\
    nat_to_bytes_le 16 v == S.poly1305 text k
  ))
