module Hacl.AES.Generic.Lemmas

open FStar.Mul
open Lib.IntTypes
open Lib.ByteSequence
open Lib.Sequence

open Spec.AES
open Hacl.Impl.AES.Core

val key_to_bytes_lemma:
  m:m_spec{m == MAES \/ m == M32}
  -> a: variant
  -> b:lseq (stelem m) ((num_rounds a-1) * (v (klen m)))
  -> i:nat{i < (num_rounds a-1)} ->
  Lemma (sub (keys_to_bytes m a b) (i*16) 16 == key_to_bytes m (sub b (i * v (klen m)) (v (klen m))))

val keyx_to_bytes_lemma:
  m:m_spec{m == MAES \/ m == M32}
  -> a: variant
  -> b:lseq (stelem m) ((num_rounds a+1) * (v (klen m)))
  -> i:nat{i < (num_rounds a+1)} ->
  Lemma (sub (keyx_to_bytes m a b) (i*16) 16 == key_to_bytes m (sub b (v (klen m) * i) (v (klen m))))

val keys_to_bytes_lemma:
  m:m_spec{m == MAES \/ m == M32}
  -> a: variant
  -> b:lseq (stelem m) ((num_rounds a+1) * (v (klen m))) ->
  Lemma (sub (keyx_to_bytes m a b) 16 ((num_rounds a-1) * 16) ==
    keys_to_bytes m a (sub b (v (klen m)) (v (klen m) * (num_rounds a-1))))

val keyx_zero_lemma:
  m:m_spec{m == MAES \/ m == M32}
  -> a: variant
  -> b:lseq (stelem m) ((num_rounds a+1) * (v (klen m))) ->
  Lemma 
  (requires (b == Seq.create ((num_rounds a+1) * v (klen m)) (elem_zero m)))
  (ensures (keyx_to_bytes m a b == create ((num_rounds a+1) * 16) (u8 0)))

val u8_16_to_le_lemma:
  x:lseq uint8 16 ->
  Lemma (Hacl.AES.Common.u8_16_to_le (Hacl.AES.Common.u8_16_to_le x) == x)
