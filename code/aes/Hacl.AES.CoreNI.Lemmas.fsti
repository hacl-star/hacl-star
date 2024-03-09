module Hacl.AES.CoreNI.Lemmas

open Lib.IntTypes
open Lib.ByteSequence

open Hacl.AES.Common

module LSeq = Lib.Sequence

val uints_bytes_be_lemma:
  b:LSeq.lseq uint8 16 ->
  Lemma (
    uints_to_bytes_be (uints_from_bytes_be #U128 #SEC #1 b) == b)

val vec_set_counter_lemma:
  b:LSeq.lseq uint8 16 
  -> c:size_nat ->
  Lemma (
    let counter = uint #U32 #SEC c in
    let n = uints_from_bytes_be #U32 #SEC #4 b in
    LSeq.update_sub b 12 4 (nat_to_bytes_be 4 c) ==
    uints_to_bytes_be (uints_from_bytes_be #U128 #SEC #1 (uints_to_bytes_be (LSeq.upd n 3 counter))))

val vec_xor_lemma:
  b1:LSeq.lseq uint128 1 
  -> b2:LSeq.lseq uint128 1 ->
  Lemma (
    LSeq.map2 (logxor #U8) (uints_to_bytes_be b1) (uints_to_bytes_be b2) ==
    uints_to_bytes_be (LSeq.map2 ( ^. ) b1 b2))

val uints_to_bytes_u8_16_le:
  b:LSeq.lseq uint128 1 ->
  Lemma (
    u8_16_to_le (uints_to_bytes_be #U128 #SEC #1 b) ==
    uints_to_bytes_le #U128 #SEC #1 b)

val vec_xor_lemma_le:
  b1:LSeq.lseq uint8 16
  -> b2:LSeq.lseq uint128 1 ->
  Lemma (
    uints_to_bytes_le (LSeq.map2 ( ^. ) (uints_from_bytes_le b1) b2) ==
    u8_16_to_le (LSeq.map2 (logxor #U8) (u8_16_to_le b1) (uints_to_bytes_be b2)))

val vec_shift_l_32_lemma:
  p:LSeq.lseq uint8 16{LSeq.index p 12 == u8 0 /\
                       LSeq.index p 13 == u8 0 /\
                       LSeq.index p 14 == u8 0 /\
                       LSeq.index p 15 == u8 0}
  -> b:LSeq.lseq uint128 1 ->
  Lemma (
    LSeq.update_sub p 0 12 (LSeq.sub (uints_to_bytes_be b) 4 12) ==
    uints_to_bytes_be (LSeq.map (shift_left_i (size 32)) b))

val vec_create4_3_lemma:
  b:LSeq.lseq uint8 16 ->
  Lemma (
    let i = LSeq.index (uints_from_bytes_be #U32 #SEC #4 b) 3 in
    let b0 = LSeq.update_sub b 8 4 (LSeq.sub b 12 4) in
    uints_to_bytes_be (LSeq.create4 i i i i) ==
    LSeq.update_sub b0 0 8 (LSeq.sub b0 8 8))

val vec_create4_2_lemma:
  b:LSeq.lseq uint8 16 ->
  Lemma (
    let i = LSeq.index (uints_from_bytes_be #U32 #SEC #4 b) 2 in
    let b0 = LSeq.update_sub b 12 4 (LSeq.sub b 8 4) in
    uints_to_bytes_be (LSeq.create4 i i i i) ==
    LSeq.update_sub b0 0 8 (LSeq.sub b0 8 8))

val uints_bytes_le_lemma:
  b:LSeq.lseq uint8 16 ->
  Lemma (
    u8_16_to_le (uints_to_bytes_be (uints_from_bytes_le #U128 #SEC #1 b)) == b)

val vec_u128_to_u8:
  b:LSeq.lseq uint128 1 ->
  Lemma (uints_from_bytes_be #U8 #SEC #16 (uints_to_bytes_be b) ==
    uints_to_bytes_be b)

val vec_u8_16:
  b:LSeq.lseq uint8 16 ->
  Lemma (uints_to_bytes_be b == b)
