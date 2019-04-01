module Arch.BufferFriend

module B = LowStar.Buffer
module LI = Lib.IntTypes
module BS = Lib.ByteSequence
module FE = FStar.Endianness
module HS = FStar.HyperStack
module DV = LowStar.BufferView.Down
module UV = LowStar.BufferView.Up

open Words_s
open Types_s
open FStar.Mul
open FStar.Seq.Base

val to_bytes (s:seq UInt8.t) : GTot (b:BS.bytes{b === s /\ length b == length s})
val of_bytes (b:BS.bytes) : GTot (s:seq UInt8.t{b === s /\ length b == length s})

val lemma_to_bytes_slice (s:seq UInt8.t) (i j:nat) : Lemma
  (requires i <= j /\ j <= length s)
  (ensures to_bytes (slice s i j) == slice (to_bytes s) i j)
  [SMTPat (to_bytes (slice s i j))]

val lemma_of_bytes_slice (b:BS.bytes) (i j:nat) : Lemma
  (requires i <= j /\ j <= length b)
  (ensures of_bytes (slice b i j) == slice (of_bytes b) i j)
  [SMTPat (of_bytes (slice b i j))]

val lemma_up_as_seq_index (#b:_) (h:HS.mem) (vb:UV.buffer b) (i:nat) : Lemma
  (requires i < length (UV.as_seq h vb) /\ UV.View?.n (UV.get_view vb) == 8) // TODO: generalize this beyond n = 8
  (ensures (
    let s0 = DV.as_seq h (UV.as_down_buffer vb) in
    let v = UV.get_view vb in
    let n = UV.View?.n v in
    let start = i * n in
    0 <= start /\ start + n <= length s0 /\
    index (UV.as_seq h vb) i == UV.View?.get v (slice s0 start (start + n))
  ))

// TODO: this was copied out of Simplify_Sha.fst, but with the liveness requirement on b removed; we could consolidate the two versions
val same_seq_downview8 (b:B.buffer UInt8.t) (h:HS.mem) : Lemma
  (DV.as_seq h (DV.mk_buffer_view b (Views.down_view8)) == B.as_seq h b)

val lemma_le_to_n_is_nat_from_bytes (s:FE.bytes) : Lemma
  (ensures FE.le_to_n s == BS.nat_from_bytes_le (to_bytes s))
  (decreases (length s))

val lemma_n_to_le_is_nat_to_bytes (len:nat) (n:nat) : Lemma
  (requires n < pow2 (8 * len))
  (ensures FE.n_to_le len n == of_bytes (BS.nat_to_bytes_le len n))
  (decreases len)

val nat_from_bytes_le_is_four_to_nat (b:BS.bytes) : Lemma
  (requires length b == 4)
  (ensures
    BS.nat_from_bytes_le b ==
    Words.Four_s.four_to_nat 8 (Words.Four_s.four_map LI.uint_v (Words.Seq_s.seq_to_four_LE b))
  )

val nat_from_bytes_le_is_le_bytes_to_nat32 (b:BS.bytes) : Lemma
  (requires length b == 4)
  (ensures
    length (of_bytes b) == 4 /\
    BS.nat_from_bytes_le b == le_bytes_to_nat32 (Words.Seq_s.seq_uint8_to_seq_nat8 (of_bytes b))
  )

val nat_from_bytes_le_is_le_bytes_to_nat64 (b:BS.bytes) : Lemma
  (requires length b == 8)
  (ensures
    length (of_bytes b) == 8 /\
    BS.nat_from_bytes_le b == le_bytes_to_nat64 (Words.Seq_s.seq_uint8_to_seq_nat8 (of_bytes b))
  )

