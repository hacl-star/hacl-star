module Spec.Frodo.Clear

open FStar.Mul

open Lib.IntTypes
open Lib.Sequence

// REMARK:
// The C implementation clears one 32-bit word at a time, so we need [len]
// to be such that we clear an exact multiple of 32-bit words.
// This condition can be relaxed, but it's enough for our use in Frodo.

val clear_words_u16:
    nwords:size_nat{nwords % 2 == 0}
  -> b:seq uint16{nwords <= length b}
  -> res:lseq uint16 (length b)
let clear_words_u16 nwords b =
  create (length b) (u16 0)

val clear_words_u8:
    nwords:size_nat{nwords % 4 == 0}
  -> b:seq uint8{nwords <= length b}
  -> res:lseq uint8 (length b)
let clear_words_u8 nwords b =
  create (length b) (u8 0)
