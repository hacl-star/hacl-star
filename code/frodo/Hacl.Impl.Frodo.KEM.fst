module Hacl.Impl.Frodo.KEM

open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Mul

open LowStar.Buffer

open Lib.IntTypes
open Lib.Buffer
open Lib.Memzero0

open Hacl.Impl.Matrix

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

inline_for_extraction noextract
val clear_matrix:
    #n1:size_t
  -> #n2:size_t{v n1 * v n2 <= max_size_t}
  -> m:matrix_t n1 n2
  -> Stack unit
    (requires fun h -> live h m)
    (ensures  fun h0 _ h1 -> modifies1 m h0 h1)

let clear_matrix #n1 #n2 m =
  memzero #uint16 m (n1 *! n2)


inline_for_extraction noextract
val clear_words_u8:
    #len:size_t
  -> b:lbytes len
  -> Stack unit
    (requires fun h -> live h b)
    (ensures  fun h0 _ h1 -> modifies (loc b) h0 h1)

let clear_words_u8 #len b =
  memzero #uint8 b len
