module Lib.CreateN

open FStar.Mul
open FStar.HyperStack
open FStar.HyperStack.ST

open Lib.IntTypes
open Lib.IntVector
open Lib.Buffer


#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

inline_for_extraction noextract
val create8_st: #a:Type0 -> st:lbuffer a 8ul
  -> v0:a -> v1:a -> v2:a -> v3:a
  -> v4:a -> v5:a -> v6:a -> v7:a ->
  Stack unit
  (requires fun h -> live h st)
  (ensures  fun h0 _ h1 -> modifies (loc st) h0 h1 /\
    as_seq h1 st == create8 v0 v1 v2 v3 v4 v5 v6 v7)


inline_for_extraction noextract
val create16_st: #a:Type0 -> st:lbuffer a 16ul
  -> v0:a -> v1:a -> v2:a -> v3:a
  -> v4:a -> v5:a -> v6:a -> v7:a
  -> v8:a -> v9:a -> v10:a -> v11:a
  -> v12:a -> v13:a -> v14:a -> v15:a ->
  Stack unit
  (requires fun h -> live h st)
  (ensures  fun h0 _ h1 -> modifies (loc st) h0 h1 /\
    as_seq h1 st == create16 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15)
