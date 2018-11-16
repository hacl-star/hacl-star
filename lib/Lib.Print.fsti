module Lib.Print

open Lib.IntTypes
open Lib.Buffer

open FStar.HyperStack.ST

val print_bytes:
    #t:buftype
  -> len: size_t
  -> buf: lbuffer_t t uint8 len ->
  Stack unit
  (requires fun h -> live h buf)
  (ensures  fun h0 _ h1 -> modifies0 h0 h1)

val print_compare:
    #t0:buftype
  -> #t1:buftype
  -> len: size_t
  -> buf0: lbuffer_t t0 uint8 len
  -> buf1: lbuffer_t t1 uint8 len ->
  Stack unit
  (requires fun h -> live h buf0 /\ live h buf1)
  (ensures  fun h0 _ h1 -> modifies0 h0 h1)

val print_compare_display:
    #t0:buftype
  -> #t1:buftype
  -> len: size_t
  -> buf0: lbuffer_t t0 uint8 len
  -> buf1: lbuffer_t t1 uint8 len ->
  Stack unit
  (requires fun h -> live h buf0 /\ live h buf1)
  (ensures  fun h0 _ h1 -> modifies0 h0 h1)

val result_compare_display:
    #t0:buftype
  -> #t1:buftype
  -> len: size_t
  -> buf0: lbuffer_t t0 uint8 len
  -> buf1: lbuffer_t t1 uint8 len ->
  Stack bool
  (requires fun h -> live h buf0 /\ live h buf1)
  (ensures  fun h0 _ h1 -> modifies0 h0 h1)
