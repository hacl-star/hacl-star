module Lib.PrintBuffer

open Lib.IntTypes
open Lib.Buffer

open FStar.HyperStack.All


val print_bytes:
    len: size_t
  -> buf: lbuffer uint8 len ->
  Stack unit
  (requires (fun h -> live h buf))
  (ensures (fun h0 _ h1 -> modifies0 h0 h1))

val print_compare:
    len: size_t
  -> buf0: lbuffer uint8 len
  -> buf1: lbuffer uint8 len ->
  Stack unit
  (requires (fun h -> live h buf0 /\ live h buf1))
  (ensures (fun h0 _ h1 -> modifies0 h0 h1))

val print_compare_display:
     len: size_t
  -> buf0: clbuffer uint8 len
  -> buf1: clbuffer uint8 len ->
  Stack unit
  (requires (fun h -> live h buf0 /\ live h buf1))
  (ensures (fun h0 _ h1 -> modifies0 h0 h1))

val result_compare_display:
     len: size_t
  -> buf0: clbuffer uint8 len
  -> buf1: clbuffer uint8 len ->
  Stack bool
  (requires (fun h -> live h buf0 /\ live h buf1))
  (ensures (fun h0 _ h1 -> modifies0 h0 h1))
