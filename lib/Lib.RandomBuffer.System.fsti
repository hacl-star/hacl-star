module Lib.RandomBuffer.System

open Lib.IntTypes
open Lib.Buffer

open FStar.HyperStack.All


val randombytes:
    buf: buffer uint8
  -> len: size_t{v len == length buf} ->
  Stack bool
  (requires (fun h -> live h buf))
  (ensures (fun h0 _ h1 -> modifies1 buf h0 h1))
