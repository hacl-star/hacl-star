module Lib.RandomBuffer.System

open Lib.IntTypes
open Lib.Buffer
module B = LowStar.Buffer

open FStar.HyperStack.All

open Lib.RandomSequence
module R = Lib.RandomSequence

[@@ deprecated "random_crypto" ]
val randombytes:
    buf: buffer uint8
  -> len: size_t{v len == length buf} ->
  Stack bool
  (requires (fun h -> live h buf))
  (ensures (fun h0 _ h1 -> modifies1 buf h0 h1))

// In order to be able to reason about disjointness, we make the entropy pointer
// recallable. Use Lib.Buffer.recall to recall that entropy_p is included
// in the current memory snapshot.
val entropy_p : b:lbuffer (Ghost.erased entropy) 1ul{ recallable b }

/// This function waits until it has received enough entropy before
/// generating random bytes. Note that it may wait for some time.
val crypto_random:
     buf: buffer uint8
  -> len: size_t{v len == length buf} ->
  Stack unit
  (requires (fun h0 ->
    live h0 buf /\
    disjoint buf entropy_p))
  (ensures (fun h0 () h1 ->
    modifies2 buf entropy_p h0 h1 /\
    begin
    let e0_v = B.deref h0 (entropy_p <: B.buffer (Ghost.erased entropy)) in
    let e1_v = B.deref h1 (entropy_p <: B.buffer (Ghost.erased entropy)) in
    let buf_v = B.as_seq h1 buf in
    (Ghost.reveal e1_v, buf_v) == R.crypto_random e0_v (size_v len)
    end))
