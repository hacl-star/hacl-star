module Hacl.Impl.SHA2.Core
open FStar.Mul
module ST = FStar.HyperStack.ST
open FStar.HyperStack
open FStar.HyperStack.All
open Lib.IntTypes
open Lib.Sequence
open Lib.Buffer
open Lib.IntVector
open Spec.Hash.Definitions
open Hacl.Hash.Definitions

val sha256: hash:lbuffer uint8 32ul -> len:size_t -> b:buffer uint8{length b == v len} ->
    Stack unit
    (requires (fun h0 -> live h0 b /\ live h0 hash /\ disjoint hash b))
    (ensures (fun h0 _ h1 -> modifies (loc hash) h0 h1))

val sha256_4: r0:lbuffer uint8 32ul ->
              r1:lbuffer uint8 32ul ->
              r2:lbuffer uint8 32ul ->
              r3:lbuffer uint8 32ul ->
              len:size_t ->
              b0:buffer uint8{length b0 == v len} ->
              b1:buffer uint8{length b1 == v len} ->
              b2:buffer uint8{length b2 == v len} ->
              b3:buffer uint8{length b3 == v len} ->
    Stack unit
    (requires (fun h0 -> live h0 b0 /\ live h0 b1 /\ live h0 b2 /\ live h0 b3 /\ 
                       live h0 r0 /\ live h0 r1 /\ live h0 r2 /\ live h0 r3))
    (ensures (fun h0 _ h1 -> modifies (loc r0 |+| loc r1 |+| loc r2 |+| loc r3) h0 h1))


