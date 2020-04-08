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

