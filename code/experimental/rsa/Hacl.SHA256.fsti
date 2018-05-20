module Hacl.SHA256

open FStar.HyperStack.All
open Spec.Lib.IntBuf.Lemmas
open Spec.Lib.IntBuf
open Spec.Lib.IntTypes
open FStar.Mul

module Buffer = Spec.Lib.IntBuf

(* SHA 256 *)
inline_for_extraction
let hLen:size_t = size 32

val hash:
  #len:size_nat ->
  mHash:Buffer.lbuffer uint8 (v hLen) ->
  clen:size_t{v clen == len} ->
  m:Buffer.lbuffer uint8 len -> Stack unit
  (requires (fun h -> live h mHash /\ live h m /\ disjoint m mHash))
  (ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 mHash h0 h1))
