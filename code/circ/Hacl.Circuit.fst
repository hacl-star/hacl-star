module Hacl.Circuit

open Lib.Sliceable
open FStar.HyperStack.ST
open FStar.HyperStack

module IT = Lib.IntTypes
module B = Lib.Buffer

inline_for_extraction noextract
let p:nat = 128

inline_for_extraction noextract
val circ : circuit 1 p
inline_for_extraction noextract
let circ (i:nat{i<p}) : gate 1 i =
if i = 0 then Input 0 else Xor (i-1) (i-1)

inline_for_extraction noextract
let u32 = uN IT.U32 IT.PUB

let circ_lowstar :
    (input:B.lbuffer u32.t (IT.size 1)) ->
    (output:B.lbuffer u32.t (IT.size p)) ->
    Stack unit
      (requires (fun h ->
        B.live h input /\ B.live h output
        /\ B.disjoint input output
      ))
      (ensures  (fun h0 _ h1 -> forall(j:nat{j<1}). B.get h1 output j == circuit_def circ (xNxM_of_lbuffer h0 input) j))
= circuit_lowstar circ u32
