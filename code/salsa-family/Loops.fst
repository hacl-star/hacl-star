module Loops

open FStar.Buffer
open Spec.Chacha20
open Combinators
open Hacl.Spec.Endianness

assume val rounds:
  st:buffer Hacl.UInt32.t{length st = 16} ->
  Stack unit
    (requires (fun h -> live h st))
    (ensures (fun h0 _ h1 -> live h0 st /\ live h1 st /\ modifies_1 st h0 h1
      /\ (let s = reveal_h32s (as_seq h0 st) in
         let s' = reveal_h32s (as_seq h1 st) in
         s' == rounds s)))

assume val rounds':
  st:buffer Hacl.UInt32.t{length st = 16} ->
  Stack unit
    (requires (fun h -> live h st))
    (ensures (fun h0 _ h1 -> live h0 st /\ live h1 st /\ modifies_1 st h0 h1
      /\ (let s = reveal_h32s (as_seq h0 st) in
         let s' = reveal_h32s (as_seq h1 st) in
         s' == Spec.Salsa20.rounds s)))

assume val sum_states:
  st:buffer Hacl.UInt32.t{length st = 16} ->
  st':buffer Hacl.UInt32.t{length st' = 16 /\ disjoint st st'} ->
  Stack unit
    (requires (fun h -> live h st /\ live h st'))
    (ensures  (fun h0 _ h1 -> live h0 st /\ live h1 st /\ live h0 st' /\ modifies_1 st h0 h1
      /\ (let s1 = as_seq h1 st in let s = as_seq h0 st in let s' = as_seq h0 st' in
         s1 == Combinators.seq_map2 (fun x y -> Hacl.UInt32.(x +%^ y)) s s')))

assume val xor_bytes:
  output:buffer Hacl.UInt8.t ->
  in1:buffer Hacl.UInt8.t{disjoint in1 output} ->
  in2:buffer Hacl.UInt8.t{disjoint in2 output} ->
  len:FStar.UInt32.t{FStar.UInt32.v len = length output /\ length output = length in1 /\ length in1 = length in2} ->
  Stack unit
    (requires (fun h -> live h output /\ live h in1 /\ live h in2))
    (ensures (fun h0 _ h1 -> live h1 output /\ live h0 in1 /\ live h0 in2 /\ modifies_1 output h0 h1
      /\ (let out = as_seq h1 output in
         let in1 = as_seq h0 in1 in
         let in2 = as_seq h0 in2 in
         out == seq_map2 (fun x y -> Hacl.UInt8.(x ^^ y)) in1 in2)))
