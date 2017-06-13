module Loops_vec

open FStar.HyperStack.All

module ST = FStar.HyperStack.ST

open FStar.Buffer
open Spec.Chacha20
open C.Loops
open Hacl.Spec.Endianness
open Hacl.UInt32x4N

assume val rounds:
  st:buffer vec{length st = 4} ->
  Stack unit
    (requires (fun h -> live h st))
    (ensures (fun h0 _ h1 -> live h0 st /\ live h1 st /\ modifies_1 st h0 h1))

assume val rounds2:
  st:buffer vec{length st = 4} ->
  st':buffer vec{length st = 4} ->
  Stack unit
    (requires (fun h -> live h st /\ live h st'))
    (ensures (fun h0 _ h1 -> live h1 st /\ live h1 st' /\ modifies_2 st st' h0 h1))

assume val rounds3:
  st:buffer vec{length st = 4} ->
  st':buffer vec{length st = 4} ->
  st'':buffer vec{length st = 4} ->
  Stack unit
    (requires (fun h -> live h st /\ live h st' /\ live h st''))
    (ensures (fun h0 _ h1 -> live h1 st /\ live h1 st' /\ live h1 st'' /\  modifies_3 st st' st'' h0 h1))



assume val rounds16:
  st:buffer vec{length st = 16} ->
  Stack unit
    (requires (fun h -> live h st))
    (ensures (fun h0 _ h1 -> live h0 st /\ live h1 st /\ modifies_1 st h0 h1))


assume val sum_states16:
  st:buffer vec{length st = 16} ->
  st':buffer vec{length st = 16} ->
  Stack unit
    (requires (fun h -> live h st /\ live h st'))
    (ensures  (fun h0 _ h1 -> live h0 st /\ live h1 st /\ live h0 st' /\ modifies_1 st h0 h1))

assume val copy_state16:
  st:buffer vec{length st = 16} ->
  st':buffer vec{length st = 16} ->
  Stack unit
    (requires (fun h -> live h st /\ live h st'))
    (ensures  (fun h0 _ h1 -> live h0 st /\ live h1 st /\ live h0 st' /\ modifies_1 st h0 h1))

module U32 = Hacl.UInt32
open FStar.Mul

assume val vec_store16:
  output:buffer Hacl.UInt8.t ->
  st:buffer vec{length st = 16} ->
  vs:Hacl.UInt32.t{U32.v vs = 4 * U32.v vec_size} ->
  Stack unit
    (requires (fun h -> live h st /\ live h output))
    (ensures (fun h0 _ h1 -> live h0 st /\ live h1 st /\ live h1 output /\ modifies_1 output h0 h1))

assume val vec_gather16:
  st:buffer vec{length st = 16} ->
  input:buffer Hacl.UInt8.t ->
  vs:Hacl.UInt32.t{U32.v vs = 4 * U32.v vec_size} ->
  Stack unit
    (requires (fun h -> live h st /\ live h input))
    (ensures (fun h0 _ h1 -> live h0 st /\ live h1 st /\ live h1 input /\ modifies_1 st h0 h1))

assume val vec_xor16:
  output:buffer Hacl.UInt8.t{length output >=  64 * U32.v vec_size} ->
  input:buffer Hacl.UInt8.t{length input >=  64 * U32.v vec_size} ->
  st:buffer vec{length st = 16} ->
  vs:Hacl.UInt32.t{U32.v vs = 4 * U32.v vec_size} ->
  Stack unit
    (requires (fun h -> live h st /\ live h output /\ live h input))
    (ensures (fun h0 _ h1 -> live h0 st /\ live h1 st /\ live h1 output /\ modifies_1 output h0 h1))

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
