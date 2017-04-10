module Hacl.Impl.Store56

open FStar.Buffer
open Hacl.UInt64
open Hacl.Endianness

let hint8_p = buffer Hacl.UInt8.t
let qelem   = buffer Hacl.UInt64.t

val store_56:
  out:hint8_p{length out = 32} ->
  b:qelem ->
  Stack unit
    (requires (fun h -> live h out /\ live h b))
    (ensures (fun h0 _ h1 -> live h1 out /\ live h0 b /\ modifies_1 out h0 h1))
let store_56 out b =
  let b0 = b.(0ul) in
  let b1 = b.(1ul) in
  let b2 = b.(2ul) in
  let b3 = b.(3ul) in
  let b4 = b.(4ul) in
  let b4 = Hacl.Cast.sint64_to_sint32 b4 in
  hstore64_le (Buffer.sub out 0ul  8ul) b0;
  hstore64_le (Buffer.sub out 7ul  8ul) b1;
  hstore64_le (Buffer.sub out 14ul 8ul) b2;
  hstore64_le (Buffer.sub out 21ul 8ul) b3;
  hstore32_le (Buffer.sub out 28ul 4ul) b4
