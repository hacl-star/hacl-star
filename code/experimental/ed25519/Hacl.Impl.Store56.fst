module Hacl.Impl.Store56

module ST = FStar.HyperStack.ST
open FStar.HyperStack.All
open FStar.Mul

open Lib.IntTypes
open Lib.Buffer
open Lib.ByteBuffer

val hstore56_le:
    out:lbuffer uint8 32ul
  -> off:size_t{v off <= 21}
  -> x:uint64 -> //{v x < pow2 56} ->
  Stack unit
    (requires fun h -> live h out)
    (ensures  fun h0 _ h1 -> modifies (loc out) h0 h1)
let hstore56_le out off x =
  let b8 = sub out off 8ul in
  uint_to_bytes_le b8 x

val store_56:
    out:lbuffer uint8 32ul
  -> b:lbuffer uint64 5ul ->
  Stack unit
    (requires fun h -> live h out /\ live h b)
    (ensures  fun h0 _ h1 -> modifies (loc out) h0 h1)
let store_56 out b =
  let b0 = b.(0ul) in
  let b1 = b.(1ul) in
  let b2 = b.(2ul) in
  let b3 = b.(3ul) in
  let b4 = b.(4ul) in
  let b4 = to_u32 b4 in

  hstore56_le out 0ul b0;
  hstore56_le out 7ul b1;
  hstore56_le out 14ul b2;
  hstore56_le out 21ul b3;
  uint_to_bytes_le (sub out 28ul 4ul) b4
