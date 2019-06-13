module Hacl.Impl.Load56

module ST = FStar.HyperStack.ST
open FStar.HyperStack.All
open FStar.Mul

open Lib.IntTypes
open Lib.Buffer
open Lib.ByteBuffer

val hload56_le:
    b:lbuffer uint8 64ul
  -> off:size_t{v off <= 56} ->
  Stack uint64
    (requires fun h -> live h b)
    (ensures fun h0 z h1 -> h0 == h1)
let hload56_le b off =
  let b8 = sub b off 8ul in
  let z  = uint_from_bytes_le b8 in
  let z' = z &. u64 0xffffffffffffff in
  z'

val load_64_bytes:
  out:lbuffer uint64 10ul
  -> b:lbuffer uint8 64ul ->
  Stack unit
    (requires fun h -> live h out /\ live h b)
    (ensures fun h0 _ h1 -> modifies (loc out) h0 h1)
let load_64_bytes out b =
  let b0 = hload56_le b 0ul in
  let b1 = hload56_le b 7ul in
  let b2 = hload56_le b 14ul in
  let b3 = hload56_le b 21ul in
  let b4 = hload56_le b 28ul in
  let b5 = hload56_le b 35ul in
  let b6 = hload56_le b 42ul in
  let b7 = hload56_le b 49ul in
  let b8 = hload56_le b 56ul in
  let b63 = b.(63ul) in
  let b9 = to_u64 b63 in
  Hacl.Bignum25519.make_u64_10 out b0 b1 b2 b3 b4 b5 b6 b7 b8 b9

val hload56_le':
    b:lbuffer uint8 32ul
  -> off:size_t{v off <= 21} ->
  Stack uint64
    (requires fun h -> live h b)
    (ensures fun h0 z h1 -> h0 == h1)
let hload56_le' b off =
  let b8 = sub b off 8ul in
  let z  = uint_from_bytes_le b8 in
  let z' = z &. u64 0xffffffffffffff in
  z'

val load_32_bytes:
  out:lbuffer uint64 5ul
  -> b:lbuffer uint8 32ul ->
  Stack unit
    (requires fun h -> live h out /\ live h b)
    (ensures  fun h0 _ h1 -> modifies (loc out) h0 h1)
let load_32_bytes out b =
  let b0 = hload56_le' b 0ul in
  let b1 = hload56_le' b 7ul in
  let b2 = hload56_le' b 14ul in
  let b3 = hload56_le' b 21ul in
  let b4 = uint_from_bytes_le #U32 (sub b 28ul 4ul) in
  let b4 = to_u64 b4 in
  Hacl.Bignum25519.make_u64_5 out b0 b1 b2 b3 b4
