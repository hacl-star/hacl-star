module Hacl.Impl.Ed25519.PointDecompress

module ST = FStar.HyperStack.ST
open FStar.HyperStack.All
open FStar.Mul

open Lib.IntTypes
open Lib.Buffer

open Hacl.Bignum25519

inline_for_extraction noextract
val most_significant_bit:
  s:lbuffer uint8 32ul ->
  Stack uint64
    (requires fun h -> live h s)
    (ensures fun h0 z h1 -> h1 == h0)
let most_significant_bit s =
  let s31 = s.(31ul) in
  let z   = s31 >>. 7ul in
  to_u64 z

inline_for_extraction noextract
val point_decompress_:
    out:point
  -> s:lbuffer uint8 32ul
  -> tmp:lbuffer uint64 10ul ->
  Stack bool
    (requires fun h ->
      live h out /\ live h s /\ live h tmp /\
      disjoint s tmp /\ disjoint out tmp)
    (ensures  fun h0 b h1 -> modifies (loc out |+| loc tmp) h0 h1)
let point_decompress_ out s tmp =
  let y    = sub tmp 0ul 5ul in
  let x    = sub tmp 5ul 5ul in
  let sign = most_significant_bit s in
  load_51 y s;
  let z = Hacl.Impl.Ed25519.RecoverX.recover_x x y sign in

  let res =
  if z = false then false
  else (
    let outx = getx out in
    let outy = gety out in
    let outz = getz out in
    let outt = gett out in
    copy outx x;
    copy outy y;
    make_one outz;
    fmul outt x y;
    true
  ) in
  res

val point_decompress:
    out:point
  -> s:lbuffer uint8 32ul ->
  Stack bool
    (requires fun h -> live h out /\ live h s)
    (ensures  fun h0 b h1 -> modifies (loc out) h0 h1)
let point_decompress out s =
  push_frame();
  let tmp  = create 10ul (u64 0) in
  let res = point_decompress_ out s tmp in
  pop_frame();
  res
