module Hacl.Impl.Ed25519.PointDecompress

open FStar.Buffer
open Hacl.UInt64
open Hacl.Bignum25519
open Hacl.Impl.Ed25519.ExtPoint


#reset-options "--max_fuel 0 --z3rlimit 20"

private
val split_2_255:
  y:felem ->
  Stack sign
    (requires (fun h -> live h y /\ red_51 (as_seq h y)))
    (ensures (fun h0 z h1 -> live h1 y /\ live h0 y /\ modifies_1 y h0 h1 /\
      

val point_decompress:
  out:Hacl.Impl.Ed25519.ExtPoint.point ->
  s:buffer Hacl.UInt8.t{length s = 32} ->
  Stack bool
    (requires (fun h -> live h out /\ live h s))
    (ensures (fun h0 b h1 -> live h0 s /\ live h1 out /\ modifies_1 out h0 h1 /\
      (let x, y, z, t = as_point h1 out in
       (seval x, seval y, seval z, seval t) == Spec.Ed25519.point_decompress (as_seq h0 s) /\
       red_513 x /\ red_513 y /\ red_513 z /\ red_513 t)
    ))
let point_decompress out s =
  push_frame();
  let tmp  = Buffer.create 0uL 10ul in
  let y    = Buffer.sub tmp 0ul 5ul in
  let x    = Buffer.sub tmp 5ul 5ul in
  Hacl.Impl.Load51.load_51 y s;
  let y0 = y.(0ul) in
  let y1 = y.(1ul) in
  let y2 = y.(2ul) in
  let y3 = y.(3ul) in
  let y4 = y.(4ul) in
  let s31 = s.(31ul) in
  let sign = FStar.UInt8.((s31 >>^ 7ul) &^ 1uy) in
  let sign = Int.Cast.uint8_to_uint64 sign in
  (* let y4' = y4 &^ 0x7ffffffffffffuL in *)
  Hacl.Lib.Create64.make_h64_5 y y0 y1 y2 y3 y4;
  let z = Hacl.Impl.Ed25519.RecoverX.recover_x x y sign in
  let res =
  if z = false then false
  else (
    let outx = getx out in
    let outy = gety out in
    let outz = getz out in
    let outt = gett out in
    blit x 0ul outx 0ul 5ul;
    blit y 0ul outy 0ul 5ul;
    Hacl.Lib.Create64.make_h64_5 outz 1uL 0uL 0uL 0uL 0uL;
    fmul outt x y;
    true
  ) in
  pop_frame();
  res
