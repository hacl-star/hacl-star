module Hacl.Impl.Ed25519.PointCompress

open FStar.Buffer
open Hacl.UInt64
open Hacl.Bignum25519


#reset-options "--max_fuel 0 --z3rlimit 20"

let hint8_p = buffer Hacl.UInt8.t
let op_String_Access h b = Hacl.Spec.Endianness.reveal_sbytes (as_seq h b)


val point_compress:
  out:hint64_p{length out = 32} ->
  p:Hacl.Impl.Ed25519.ExtPoint.point ->
  Stack unit
    (requires (fun h -> live h out /\ live h p))
    (ensures (fun h0 _ h1 -> live h0 out /\ live h0 p /\ 
      live h1 out /\ modifies_1 out h0 h1 /\
      h1.[out] == Spec.point_compress 
      ))
let point_compress out p =
  push_frame();
  let tmp  = create (Hacl.Cast.uint64_to_sint64 0uL) 10ul in
  let zinv = Buffer.sub tmp 0ul 5ul in
  let x    = Buffer.sub tmp 5ul 5ul in
  let px   = Hacl.Impl.Ed25519.ExtPoint.getx p in
  let py   = Hacl.Impl.Ed25519.ExtPoint.gety p in
  let pz   = Hacl.Impl.Ed25519.ExtPoint.getz p in
  Hacl.Bignum25519.inverse zinv pz;
  Hacl.Bignum25519.fmul x   px zinv;
  Hacl.Bignum25519.fmul out py zinv;
  let b = x.(0ul) &^ 1uL in
  let out4 = out.(4ul) in
  out.(4ul) <- out4 +^ (b <<^ 51ul);
  pop_frame()
