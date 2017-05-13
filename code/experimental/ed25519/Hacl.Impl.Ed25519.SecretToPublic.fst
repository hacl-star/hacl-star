module Hacl.Impl.Ed25519.SecretToPublic


open FStar.HyperStack
open FStar.Buffer


open Hacl.Impl.Ed25519.SecretExpand
open Hacl.Impl.Ed25519.Ladder
open Hacl.Impl.Ed25519.PointCompress
open Hacl.Impl.Ed25519.G


#reset-options "--max_fuel 0 --z3rlimit 20"

let hint8_p = buffer Hacl.UInt8.t
let op_String_Access h b = Hacl.Spec.Endianness.reveal_sbytes (as_seq h b)


val secret_to_public:
  out:hint8_p{length out = 32} ->
  secret:hint8_p{length secret = 32 /\ disjoint out secret} ->
  Stack unit
    (requires (fun h -> live h out /\ live h secret))
    (ensures (fun h0 _ h1 -> live h0 out /\ live h0 secret /\ live h1 out /\ modifies_1 out h0 h1 /\
      as_seq h1 out == Spec.Ed25519.secret_to_public h0.[secret]))
let secret_to_public out secret =
  push_frame();
  let expanded_secret = create 0uy 64ul in
  let res             = create 0uL 20ul in
  let g               = create 0uL 5ul  in
  let a               = sub expanded_secret 0ul 32ul in
  secret_expand expanded_secret secret;
  make_g g;
  point_mul res a g;
  point_compress out res;
  pop_frame()
