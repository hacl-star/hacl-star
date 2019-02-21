module Hacl.Impl.Ed25519.SecretToPublic

module ST = FStar.HyperStack.ST

open FStar.HyperStack.All


open FStar.HyperStack
open FStar.Buffer

open Hacl.Spec.Endianness

open Hacl.Impl.Ed25519.ExtPoint
open Hacl.Impl.Ed25519.SecretExpand
open Hacl.Impl.Ed25519.Ladder
open Hacl.Impl.Ed25519.PointCompress
open Hacl.Impl.Ed25519.G


#reset-options "--max_fuel 0 --z3rlimit 20"

inline_for_extraction
private
val point_mul_g:
  result:point ->
  scalar:buffer Hacl.UInt8.t{length scalar = 32 /\ disjoint result scalar} ->
  Stack unit
  (requires (fun h -> Buffer.live h scalar /\ live h result))
  (ensures (fun h0 _ h1 -> Buffer.live h0 scalar /\ live h0 result /\
    live h1 result /\ modifies_1 result h0 h1 /\ point_inv h1 result /\
    (let r = as_point h1 result in
     let n  = reveal_sbytes (as_seq h0 scalar) in
     r == Spec.Ed25519.point_mul n Spec.Ed25519.g) ))

#reset-options "--max_fuel 0 --z3rlimit 20"

let point_mul_g result scalar =
  push_frame();
  let h0 = ST.get() in
  let g = create (Hacl.Cast.uint64_to_sint64 0uL) 20ul in
  Hacl.Impl.Ed25519.G.make_g g;
  let h1 = ST.get() in
  no_upd_lemma_0 h0 h1 scalar;
  Hacl.Impl.Ed25519.Ladder.point_mul result scalar g;
  let h2 = ST.get() in
  no_upd_lemma_1 h1 h2 result scalar;
  pop_frame()


inline_for_extraction
val secret_to_public_:
  out:hint8_p{length out = 32} ->
  secret:hint8_p{length secret = 32 /\ disjoint out secret} ->
  expanded:hint8_p{length expanded = 64 /\ disjoint expanded out /\ disjoint expanded secret} ->
  Stack unit
    (requires (fun h -> live h out /\ live h secret /\ live h expanded /\ (
      let low = Buffer.sub expanded 0ul 32ul in let high = Buffer.sub expanded 32ul 32ul in
      (h.[low], h.[high]) == Spec.Ed25519.secret_expand h.[secret])))
    (ensures (fun h0 _ h1 -> live h0 out /\ live h0 secret /\ live h1 out /\ modifies_1 out h0 h1 /\
      h1.[out] == Spec.Ed25519.secret_to_public h0.[secret]))

#reset-options "--max_fuel 0 --z3rlimit 100"

let secret_to_public_ out secret expanded_secret =
  let a               = sub expanded_secret 0ul 32ul in
  push_frame();
  let res             = create (Hacl.Cast.uint64_to_sint64 0uL) 20ul in
  point_mul_g res a;
  point_compress out res;
  pop_frame()


inline_for_extraction
let secret_to_public out secret =
  push_frame();
  let expanded = create (Hacl.Cast.uint8_to_sint8 0uy) 64ul in
  secret_expand expanded secret;
  secret_to_public_ out secret expanded;
  pop_frame()
