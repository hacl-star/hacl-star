module Hacl.Impl.Ed25519.SecretExpand

open FStar.Buffer
open Hacl.UInt8

let hint8_p = buffer t

val secret_expand:
  expanded:hint8_p{length expanded = 64} ->
  secret:hint8_p{length secret = 32} ->
  Stack unit
    (requires (fun h -> live h expanded /\ live h secret))
    (ensures (fun h0 _ h1 -> live h1 expanded /\ live h0 secret /\ modifies_1 expanded h0 h1))
let secret_expand expanded secret =
  Hacl.Impl.Sha512.sha512 expanded secret 32ul;
  let h_low = Buffer.sub expanded 0ul 32ul in
  let h_low0  = h_low.( 0ul) in
  let h_low31 = h_low.(31ul) in
  h_low.( 0ul) <- (h_low0 &^ 0xf8uy);
  h_low.(31ul) <- ((h_low31 &^ 127uy) |^ 64uy)
