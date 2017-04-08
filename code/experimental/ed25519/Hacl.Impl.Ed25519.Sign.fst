module Hacl.Impl.Ed25519.Sign

open FStar.Buffer

let hint8_p = buffer Hacl.UInt8.t

val sign:
  signature:hint8_p{length signature = 64} ->
  secret:hint8_p{length secret = 32} ->
  msg:hint8_p ->
  len:UInt32.t{UInt32.v len = length msg} ->
  Stack unit
    (requires (fun h -> live h signature /\ live h msg /\ live h secret))
    (ensures (fun h0_ h1 -> live h0 secret /\ live h0 secret /\ live h1 signature /\ modifies_1 signature h0 h1))
let sign signature secret msg len =
  
