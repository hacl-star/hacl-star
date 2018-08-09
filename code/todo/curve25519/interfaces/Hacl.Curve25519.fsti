module Hacl.Curve25519

module ST = FStar.HyperStack.ST

open FStar.HyperStack.All

open FStar.Buffer

#reset-options "--max_fuel 0 --z3rlimit 20"

type uint8_p = Buffer.buffer Hacl.UInt8.t

private let op_String_Access h (b:uint8_p{live h b}) = Hacl.Spec.Endianness.reveal_sbytes (as_seq h b)

val crypto_scalarmult:
  mypublic:uint8_p{length mypublic = 32} ->
  secret:uint8_p{length secret = 32} ->
  point:uint8_p{length point = 32} ->
  Stack unit
    (requires (fun h -> live h mypublic /\ live h secret /\ live h point))
    (ensures (fun h0 _ h1 -> live h1 mypublic /\ modifies_1 mypublic h0 h1 /\
     live h0 mypublic /\ live h0 secret /\ live h0 point /\
     h1.[mypublic] == Spec.Curve25519.(scalarmult h0.[secret] h0.[point])))
