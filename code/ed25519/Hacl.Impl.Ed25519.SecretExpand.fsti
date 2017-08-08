module Hacl.Impl.Ed25519.SecretExpand

module ST = FStar.HyperStack.ST

open FStar.HyperStack.All

open FStar.Buffer
open Hacl.UInt8


#reset-options "--max_fuel 0 --max_ifuel 0 --z3rlimit 20"

let hint8_p = buffer Hacl.UInt8.t

let op_String_Access (h:HyperStack.mem) (b:hint8_p{live h b}) =
  Hacl.Spec.Endianness.reveal_sbytes (as_seq h b)

val secret_expand:
  expanded:hint8_p{length expanded = 64} ->
  secret:hint8_p{length secret = 32} ->
  Stack unit
    (requires (fun h -> live h expanded /\ live h secret))
    (ensures (fun h0 _ h1 -> live h0 expanded /\ live h0 secret /\
      live h1 expanded /\ modifies_1 expanded h0 h1 /\
      (let low = Buffer.sub expanded 0ul 32ul in let high = Buffer.sub expanded 32ul 32ul in
      (h1.[low], h1.[high]) == Spec.Ed25519.secret_expand h0.[secret])))
