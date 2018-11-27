module Hacl.Impl.Ed25519.SecretToPublic

module ST = FStar.HyperStack.ST

open FStar.HyperStack.All

open FStar.HyperStack
open FStar.Buffer

#reset-options "--max_fuel 0 --z3rlimit 20"

let hint8_p = buffer Hacl.UInt8.t

inline_for_extraction
let op_String_Access (h:HyperStack.mem) (b:hint8_p{live h b}) =
  Hacl.Spec.Endianness.reveal_sbytes (as_seq h b)

inline_for_extraction
val secret_to_public:
  out:hint8_p{length out = 32} ->
  secret:hint8_p{length secret = 32 /\ disjoint out secret} ->
  Stack unit
    (requires (fun h -> live h out /\ live h secret))
    (ensures (fun h0 _ h1 -> live h0 out /\ live h0 secret /\ live h1 out /\ modifies_1 out h0 h1 /\
      h1.[out] == Spec.Ed25519.secret_to_public h0.[secret]))
