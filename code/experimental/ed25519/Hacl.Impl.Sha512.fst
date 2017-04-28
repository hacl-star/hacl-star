module Hacl.Impl.Sha512


open FStar.Buffer


#reset-options "--max_fuel 0 --max_ifuel 0 --z3rlimit 20"

let hint8_p = buffer Hacl.UInt8.t
let op_String_Access h b = Hacl.Spec.Endianness.reveal_sbytes (as_seq h b)


assume val sha512:
  hash :hint8_p{length hash = 64} ->
  input:hint8_p ->
  len  :UInt32.t{UInt32.v len = length input} ->
  Stack unit
        (requires (fun h0 -> live h0 hash /\ live h0 input))
        (ensures  (fun h0 _ h1 -> live h0 hash /\ live h0 input /\
          live h1 hash /\ modifies_1 hash h0 h1 /\
          h1.[hash] == Spec.Sha512.sha512 h0.[input]))
