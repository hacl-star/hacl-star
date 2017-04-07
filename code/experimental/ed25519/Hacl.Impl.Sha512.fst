module Hacl.Impl.Sha512

open FStar.Buffer

assume val sha512:
  hash :buffer Hacl.UInt8.t{length hash = 64} ->
  input:buffer Hacl.UInt8.t ->
  len  :UInt32.t{UInt32.v len = length input} ->
  Stack unit
        (requires (fun h0 -> live h0 hash /\ live h0 input))
        (ensures  (fun h0 _ h1 -> live h0 input /\ live h1 hash /\ modifies_1 hash h0 h1 /\
                  as_seq h1 hash == Spec.Sha512.sha512 (as_seq h0 input)))
