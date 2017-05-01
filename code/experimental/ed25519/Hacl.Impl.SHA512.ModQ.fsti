module Hacl.Impl.SHA512.ModQ

open FStar.Buffer
open Hacl.UInt64


#reset-options "--max_fuel 0 --z3rlimit 20"

val sha512_modq:
  out:buffer Hacl.UInt64.t{length out = 5} ->
  input:buffer Hacl.UInt8.t ->
  len  :UInt32.t{UInt32.v len = length input} ->
  Stack unit
        (requires (fun h0 -> live h0 input /\ live h0 out))
        (ensures  (fun h0 _ h1 -> live h0 input /\ live h1 out /\ modifies_1 out h0 h1 /\
          Hacl.Spec.BignumQ.Eval.eval_q (as_seq h1 out) == Spec.Ed25519.sha512_modq (as_seq h0 input) /\
          (let out = as_seq h1 out in let op_String_Access = Seq.index in
           v (out.[0]) < 0x100000000000000 /\ v (out.[1]) < 0x100000000000000 /\
           v (out.[2]) < 0x100000000000000 /\ v (out.[3]) < 0x100000000000000 /\
           v (out.[4]) < 0x100000000000000) ))
