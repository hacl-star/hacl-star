module Hacl.Impl.SHA512.ModQ

module ST = FStar.HyperStack.ST

open FStar.HyperStack.All

open FStar.Buffer
open Hacl.UInt64

open Hacl.Spec.Endianness

#reset-options "--max_fuel 0 --z3rlimit 20"

val sha512_modq_pre:
  out:buffer Hacl.UInt64.t{length out = 5} ->
  prefix:buffer Hacl.UInt8.t{length prefix = 32 /\ disjoint prefix out} ->
  input:buffer Hacl.UInt8.t{disjoint out input} ->
  len  :UInt32.t{UInt32.v len = length input /\ length input < pow2 32 - 32} ->
  Stack unit
        (requires (fun h0 -> live h0 input /\ live h0 out /\ live h0 prefix))
        (ensures  (fun h0 _ h1 -> live h0 input /\ live h1 out /\ modifies_1 out h0 h1 /\
          live h0 prefix /\ live h1 prefix /\
          Hacl.Spec.BignumQ.Eval.eval_q (reveal_h64s (as_seq h1 out)) == Spec.Ed25519.sha512_modq FStar.Seq.(reveal_sbytes (as_seq h0 prefix @| as_seq h0 input)) /\
          (let out = as_seq h1 out in let op_String_Access = Seq.index in
           v (out.[0]) < 0x100000000000000 /\ v (out.[1]) < 0x100000000000000 /\
           v (out.[2]) < 0x100000000000000 /\ v (out.[3]) < 0x100000000000000 /\
           v (out.[4]) < 0x100000000000000) ))

val sha512_modq_pre_pre2:
  out:buffer Hacl.UInt64.t{length out = 5} ->
  prefix:buffer Hacl.UInt8.t{length prefix = 32 /\ disjoint prefix out} ->
  prefix2:buffer Hacl.UInt8.t{length prefix2 = 32 /\ disjoint prefix2 out} ->
  input:buffer Hacl.UInt8.t{disjoint out input} ->
  len  :UInt32.t{UInt32.v len = length input /\ length input < pow2 32 - 64} ->
  Stack unit
        (requires (fun h -> live h input /\ live h out /\ live h prefix /\ live h prefix2))
        (ensures  (fun h0 _ h1 -> live h0 input /\ live h1 out /\ modifies_1 out h0 h1 /\
          live h0 prefix /\ live h1 prefix /\ live h0 prefix2 /\ live h1 prefix2 /\
          Hacl.Spec.BignumQ.Eval.eval_q (reveal_h64s (as_seq h1 out)) == Spec.Ed25519.sha512_modq FStar.Seq.(reveal_sbytes (as_seq h0 prefix @| as_seq h0 prefix2 @| as_seq h0 input)) /\
          (let out = as_seq h1 out in let op_String_Access = Seq.index in
           v (out.[0]) < 0x100000000000000 /\ v (out.[1]) < 0x100000000000000 /\
           v (out.[2]) < 0x100000000000000 /\ v (out.[3]) < 0x100000000000000 /\
           v (out.[4]) < 0x100000000000000) ))
