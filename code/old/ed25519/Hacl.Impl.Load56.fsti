module Hacl.Impl.Load56

module ST = FStar.HyperStack.ST

open FStar.HyperStack.All

open FStar.Mul
open FStar.Buffer
open FStar.Old.Endianness
open Hacl.Endianness
open Hacl.UInt64

open Hacl.Spec.Endianness

#reset-options "--max_fuel 0 --z3rlimit 20"

let u32 = UInt32.t
let h8 = Hacl.UInt8.t
let h64 = Hacl.UInt64.t
let hint8_p = buffer h8


val load_64_bytes:
  out:buffer h64{length out = 10} ->
  b:hint8_p{length b = 64} ->
  Stack unit
    (requires (fun h -> live h out /\ live h b))
    (ensures (fun h0 _ h1 -> live h1 out /\ modifies_1 out h0 h1 /\ live h0 b
      /\ (let out = reveal_h64s (as_seq h1 out) in
         let op_String_Access = Seq.index in
         let open FStar.UInt64 in
         v out.[0] < 0x100000000000000
         /\ v out.[1] < 0x100000000000000
         /\ v out.[2] < 0x100000000000000
         /\ v out.[3] < 0x100000000000000
         /\ v out.[4] < 0x100000000000000
         /\ v out.[5] < 0x100000000000000
         /\ v out.[6] < 0x100000000000000
         /\ v out.[7] < 0x100000000000000
         /\ v out.[8] < 0x100000000000000
         /\ v out.[9] < 0x100000000000000
         /\ little_endian (reveal_sbytes (as_seq h0 b))
          == Hacl.Spec.BignumQ.Eval.eval_q_10 out.[0] out.[1] out.[2] out.[3] out.[4] out.[5] out.[6] out.[7] out.[8] out.[9]
        /\ little_endian (reveal_sbytes (as_seq h0 b)) < pow2 512)
    ))


val load_32_bytes:
  out:buffer h64{length out = 5} ->
  b:hint8_p{length b = 32} ->
  Stack unit
    (requires (fun h -> live h out /\ live h b))
    (ensures (fun h0 _ h1 -> live h1 out /\ modifies_1 out h0 h1 /\ live h0 b
      /\ (let out = reveal_h64s (as_seq h1 out) in
         let op_String_Access = Seq.index in
         let open FStar.UInt64 in
         v out.[0] < 0x100000000000000
         /\ v out.[1] < 0x100000000000000
         /\ v out.[2] < 0x100000000000000
         /\ v out.[3] < 0x100000000000000
         /\ v out.[4] < 0x100000000000000 /\
         little_endian (reveal_sbytes (as_seq h0 b))
          == Hacl.Spec.BignumQ.Eval.eval_q out)))
