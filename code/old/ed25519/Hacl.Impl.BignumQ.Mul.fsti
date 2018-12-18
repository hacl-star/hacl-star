module Hacl.Impl.BignumQ.Mul

module ST = FStar.HyperStack.ST

open FStar.HyperStack.All

open FStar.Mul
open FStar.HyperStack
open FStar.Buffer


open Hacl.Cast
open Hacl.UInt64

open Hacl.Spec.Endianness
open Hacl.Spec.BignumQ.Eval


#reset-options "--max_fuel 0 --z3rlimit 20"

let qelemB = b:buffer Hacl.UInt64.t{length b = 5}


let within_56 (h:mem) (b:qelemB) : GTot Type0 =
  live h b /\ (let b = as_seq h b in
    v b.[0] < 0x100000000000000 /\ v b.[1] < 0x100000000000000 /\ v b.[2] < 0x100000000000000 /\ 
    v b.[3] < 0x100000000000000 /\ v b.[4] < 0x100000000000000)


let all_10_bellow_56 (t:Seq.seq Hacl.UInt64.t{Seq.length t = 10}) : GTot Type0 =
  Seq.length t = 10 /\ (let op_String_Access = Seq.index in
  v t.[0] < 0x100000000000000
  /\ v t.[1] < 0x100000000000000
  /\ v t.[2] < 0x100000000000000
  /\ v t.[3] < 0x100000000000000
  /\ v t.[4] < 0x100000000000000
  /\ v t.[5] < 0x100000000000000
  /\ v t.[6] < 0x100000000000000
  /\ v t.[7] < 0x100000000000000
  /\ v t.[8] < 0x100000000000000
  /\ v t.[9] < 0x100000000000000)

inline_for_extraction
val barrett_reduction:
  z:qelemB ->
  t:buffer Hacl.UInt64.t{length t = 10} ->
  Stack unit
    (requires (fun h -> live h z /\ live h t /\ (let t = as_seq h t in
      all_10_bellow_56 t /\
      eval_q_10 (h64_to_u64 t.[0]) (h64_to_u64 t.[1]) (h64_to_u64 t.[2]) (h64_to_u64 t.[3]) (h64_to_u64 t.[4]) (h64_to_u64 t.[5]) (h64_to_u64 t.[6]) (h64_to_u64 t.[7]) (h64_to_u64 t.[8]) (h64_to_u64 t.[9]) < pow2 512)))
    (ensures (fun h0 _ h1 -> live h1 z /\ live h0 t /\ within_56 h1 z /\ (
      let z = reveal_h64s (as_seq h1 z) in
      let t = as_seq h0 t in let op_String_Access = Seq.index in
      all_10_bellow_56 t /\
      eval_q_10 (h64_to_u64 t.[0]) (h64_to_u64 t.[1]) (h64_to_u64 t.[2]) (h64_to_u64 t.[3]) (h64_to_u64 t.[4]) (h64_to_u64 t.[5]) (h64_to_u64 t.[6]) (h64_to_u64 t.[7]) (h64_to_u64 t.[8]) (h64_to_u64 t.[9])  < pow2 512 /\
      eval_q z = eval_q_10 (h64_to_u64 t.[0]) (h64_to_u64 t.[1]) (h64_to_u64 t.[2]) (h64_to_u64 t.[3]) (h64_to_u64 t.[4]) (h64_to_u64 t.[5]) (h64_to_u64 t.[6]) (h64_to_u64 t.[7]) (h64_to_u64 t.[8]) (h64_to_u64 t.[9]) % 0x1000000000000000000000000000000014def9dea2f79cd65812631a5cf5d3ed) /\
      within_56 h1 z /\ modifies_1 z h0 h1
    ))


val mul_modq:
  z:qelemB ->
  x:qelemB ->
  y:qelemB ->
  Stack unit
    (requires (fun h -> live h z /\ live h x /\ live h y /\ within_56 h x /\ within_56 h y /\
      (let x = reveal_h64s (as_seq h x) in let y = reveal_h64s (as_seq h y) in
      eval_q x < pow2 256 /\ eval_q y < pow2 256)))
    (ensures (fun h0 _ h1 -> live h1 z /\ live h0 x /\ live h0 y /\ modifies_1 z h0 h1 /\
      (let x = reveal_h64s (as_seq h0 x) in let y = reveal_h64s (as_seq h0 y) in
       eval_q x < pow2 256 /\ eval_q y < pow2 256) /\
       within_56 h1 z /\
       eval_q (reveal_h64s (as_seq h1 z)) == (eval_q (reveal_h64s (as_seq h0 x)) * eval_q (reveal_h64s (as_seq h0 y))) % 0x1000000000000000000000000000000014def9dea2f79cd65812631a5cf5d3ed))


val add_modq:
  z:qelemB ->
  x:qelemB ->
  y:qelemB ->
  Stack unit
    (requires (fun h -> live h z /\ live h x /\ live h y /\ within_56 h x /\ within_56 h y /\
      (let x = reveal_h64s (as_seq h x) in let y = reveal_h64s (as_seq h y) in
      eval_q x < 0x1000000000000000000000000000000014def9dea2f79cd65812631a5cf5d3ed /\
      eval_q y < 0x1000000000000000000000000000000014def9dea2f79cd65812631a5cf5d3ed)))
    (ensures (fun h0 _ h1 -> live h1 z /\ live h0 x /\ live h0 y /\ modifies_1 z h0 h1 /\
      (let x = reveal_h64s (as_seq h0 x) in let y = reveal_h64s (as_seq h0 y) in
       eval_q x < 0x1000000000000000000000000000000014def9dea2f79cd65812631a5cf5d3ed /\
       eval_q y < 0x1000000000000000000000000000000014def9dea2f79cd65812631a5cf5d3ed) /\
       within_56 h1 z /\
       eval_q (reveal_h64s (as_seq h1 z)) == (eval_q (reveal_h64s (as_seq h0 x)) + eval_q (reveal_h64s (as_seq h0 y))) % 0x1000000000000000000000000000000014def9dea2f79cd65812631a5cf5d3ed))
