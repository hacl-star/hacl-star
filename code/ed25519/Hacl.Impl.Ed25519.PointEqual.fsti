module Hacl.Impl.Ed25519.PointEqual

module ST = FStar.HyperStack.ST

open FStar.HyperStack.All

open FStar.Mul
open FStar.Buffer
open FStar.UInt32

open Hacl.Bignum25519
open Hacl.Impl.Ed25519.ExtPoint


#reset-options "--max_fuel 0 --z3rlimit 20"

let point_inv h (p:point) : GTot Type0 =
  live h p /\ (let x = getx p in let y = gety p in let z = getz p in let t = gett p in
  red_513 (as_seq h x) /\ red_513 (as_seq h y) /\ red_513 (as_seq h z) /\ red_513 (as_seq h t))


val gte_q:
  s:buffer UInt64.t{length s = 5} ->
  Stack bool
    (requires (fun h -> live h s /\ (let s = as_seq h s in let op_String_Access = Seq.index in
      UInt64.v s.[0] < 0x100000000000000 /\ UInt64.v s.[1] < 0x100000000000000 /\
      UInt64.v s.[2] < 0x100000000000000 /\ UInt64.v s.[3] < 0x100000000000000 /\
      UInt64.v s.[4] < 0x100000000000000 )))
    (ensures (fun h0 b h1 -> live h0 s /\ h0 == h1 /\
      (Hacl.Spec.BignumQ.Eval.eval_q (as_seq h0 s) >= 0x1000000000000000000000000000000014def9dea2f79cd65812631a5cf5d3ed <==> b)))


val point_equal:
  p:Hacl.Impl.Ed25519.ExtPoint.point ->
  q:Hacl.Impl.Ed25519.ExtPoint.point ->
  Stack bool
    (requires (fun h -> live h p /\ live h q /\ point_inv h p /\ point_inv h q))
    (ensures (fun h0 z h1 -> live h0 p /\ live h0 q /\ modifies_0 h0 h1 /\
      z == Spec.Ed25519.point_equal (as_point h0 p) (as_point h0 q) ))
