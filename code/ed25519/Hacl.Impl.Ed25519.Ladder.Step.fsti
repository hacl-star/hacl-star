module Hacl.Impl.Ed25519.Ladder.Step

module ST = FStar.HyperStack.ST

open FStar.HyperStack.All

open FStar.Buffer

open Hacl.Bignum25519
open Hacl.Impl.Ed25519.ExtPoint
open Hacl.Spec.Endianness


module U32 = FStar.UInt32
module H8 = Hacl.UInt8

#reset-options "--max_fuel 0 --z3rlimit 20"


let point_inv h (p:point) : GTot Type0 =
  live h p /\ (let x = getx p in let y = gety p in let z = getz p in let t = gett p in
  red_513 (as_seq h x) /\ red_513 (as_seq h y) /\ red_513 (as_seq h z) /\ red_513 (as_seq h t))


val loop_step:
  b:buffer Hacl.UInt64.t{length b = 80} ->
  k:buffer Hacl.UInt8.t{length k = 32 /\ disjoint k b} ->
  ctr:UInt32.t{UInt32.v ctr < 256} ->
  Stack unit
    (requires (fun h -> live h b /\ live h k /\
      (let nq = Buffer.sub b 0ul 20ul in
       let nqpq = Buffer.sub b 20ul 20ul in
       let nq2 = Buffer.sub b 40ul 20ul in
       let nqpq2 = Buffer.sub b 60ul 20ul in
       point_inv h nq /\ point_inv h nqpq)))
    (ensures (fun h0 _ h1 -> live h0 b /\ live h0 k /\ live h1 b /\ modifies_1 b h0 h1 /\
      (let nq = Buffer.sub b 0ul 20ul in
       let nqpq = Buffer.sub b 20ul 20ul in
       let nq2 = Buffer.sub b 40ul 20ul in
       let nqpq2 = Buffer.sub b 60ul 20ul in
       let ctr' = UInt32.v ctr in
       let x = as_point h0 nq in
       let xp1 = as_point h0 nqpq in
       let x' = as_point h1 nq in
       let xp1' = as_point h1 nqpq in
       let x'', xp1'' = Spec.Ed25519.(
         let x, xp1 = if ith_bit (reveal_sbytes (as_seq h0 k)) ctr' = 1 then xp1, x else x, xp1 in
         let xx = point_double x in
         let xxp1 = point_add x xp1 in
         if ith_bit (reveal_sbytes (as_seq h0 k)) ctr' = 1 then xxp1, xx else xx, xxp1) in
       point_inv h0 nq /\ point_inv h0 nqpq /\ point_inv h1 nq /\ point_inv h1 nqpq /\
       (x'', xp1'') == (x', xp1')
    )))
