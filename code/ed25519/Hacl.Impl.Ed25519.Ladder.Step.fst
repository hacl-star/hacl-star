module Hacl.Impl.Ed25519.Ladder.Step

module ST = FStar.HyperStack.ST

open FStar.HyperStack.All


open FStar.Mul
open FStar.HyperStack
open FStar.Ghost
open FStar.Buffer

open Hacl.Bignum25519
open Hacl.Impl.Ed25519.ExtPoint

module U32 = FStar.UInt32
module H8 = Hacl.UInt8


#reset-options "--max_fuel 0 --z3rlimit 100"

type uint8_p = buffer H8.t

inline_for_extraction
private
val ith_bit:
  k:buffer Hacl.UInt8.t{length k = 32} ->
  i:UInt32.t{UInt32.v i < 256} ->
  Stack Hacl.UInt8.t
    (requires (fun h -> live h k))
    (ensures (fun h0 z h1 -> h0 == h1 /\ live h0 k /\
      Hacl.UInt8.v z == Spec.Ed25519.ith_bit (reveal_sbytes (as_seq h0 k)) (UInt32.v i)
      /\ (Hacl.UInt8.v z == 0 \/ Hacl.UInt8.v z == 1)))

let ith_bit k i =
  assert_norm(pow2 1 = 2);
  assert_norm(pow2 3 = 8);
  assert_norm(pow2 5 = 32);
  assert_norm(pow2 8 = 256);
  let open FStar.UInt32 in
  let q = i >>^ 3ul in
  assert(v q = v i / 8);
  let r = i &^ 7ul in
  UInt.logand_mask (v i) 3;
  assert(v r = v i % 8);
  Math.Lemmas.lemma_div_lt (v i) 8 3;
  let kq = k.(q) in
  let kq' = Hacl.UInt8.(kq >>^ r) in
  let z = Hacl.UInt8.(kq' &^ Hacl.Cast.uint8_to_sint8 1uy) in
  UInt.logand_mask (Hacl.UInt8.v kq') 1;
  assert(Hacl.UInt8.v z = (Hacl.UInt8.v kq / pow2 (v r)) % 2);
  z



#reset-options "--max_fuel 0 --z3rlimit 100"

inline_for_extraction
private
val swap_cond_inplace:
  p:point -> q:point{disjoint p q} -> i:limb{Hacl.UInt64.v i = 0 \/ Hacl.UInt64.v i = 1} ->
  Stack unit
    (requires (fun h -> live h p /\ live h q /\
      ( let x1 = as_seq h (getx p) in
        let y1 = as_seq h (gety p) in
        let z1 = as_seq h (getz p) in
        let t1 = as_seq h (gett p) in
        red_513 x1 /\ red_513 y1 /\ red_513 z1 /\ red_513 t1) /\
      ( let x2 = as_seq h (getx q) in
        let y2 = as_seq h (gety q) in
        let z2 = as_seq h (getz q) in
        let t2 = as_seq h (gett q) in
        red_513 x2 /\ red_513 y2 /\ red_513 z2 /\ red_513 t2) ))
    (ensures (fun h0 _ h1 -> live h1 p /\ live h1 q /\ modifies_2 p q h0 h1 /\ live h0 p /\ live h0 q /\
      ( let x1 = as_seq h0 (getx p) in
        let y1 = as_seq h0 (gety p) in
        let z1 = as_seq h0 (getz p) in
        let t1 = as_seq h0 (gett p) in
        let x2 = as_seq h0 (getx q) in
        let y2 = as_seq h0 (gety q) in
        let z2 = as_seq h0 (getz q) in
        let t2 = as_seq h0 (gett q) in
        let x1' = as_seq h1 (getx p) in
        let y1' = as_seq h1 (gety p) in
        let z1' = as_seq h1 (getz p) in
        let t1' = as_seq h1 (gett p) in
        let x2' = as_seq h1 (getx q) in
        let y2' = as_seq h1 (gety q) in
        let z2' = as_seq h1 (getz q) in
        let t2' = as_seq h1 (gett q) in
        red_513 x1 /\ red_513 y1 /\ red_513 z1 /\ red_513 t1 /\
        red_513 x2 /\ red_513 y2 /\ red_513 z2 /\ red_513 t2 /\
        red_513 x1' /\ red_513 y1' /\ red_513 z1' /\ red_513 t1' /\
        red_513 x2' /\ red_513 y2' /\ red_513 z2' /\ red_513 t2' /\
      (if Hacl.UInt64.v i = 1 then (x1' == x2 /\ y1' == y2 /\ z1' == z2 /\ t1' == t2 /\
                                    x2' == x1 /\ y2' == y1 /\ z2' == z1 /\ t2' == t1)
         else (x1' == x1 /\ y1' == y1 /\ z1' == z1 /\ t1' == t1 /\
               x2' == x2 /\ y2' == y2 /\ z2' == z2 /\ t2' == t2)))
    ))

#reset-options "--max_fuel 0 --z3rlimit 100"

let swap_cond_inplace p q iswap =
  Hacl.Impl.Ed25519.SwapConditional.swap_conditional_inplace p q iswap


#reset-options "--max_fuel 0 --z3rlimit 100"

inline_for_extraction
private
val swap_cond:
  p':point -> q':point{disjoint p' q'} ->
  p:point{disjoint p p' /\ disjoint p q'} ->
  q:point{disjoint p' q /\ disjoint q' q /\ disjoint p q} ->
  i:limb{Hacl.UInt64.v i = 0 \/ Hacl.UInt64.v i = 1} ->
  Stack unit
    (requires (fun h -> live h p /\ live h q /\ live h p' /\ live h q' /\
      ( let x1 = as_seq h (getx p) in
        let y1 = as_seq h (gety p) in
        let z1 = as_seq h (getz p) in
        let t1 = as_seq h (gett p) in
        red_513 x1 /\ red_513 y1 /\ red_513 z1 /\ red_513 t1) /\
      ( let x2 = as_seq h (getx q) in
        let y2 = as_seq h (gety q) in
        let z2 = as_seq h (getz q) in
        let t2 = as_seq h (gett q) in
        red_513 x2 /\ red_513 y2 /\ red_513 z2 /\ red_513 t2) ))
    (ensures (fun h0 _ h1 -> live h1 p' /\ live h1 q' /\ modifies_2 p' q' h0 h1 /\ live h0 p /\ live h0 q /\
      ( let x1 = as_seq h0 (getx p) in
        let y1 = as_seq h0 (gety p) in
        let z1 = as_seq h0 (getz p) in
        let t1 = as_seq h0 (gett p) in
        let x2 = as_seq h0 (getx q) in
        let y2 = as_seq h0 (gety q) in
        let z2 = as_seq h0 (getz q) in
        let t2 = as_seq h0 (gett q) in
        let x1' = as_seq h1 (getx p') in
        let y1' = as_seq h1 (gety p') in
        let z1' = as_seq h1 (getz p') in
        let t1' = as_seq h1 (gett p') in
        let x2' = as_seq h1 (getx q') in
        let y2' = as_seq h1 (gety q') in
        let z2' = as_seq h1 (getz q') in
        let t2' = as_seq h1 (gett q') in
        red_513 x1 /\ red_513 y1 /\ red_513 z1 /\ red_513 t1 /\
        red_513 x2 /\ red_513 y2 /\ red_513 z2 /\ red_513 t2 /\
        red_513 x1' /\ red_513 y1' /\ red_513 z1' /\ red_513 t1' /\
        red_513 x2' /\ red_513 y2' /\ red_513 z2' /\ red_513 t2' /\
      (if Hacl.UInt64.v i = 1 then (x1' == x2 /\ y1' == y2 /\ z1' == z2 /\ t1' == t2 /\
                                    x2' == x1 /\ y2' == y1 /\ z2' == z1 /\ t2' == t1)
         else (x1' == x1 /\ y1' == y1 /\ z1' == z1 /\ t1' == t1 /\
               x2' == x2 /\ y2' == y2 /\ z2' == z2 /\ t2' == t2)))
    ))

#reset-options "--max_fuel 0 --z3rlimit 100"

let swap_cond p' q' p q iswap =
  Hacl.Impl.Ed25519.SwapConditional.swap_conditional p' q' p q iswap

#reset-options "--max_fuel 0 --z3rlimit 100"

inline_for_extraction
private
val loop_step_1:
  b:buffer Hacl.UInt64.t{length b = 80} ->
  k:uint8_p{length k = 32 /\ disjoint k b} ->
  ctr:UInt32.t{UInt32.v ctr < 256} ->
  i:Hacl.UInt8.t{Hacl.UInt8.v i = 0 \/ Hacl.UInt8.v i = 1} ->
  Stack unit
    (requires (fun h -> live h b /\ live h k /\
      (let nq    = Buffer.sub b 0ul 20ul in
       let nqpq  = Buffer.sub b 20ul 20ul in
       let nq2   = Buffer.sub b 40ul 20ul in
       let nqpq2 = Buffer.sub b 60ul 20ul in
       point_inv h nq /\ point_inv h nqpq)))
    (ensures (fun h0 _ h1 -> live h0 b /\ live h0 k /\ live h1 b /\ modifies_1 b h0 h1 /\
      (let nq    = Buffer.sub b 0ul 20ul in
       let nqpq  = Buffer.sub b 20ul 20ul in
       let ctr'  = UInt32.v ctr in
       let x     = as_point h0 nq in
       let xp1   = as_point h0 nqpq in
       let x'    = as_point h1 nq in
       let xp1'  = as_point h1 nqpq in
       let x'', xp1'' = (if Hacl.UInt8.v i = 1 then xp1, x else x, xp1) in
       point_inv h0 nq /\ point_inv h0 nqpq /\ point_inv h1 nq /\ point_inv h1 nqpq /\
       (x'', xp1'') == (x', xp1')
    )))

#reset-options "--max_fuel 0 --z3rlimit 200"

let loop_step_1 b k ctr i =
  let nq    = Buffer.sub b 0ul 20ul in
  let nqpq  = Buffer.sub b 20ul 20ul in
  let nq2   = Buffer.sub b 40ul 20ul in
  let nqpq2 = Buffer.sub b 60ul 20ul in
  let bit   = Hacl.Cast.sint8_to_sint64 i in
  let h0    = ST.get() in
  swap_cond_inplace nq nqpq bit


inline_for_extraction
private
val loop_step_2:
  b:buffer Hacl.UInt64.t{length b = 80} ->
  k:uint8_p{length k = 32 /\ disjoint k b} ->
  ctr:UInt32.t{UInt32.v ctr < 256} ->
  Stack unit
    (requires (fun h -> live h b /\ live h k /\
      (let nq    = Buffer.sub b 0ul 20ul in
       let nqpq  = Buffer.sub b 20ul 20ul in
       let nq2   = Buffer.sub b 40ul 20ul in
       let nqpq2 = Buffer.sub b 60ul 20ul in
       point_inv h nq /\ point_inv h nqpq)))
    (ensures (fun h0 _ h1 -> live h0 b /\ live h0 k /\ live h1 b /\ modifies_1 b h0 h1 /\
      (let nq    = Buffer.sub b 0ul 20ul in
       let nqpq  = Buffer.sub b 20ul 20ul in
       let nq2   = Buffer.sub b 40ul 20ul in
       let nqpq2 = Buffer.sub b 60ul 20ul in
       let ctr'  = UInt32.v ctr in
       let x     = as_point h0 nq in
       let xp1   = as_point h0 nqpq in
       let x'    = as_point h1 nq2 in
       let xp1'  = as_point h1 nqpq2 in
       x' == Spec.Ed25519.point_double x /\ xp1' == Spec.Ed25519.point_add x xp1 /\
       point_inv h0 nq /\ point_inv h0 nqpq /\ point_inv h1 nq2 /\ point_inv h1 nqpq2
    )))

#reset-options "--max_fuel 0 --z3rlimit 200"

let loop_step_2 b k ctr =
  let nq    = Buffer.sub b 0ul 20ul in
  let nqpq  = Buffer.sub b 20ul 20ul in
  let nq2   = Buffer.sub b 40ul 20ul in
  let nqpq2 = Buffer.sub b 60ul 20ul in
  let h0    = ST.get() in
  let h1    = ST.get() in
  Hacl.Impl.Ed25519.PointDouble.point_double nq2 nq;
  let h     = ST.get() in
(*
  let x = getx nq in
  let y = gety nq in
  let z = getz nq in
  let t = gett nq in
  let x' = getx nqpq in
  let y' = gety nqpq in
  let z' = getz nqpq in
  let t' = gett nqpq in
  no_upd_lemma_1 h1 h nq2 x;
  no_upd_lemma_1 h1 h nq2 y;
  no_upd_lemma_1 h1 h nq2 z;
  no_upd_lemma_1 h1 h nq2 t;
  no_upd_lemma_1 h1 h nq2 x';
  no_upd_lemma_1 h1 h nq2 y';
  no_upd_lemma_1 h1 h nq2 z';
  no_upd_lemma_1 h1 h nq2 t';
*)
  Hacl.Impl.Ed25519.PointAdd.point_add nqpq2 nq nqpq;
  ()
(*  let h2    = ST.get() in
  let x'' = getx nq2 in
  let y'' = gety nq2 in
  let z'' = getz nq2 in
  let t'' = gett nq2 in
  no_upd_lemma_1 h h2 nqpq2 x;
  no_upd_lemma_1 h h2 nqpq2 y;
  no_upd_lemma_1 h h2 nqpq2 z;
  no_upd_lemma_1 h h2 nqpq2 t;
  no_upd_lemma_1 h h2 nqpq2 x';
  no_upd_lemma_1 h h2 nqpq2 y';
  no_upd_lemma_1 h h2 nqpq2 z';
  no_upd_lemma_1 h h2 nqpq2 t';
  no_upd_lemma_1 h h2 nqpq2 x'';
  no_upd_lemma_1 h h2 nqpq2 y'';
  no_upd_lemma_1 h h2 nqpq2 z'';
  no_upd_lemma_1 h h2 nqpq2 t''*)


inline_for_extraction
private
val loop_step_3:
  b:buffer Hacl.UInt64.t{length b = 80} ->
  k:uint8_p{length k = 32 /\ disjoint k b} ->
  ctr:UInt32.t{UInt32.v ctr < 256} ->
  i:Hacl.UInt8.t{Hacl.UInt8.v i = 0 \/ Hacl.UInt8.v i = 1} ->
  Stack unit
    (requires (fun h -> live h b /\ live h k /\
      (let nq    = Buffer.sub b 0ul 20ul in
       let nqpq  = Buffer.sub b 20ul 20ul in
       let nq2   = Buffer.sub b 40ul 20ul in
       let nqpq2 = Buffer.sub b 60ul 20ul in
       point_inv h nq2 /\ point_inv h nqpq2)))
    (ensures (fun h0 _ h1 -> live h0 b /\ live h0 k /\ live h1 b /\ modifies_1 b h0 h1 /\
      (let nq    = Buffer.sub b 0ul 20ul in
       let nqpq  = Buffer.sub b 20ul 20ul in
       let nq2   = Buffer.sub b 40ul 20ul in
       let nqpq2 = Buffer.sub b 60ul 20ul in
       let ctr'  = UInt32.v ctr in
       let x     = as_point h0 nq2 in
       let xp1   = as_point h0 nqpq2 in
       let x'    = as_point h1 nq in
       let xp1'  = as_point h1 nqpq in
       let x'', xp1'' = (if Hacl.UInt8.v i = 1 then xp1, x else x, xp1) in
       point_inv h1 nq /\ point_inv h1 nqpq /\
       (x'', xp1'') == (x', xp1')
    )))

#reset-options "--max_fuel 0 --z3rlimit 200"

let loop_step_3 b k ctr i =
  let nq    = Buffer.sub b 0ul 20ul in
  let nqpq  = Buffer.sub b 20ul 20ul in
  let nq2   = Buffer.sub b 40ul 20ul in
  let nqpq2 = Buffer.sub b 60ul 20ul in
  let bit   = Hacl.Cast.sint8_to_sint64 i in
  swap_cond nq nqpq nq2 nqpq2 bit


#reset-options "--max_fuel 0 --z3rlimit 1000"

let loop_step b k ctr =
  let nq    = Buffer.sub b 0ul 20ul in
  let nqpq  = Buffer.sub b 20ul 20ul in
  let nq2   = Buffer.sub b 40ul 20ul in
  let nqpq2 = Buffer.sub b 60ul 20ul in
  let bit   = ith_bit k ctr in
  loop_step_1 b k ctr bit;
  loop_step_2 b k ctr;
  loop_step_3 b k ctr bit
