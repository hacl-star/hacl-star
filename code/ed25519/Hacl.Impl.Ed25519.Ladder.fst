module Hacl.Impl.Ed25519.Ladder

module HS = FStar.HyperStack
module ST = FStar.HyperStack.ST

open FStar.HyperStack.All


open FStar.Mul
open FStar.HyperStack
open FStar.Buffer

open Hacl.Impl.Ed25519.ExtPoint
open Hacl.Impl.Ed25519.Ladder.Step
open Hacl.Spec.Endianness

#reset-options "--max_fuel 1 --z3rlimit 10"

private
val lemma_montgomery_ladder_def_0:
  x:Spec.Ed25519.ext_point ->
  xp1:Spec.Ed25519.ext_point ->
  k:Spec.Lib.bytes ->
  Lemma (Spec.Ed25519.montgomery_ladder_ x xp1 k 0 == (x, xp1))
let lemma_montgomery_ladder_def_0 x xp1 k = ()


private
val lemma_montgomery_ladder_def_1:
  x:Spec.Ed25519.ext_point ->
  xp1:Spec.Ed25519.ext_point ->
  k:Spec.Lib.bytes{Seq.length k = 32} ->
  ctr:nat{ctr > 0 /\ ctr <= 256} ->
  Lemma (Spec.Ed25519.montgomery_ladder_ x xp1 k ctr == Spec.Ed25519.(
    let x, xp1 = Spec.Ed25519.montgomery_ladder_ x xp1 k (ctr-1) in
    let ctr' = 8 * Seq.length k - ctr in
    let x, xp1 = if Spec.Ed25519.ith_bit k ctr' = 1 then xp1, x else x, xp1 in
    let xx = Spec.Ed25519.point_double x in
    let xxp1 = Spec.Ed25519.point_add x xp1 in
    if Spec.Ed25519.ith_bit k ctr' = 1 then xxp1, xx else (xx, xxp1) ) )
let lemma_montgomery_ladder_def_1 x xp1 k ctr = ()


#reset-options "--max_fuel 0 --z3rlimit 100"

val point_mul_:
  b:buffer Hacl.UInt64.t{length b = 80} ->
  k:buffer Hacl.UInt8.t{length k = 32 /\ disjoint b k} ->
  Stack unit
    (requires (fun h -> Buffer.live h k /\ live h b /\
      (let nq   = Buffer.sub b 0ul 20ul in
       let nqpq = Buffer.sub b 20ul 20ul in
       point_inv h nq /\ point_inv h nqpq) ))
    (ensures (fun h0 _ h1 -> Buffer.live h0 k /\ live h0 b /\ live h1 b /\ modifies_1 b h0 h1 /\
      (let nq   = Buffer.sub b 0ul 20ul in
       let nqpq = Buffer.sub b 20ul 20ul in
       point_inv h1 nq /\ point_inv h1 nqpq /\
       (as_point h1 nq, as_point h1 nqpq) == Spec.Ed25519.montgomery_ladder_ (as_point h0 nq) (as_point h0 nqpq)
                                                                (reveal_sbytes (as_seq h0 k)) 256)))

#reset-options "--max_fuel 0 --z3rlimit 500"

let point_mul_ b k =
  let h0 = ST.get() in
  let inv (h1: HyperStack.mem) (i: nat): Type0 =
    live h1 b /\ modifies_1 b h0 h1 /\ i <= 256 /\
    (let nq   = Buffer.sub b 0ul 20ul in
     let nqpq = Buffer.sub b 20ul 20ul in
     point_inv h1 nq /\ point_inv h1 nqpq /\
     (as_point h1 nq, as_point h1 nqpq) == Spec.Ed25519.montgomery_ladder_ (as_point h0 nq) (as_point h0 nqpq)
                                                              (reveal_sbytes (as_seq h0 k)) i)
  in
  let f' (i:UInt32.t{ FStar.UInt32.( 0 <= v i /\ v i < 256) }): Stack unit
    (requires (fun h -> inv h (UInt32.v i)))
    (ensures (fun h_1 _ h_2 -> FStar.UInt32.(inv h_2 (v i + 1))))
  =
    let nq   = Buffer.sub b  0ul 20ul in
    let nqpq = Buffer.sub b 20ul 20ul in
    let h  = ST.get() in
    loop_step b k FStar.UInt32.(256ul -^ i -^ 1ul);
    let h' = ST.get() in
    lemma_montgomery_ladder_def_1 (as_point h0 nq) (as_point h0 nqpq) (reveal_sbytes (as_seq h0 k)) (UInt32.v i + 1)
  in
  let nq   = Buffer.sub b  0ul 20ul in
  let nqpq = Buffer.sub b 20ul 20ul in
  lemma_montgomery_ladder_def_0 (as_point h0 nq) (as_point h0 nqpq) (reveal_sbytes (as_seq h0 k));
  C.Compat.Loops.for 0ul 256ul inv f'

let elemB = b:buffer Hacl.UInt64.t{length b = 5}

open Hacl.Bignum25519


inline_for_extraction
private
val make_zero:
  b:elemB ->
  Stack unit
    (requires (fun h -> live h b))
    (ensures (fun h0 _ h1 -> live h1 b /\ modifies_1 b h0 h1 /\ seval (as_seq h1 b) == 0
      /\ red_513 (as_seq h1 b)))
let make_zero b =
  let zero = Hacl.Cast.uint64_to_sint64 0uL in
  Hacl.Lib.Create64.make_h64_5 b zero zero zero zero zero;
  let h = ST.get() in
  lemma_reveal_seval (as_seq h b);
  assert_norm(pow2 51 = 0x8000000000000);
  lemma_intro_red_51 (as_seq h b);
  lemma_red_51_is_red_513 (as_seq h b)


inline_for_extraction
private
val make_one:
  b:elemB ->
  Stack unit
    (requires (fun h -> live h b))
    (ensures (fun h0 _ h1 -> live h1 b /\ modifies_1 b h0 h1 /\ seval (as_seq h1 b) == 1
      /\ Hacl.Bignum25519.red_513 (as_seq h1 b)))
let make_one b =
  let zero = Hacl.Cast.uint64_to_sint64 0uL in
  let one  = Hacl.Cast.uint64_to_sint64 1uL in
  Hacl.Lib.Create64.make_h64_5 b one zero zero zero zero;
  let h = ST.get() in
  lemma_reveal_seval (as_seq h b);
  assert_norm(pow2 51 = 0x8000000000000);
  lemma_intro_red_51 (as_seq h b);
  lemma_red_51_is_red_513 (as_seq h b)


inline_for_extraction
private
val make_point_inf:
  b:buffer Hacl.UInt64.t{length b = 20} ->
  Stack unit
    (requires (fun h -> live h b))
    (ensures (fun h0 _ h1 -> live h1 b /\ modifies_1 b h0 h1 /\ (as_point h1 b) == (0, 1, 1, 0) /\
     point_inv h1 b))
let make_point_inf b =
  let x = Buffer.sub b 0ul 5ul in
  let y = Buffer.sub b 5ul 5ul in
  let z = Buffer.sub b 10ul 5ul in
  let t = Buffer.sub b 15ul 5ul in
  make_zero x;
  let h1 = ST.get() in
  make_one y;
  let h2 = ST.get() in
  no_upd_lemma_1 h1 h2 y x;
  make_one z;
  let h3 = ST.get() in
  no_upd_lemma_1 h2 h3 z x;
  no_upd_lemma_1 h2 h3 z y;
  make_zero t;
  let h4 = ST.get() in
  no_upd_lemma_1 h3 h4 t x;
  no_upd_lemma_1 h3 h4 t y;
  no_upd_lemma_1 h3 h4 t z


#reset-options "--max_fuel 0 --max_ifuel 0 --z3rlimit 500 --using_facts_from Prims --using_facts_from FStar"
let sum_modifications (#a:Type) (b1:buffer a) (b2:buffer a) (h0 h1 h2:mem) 
  : Lemma (requires (live h0 b1 /\ 
                     live h0 b2 /\
                     modifies_1 b1 h0 h1 /\
                     modifies_1 b2 h1 h2))
          (ensures modifies_2 b1 b2 h0 h2)
  =
  lemma_reveal_modifies_1 b1 h0 h1;
  lemma_reveal_modifies_1 b2 h1 h2;
  lemma_intro_modifies_2 b1 b2 h0 h2

let modifies_2_to_2_1 (#a:Type) (b1:buffer a) (b2:buffer a) (h0 h1 h2:mem)
  : Lemma (requires (live h0 b2 /\
                     b1 `unused_in` h0 /\
                     modifies_0 h0 h1 /\
                     frameOf b1 == (HS.get_tip h0) /\
                     live h1 b1 /\
                     modifies_2 b1 b2 h1 h2 ))
          (ensures modifies_2_1 b2 h0 h2)
  = lemma_reveal_modifies_0 h0 h1;
    lemma_reveal_modifies_2 b1 b2 h1 h2;
    lemma_intro_modifies_2_1 b2 h0 h2

#reset-options "--max_fuel 0 --max_ifuel 0 --z3rlimit 500"
let point_mul result scalar q =
  let h0 = ST.get() in
  push_frame();
  let hh = ST.get () in
  let b = create (Hacl.Cast.uint64_to_sint64 0uL) 80ul in
  let hh0 = ST.get () in
  let nq   = Buffer.sub b  0ul 20ul in
  let nqpq = Buffer.sub b 20ul 20ul in
  make_point_inf nq;
  let hh1 = ST.get () in
  assert (modifies_1 nq hh0 hh1);
  assert (modifies_1 b hh0 hh1);
  Hacl.Impl.Ed25519.SwapConditional.copy nqpq q;
  let hh2 = ST.get () in
  assert (modifies_1 nqpq hh1 hh2);
  assert (modifies_1 b hh1 hh2);
  point_mul_ b scalar;
  let hh3 = ST.get () in
  assert (modifies_1 b hh2 hh3);
  lemma_modifies_1_trans b hh0 hh1 hh2;
  lemma_modifies_1_trans b hh0 hh2 hh3;
  assert (modifies_1 b hh0 hh3);
  Hacl.Impl.Ed25519.SwapConditional.copy result nq;
  let hh4 = ST.get () in
  assert (modifies_1 result hh3 hh4);
  sum_modifications b result hh0 hh3 hh4;
  assert (modifies_2 b result hh0 hh4);
  assert (b `unused_in` hh);
  assert (frameOf b == (HS.get_tip hh));
  modifies_2_to_2_1 b result hh hh0 hh4;
  pop_frame();
  let h1 = ST.get() in
  FStar.Buffer.modifies_popped_1 result h0 hh hh4 h1
