module Hacl.EC.Ladder.SmallLoop


open FStar.Mul
open FStar.HyperStack
open FStar.Ghost
open FStar.Buffer

open Hacl.Bignum.Constants
open Hacl.Bignum.Parameters
open Hacl.Bignum.Limb
open Hacl.EC.Point
open Hacl.Spec.EC.Point
open Hacl.EC.AddAndDouble


module U32 = FStar.UInt32
module H8 = Hacl.UInt8


#set-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 100"


type uint8_p = buffer H8.t

private inline_for_extraction val last_bit: byt:H8.t -> Tot (b:limb{v b = 0 \/ v b = 1})
private inline_for_extraction let last_bit byt =
  let bit = byte_to_limb (H8.(byt >>^ 7ul)) in
  Math.Lemmas.lemma_div_lt (H8.v byt) 8 7;
  assert_norm(pow2 1 = 2); cut (v bit = 0 \/ v bit = 1);
  bit


private inline_for_extraction val cmult_small_loop_step_1:
  nq:point ->
  nqpq:point ->
  nq2:point ->
  nqpq2:point ->
  q:point ->
  byte:H8.t ->
  i:ctr{U32.v i > 0} ->
  Stack unit
    (requires (fun h -> fmonty_pre h nq2 nqpq2 nq nqpq q))
    (ensures (fun h0 _ h1 -> fmonty_pre h0 nq2 nqpq2 nq nqpq q
      /\ HyperStack.modifies_one (frameOf nq) h0 h1
      /\ fmonty_pre h1 nq2 nqpq2 nq nqpq q
      /\ (let spointa1 : spoint_513 = (as_seq h1 (getx nq), (as_seq h1 (getz nq))) in
         let spointb1 : spoint_513 = (as_seq h1 (getx nqpq), (as_seq h1 (getz nqpq))) in
         (spointa1, spointb1) ==
          swap_conditional_spec (as_seq h0 (getx nq), as_seq h0 (getz nq)) (as_seq h0 (getx nqpq), as_seq h0 (getz nqpq)) (last_bit byte))
    ))
#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 100"
private inline_for_extraction let cmult_small_loop_step_1 nq nqpq nq2 nqpq2 q byt i =
  let bit = last_bit byt in
  let h0 = ST.get() in
  swap_conditional nq nqpq bit;
  let h1 = ST.get() in
  lemma_reveal_modifies_2 nq nqpq h0 h1


private inline_for_extraction val cmult_small_loop_step_2:
  nq:point ->
  nqpq:point ->
  nq2:point ->
  nqpq2:point ->
  q:point ->
  byte:H8.t ->
  i:ctr{U32.v i > 0} ->
  Stack unit
    (requires (fun h -> fmonty_pre h nq2 nqpq2 nq nqpq q))
    (ensures (fun h0 _ h1 -> fmonty_pre h0 nq2 nqpq2 nq nqpq q
      /\ HyperStack.modifies_one (frameOf nq) h0 h1
      /\ fmonty_pre h1 nq nqpq nq2 nqpq2 q
      /\ (as_seq h1 (getx nq2), as_seq h1 (getz nq2), as_seq h1 (getx nqpq2), as_seq h1 (getz nqpq2)) ==
          Hacl.Spec.EC.AddAndDouble2.fmonty_tot (as_seq h0 (getx nq)) (as_seq h0 (getz nq)) (as_seq h0 (getx nqpq)) (as_seq h0 (getz nqpq)) (as_seq h0 (getx q))))
#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 100"
private inline_for_extraction let cmult_small_loop_step_2 nq nqpq nq2 nqpq2 q byt i =
  fmonty nq2 nqpq2 nq nqpq q

open Hacl.Spec.EC.Ladder

private inline_for_extraction val cmult_small_loop_step:
  nq:point ->
  nqpq:point ->
  nq2:point ->
  nqpq2:point ->
  q:point ->
  byte:H8.t ->
  i:ctr{U32.v i <= 8 /\ U32.v i > 0} ->
  Stack unit
    (requires (fun h -> fmonty_pre h nq2 nqpq2 nq nqpq q))
    (ensures (fun h0 _ h1 -> fmonty_pre h0 nq2 nqpq2 nq nqpq q
      /\ HyperStack.modifies_one (frameOf nq) h0 h1
      /\ fmonty_pre h1 nq nqpq nq2 nqpq2 q
      /\ (let spointa1 : spoint_513 = (as_seq h1 (getx nq2), (as_seq h1 (getz nq2))) in
         let spointb1 : spoint_513 = (as_seq h1 (getx nqpq2), (as_seq h1 (getz nqpq2))) in
         let pointq   : spoint_513' = (as_seq h0 (getx q), (as_seq h0 (getz q))) in
         let spointa0 : spoint_513 = (as_seq h0 (getx nq), (as_seq h0 (getz nq))) in
         let spointb0 : spoint_513 = (as_seq h0 (getx nqpq), (as_seq h0 (getz nqpq))) in
         (spointa1, spointb1) == cmult_small_loop_step_spec (spointa0) (spointb0) pointq byte i)
    ))
#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 100"
private inline_for_extraction let cmult_small_loop_step nq nqpq nq2 nqpq2 q byt i =
  cmult_small_loop_step_1 nq nqpq nq2 nqpq2 q byt i;
  cmult_small_loop_step_2 nq nqpq nq2 nqpq2 q byt i;
  cmult_small_loop_step_1 nq2 nqpq2 nq nqpq q byt i


private inline_for_extraction val cmult_small_loop_double_step:
  nq:point ->
  nqpq:point ->
  nq2:point ->
  nqpq2:point ->
  q:point ->
  byte:H8.t ->
  i:ctr{U32.v i <= 8 /\ U32.v i > 1} ->
  Stack unit
    (requires (fun h -> fmonty_pre h nq2 nqpq2 nq nqpq q))
    (ensures (fun h0 _ h1 -> fmonty_pre h0 nq2 nqpq2 nq nqpq q
      /\ HyperStack.modifies_one (frameOf nq) h0 h1
      /\ fmonty_pre h1 nq2 nqpq2 nq nqpq q
      /\ (let spointa1 : spoint_513 = (as_seq h1 (getx nq), (as_seq h1 (getz nq))) in
         let spointb1 : spoint_513 = (as_seq h1 (getx nqpq), (as_seq h1 (getz nqpq))) in
         let pointq   : spoint_513' = (as_seq h0 (getx q), (as_seq h0 (getz q))) in
         let spointa0 : spoint_513 = (as_seq h0 (getx nq), (as_seq h0 (getz nq))) in
         let spointb0 : spoint_513 = (as_seq h0 (getx nqpq), (as_seq h0 (getz nqpq))) in
         (spointa1, spointb1) == cmult_small_loop_double_step_spec (spointa0) (spointb0) pointq byte i)
    ))
#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 400"
private inline_for_extraction let cmult_small_loop_double_step nq nqpq nq2 nqpq2 q byt i =
  cmult_small_loop_step nq nqpq nq2 nqpq2 q byt i;
  let byt = H8.(byt <<^ 1ul) in
  cmult_small_loop_step nq2 nqpq2 nq nqpq q byt U32.(i-^1ul)


val cmult_small_loop:
  nq:point ->
  nqpq:point ->
  nq2:point ->
  nqpq2:point ->
  q:point ->
  byte:H8.t ->
  i:ctr{U32.v i <= 8 /\ U32.v i % 2 = 0} ->
  Stack unit
    (requires (fun h -> fmonty_pre h nq2 nqpq2 nq nqpq q))
    (ensures (fun h0 _ h1 -> fmonty_pre h0 nq2 nqpq2 nq nqpq q
      /\ HyperStack.modifies_one (frameOf nq) h0 h1
      /\ (fmonty_pre h1 nq2 nqpq2 nq nqpq q
        /\ (let spointa1 : spoint_513 = (as_seq h1 (getx nq), (as_seq h1 (getz nq))) in
           let spointb1 : spoint_513 = (as_seq h1 (getx nqpq), (as_seq h1 (getz nqpq))) in
           let pointq   : spoint_513' = (as_seq h0 (getx q), (as_seq h0 (getz q))) in
           let spointa0 : spoint_513 = (as_seq h0 (getx nq), (as_seq h0 (getz nq))) in
           let spointb0 : spoint_513 = (as_seq h0 (getx nqpq), (as_seq h0 (getz nqpq))) in
           (spointa1, spointb1) == cmult_small_loop_spec (spointa0) (spointb0) pointq byte i))
    ))
#reset-options "--initial_fuel 1 --max_fuel 1 --z3rlimit 1000"
let rec cmult_small_loop nq nqpq nq2 nqpq2 q byt i =
  if (U32.(i =^ 0ul)) then ()
  else (
    let i' = U32.(i -^ 2ul) in
    cut (U32.v i >= 2);
    cut (U32.v i' % 2 = 0);
    cmult_small_loop_double_step nq nqpq nq2 nqpq2 q byt i;
    let byt' = H8.(byt <<^ 2ul) in
    cmult_small_loop nq nqpq nq2 nqpq2 q byt' i'
    (* cut (U32.v i > 0); *)
    (* cmult_small_loop_step nq nqpq nq2 nqpq2 q byt i; *)
    (* let t = nq in *)
    (* let nq = nq2 in *)
    (* let nq2 = t in *)
    (* let t = nqpq in *)
    (* let nqpq = nqpq2 in *)
    (* let nqpq2 = t in *)
    (* let byt = H8.(byt <<^ 1ul) in *)
    (* cmult_small_loop nq nqpq nq2 nqpq2 q byt (U32.(i -^ 1ul)) *)
  )
