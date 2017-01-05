module Hacl.EC.Ladder


open FStar.Mul
open FStar.HyperStack
open FStar.Ghost
open FStar.Buffer

open Hacl.Bignum.Constants
open Hacl.Bignum.Parameters
open Hacl.Bignum.Limb
open Hacl.EC.Point
open Hacl.EC.AddAndDouble
open Hacl.EC.Ladder.BigLoop

module U32 = FStar.UInt32
module H8 = Hacl.UInt8


#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 10"

private val lemma_seq: #a:Type -> limb_zero:a -> n:nat{n <= 30} -> Lemma
  ((Seq.slice (Seq.slice (Seq.create 40 limb_zero) n (n+10)) 0 5 == Seq.create 5 limb_zero)
  /\ (Seq.slice (Seq.slice (Seq.create 40 limb_zero) n (n+10)) 5 10 == Seq.create 5 limb_zero))
private let lemma_seq #a limb_zero n =
  Seq.lemma_eq_intro (Seq.slice (Seq.create 40 (limb_zero)) n (n+10)) (Seq.create 10 limb_zero);
  Seq.lemma_eq_intro (Seq.slice (Seq.create 10 (limb_zero)) 0 (5)) (Seq.create 5 limb_zero);
  Seq.lemma_eq_intro (Seq.slice (Seq.create 10 (limb_zero)) 5 (10)) (Seq.create 5 limb_zero)

private let lemma_seq2 () : Lemma (Hacl.Spec.EC.AddAndDouble.red_513 (Seq.create 5 limb_zero)) = ()

val lemma_cmult__modifies: buf:buffer limb -> result:point -> h00:mem -> h0:mem -> h1:mem -> h2:mem -> Lemma
  (requires (Buffer.live h00 buf /\ live h00 result /\ h00.tip = h0.tip /\ h0.tip = h1.tip /\ h1.tip = h2.tip
    /\ modifies_one (frameOf buf) h0 h1 /\ modifies_1 result h1 h2 /\ frameOf buf <> frameOf result
    /\ modifies_1 buf h00 h0))
  (ensures (modifies (Set.union (Set.singleton (frameOf buf)) (Set.singleton (frameOf result))) h00 h2
    /\ modifies_buf_1 (frameOf result) result h00 h2))
#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 100"
let lemma_cmult__modifies buf result h00 h0 h1 h2 =
  lemma_reveal_modifies_1 result h1 h2;
  lemma_reveal_modifies_1 buf h00 h0


type uint8_p = Buffer.buffer H8.t


assume private val lemma_seq': h:mem -> b:buffer limb{Buffer.live h b /\ length b = 40} -> Lemma
  (requires (as_seq h b == Seq.create 40 limb_zero))
  (ensures (red_513 (as_seq h (getx (Buffer.sub b 0ul 10ul)))
    /\ red_513 (as_seq h (getz (Buffer.sub b 0ul 10ul)))))
(* private let lemma_seq' h b = *)
(*   let s = as_seq h b in *)
(*   let nq = Buffer.sub b 0ul 10ul in *)
(*   Seq.lemma_eq_intro (as_seq h nq) (Seq.create 10 limb_zero); *)
(*   Seq.lemma_eq_intro (as_seq h (getx nq)) (Seq.create 5 limb_zero); *)
(*   Seq.lemma_eq_intro (as_seq h (getz nq)) (Seq.create 5 limb_zero); admit() *)


private inline_for_extraction val cmult_: result:point ->
  buf:buffer limb{length buf = 40} ->
  scalar:uint8_p{length scalar = keylen} ->
  q:point ->
  Stack unit
  (requires (fun h -> Buffer.live h scalar /\ live h q /\ live h result
    /\ Buffer.live h buf /\ frameOf buf <> frameOf q /\ frameOf buf <> frameOf scalar /\ frameOf buf <> frameOf result
    /\ as_seq h buf == Seq.create 40 limb_zero
    /\ red_513 (as_seq h (getx q)) /\ red_513 (as_seq h (getz q))
  ))
  (ensures (fun h0 _ h1 -> Buffer.live h0 scalar /\ live h0 q /\ live h0 result /\ Buffer.live h0 buf
    /\ live h1 result /\ Buffer.live h1 buf
    /\ modifies (Set.union (Set.singleton (frameOf buf)) (Set.singleton (frameOf result))) h0 h1
    /\ modifies_buf_1 (frameOf result) result h0 h1
    /\ red_513 (as_seq h1 (getx result))
    /\ red_513 (as_seq h1 (getz result))
  ))
#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 1000"
private inline_for_extraction let cmult_ result point_buf n q =
  assert_norm(pow2 32 = 0x100000000);
  let nq    = Buffer.sub point_buf 0ul 10ul in
  let nqpq  = Buffer.sub point_buf 10ul 10ul in
  let nq2   = Buffer.sub point_buf 20ul 10ul in
  let nqpq2 = Buffer.sub point_buf 30ul 10ul in
  let h0 = ST.get() in
  lemma_seq' h0 point_buf;
  Hacl.EC.Point.copy nqpq q;
  let hh = ST.get() in
  no_upd_lemma_1 h0 hh nqpq nq;
  (getx nq).(0ul) <- limb_one;
  let h = ST.get() in
  cmult_big_loop n nq nqpq nq2 nqpq2 q 32ul;
  let h' = ST.get() in
  copy result nq;
  let h'' = ST.get() in
  lemma_cmult__modifies point_buf result h0 h h' h''


#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 100"

val cmult: result:point ->
  scalar:uint8_p{length scalar = keylen} ->
  q:point ->
  Stack unit
  (requires (fun h -> Buffer.live h scalar /\ live h q /\ live h result
    /\ red_513 (as_seq h (getx q))))
  (ensures (fun h0 _ h1 -> Buffer.live h0 scalar /\ live h0 q /\ live h0 result
    /\ live h1 result
    /\ modifies_1 result h0 h1
    /\ red_513 (as_seq h1 (getx result))
    /\ red_513 (as_seq h1 (getz result))
  ))
let cmult result n q =
  let h0 = ST.get() in
  push_frame();
  (* let nq    = result in *)
  let h1 = ST.get() in
  let point_buf = create limb_zero 40ul in
  (* (\* cmult_ result point_buf n q; *\) *)
  (* let nq = Buffer.sub point_buf 0ul 10ul in *)
  (* nq.(0ul) <- limb_one; *)
  (* let nqpq = Buffer.sub point_buf 10ul 10ul in *)
  (* let nq2 = Buffer.sub point_buf 20ul 10ul in *)
  (* let nqpq2 = Buffer.sub point_buf 30ul 10ul in *)
  (* lemma_seq 0; lemma_seq 10; lemma_seq 20; lemma_seq 30; *)
  (* Hacl.EC.Point.copy nqpq q; *)
  (* let h = ST.get() in *)
  (* cut (red_513 (as_seq h (getx nq))); *)
  (* cut (red_513 (as_seq h (getz nq))); *)
  (* cmult_big_loop n nq nqpq nq2 nqpq2 q 32ul; *)
  (* copy result nq; *)
  cmult_ result point_buf n q;
  pop_frame()
