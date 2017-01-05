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

private inline_for_extraction val cmult_small_loop_step:
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
      /\ fmonty_pre h1 nq nqpq nq2 nqpq2 q))
#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 1000"
private inline_for_extraction let cmult_small_loop_step nq nqpq nq2 nqpq2 q byt i =
  let nqx = getx nq in
  let nqz = getz nq in
  let nqpqx = getx nqpq in
  let nqpqz = getz nqpq in
  let nqx2 = getx nq2 in
  let nqz2 = getz nq2 in
  let nqpqx2 = getx nqpq2 in
  let nqpqz2 = getz nqpq2 in
  let bit = last_bit byt in
  let h0 = ST.get() in
  swap_conditional nq nqpq bit;
  let h1 = ST.get() in
  lemma_reveal_modifies_2 nq nqpq h0 h1;
  cut (fmonty_pre h1 nq2 nqpq2 nq nqpq q);
  fmonty nq2 nqpq2 nq nqpq q;
  let h2 = ST.get() in
  cut (fmonty_pre h2 nq nqpq nq2 nqpq2 q);
  swap_conditional nq2 nqpq2 bit;
  let h3 = ST.get() in
  lemma_reveal_modifies_2 nq nqpq h0 h1;  
  cut (fmonty_pre h3 nq nqpq nq2 nqpq2 q)


#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 1000"

private val cmult_small_loop:
  nq:point ->
  nqpq:point ->
  nq2:point ->
  nqpq2:point ->
  q:point ->
  byte:H8.t ->
  i:ctr{U32.v i <= 8} ->  
  Stack unit
    (requires (fun h -> fmonty_pre h nq2 nqpq2 nq nqpq q))
    (ensures (fun h0 _ h1 -> fmonty_pre h0 nq2 nqpq2 nq nqpq q
      /\ HyperStack.modifies_one (frameOf nq) h0 h1
      /\ ((U32.v i % 2 = 1) ==> fmonty_pre h1 nq nqpq nq2 nqpq2 q)
      /\ ((U32.v i % 2 = 0) ==> fmonty_pre h1 nq2 nqpq2 nq nqpq q)
    ))
#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 1000"
private let rec cmult_small_loop nq nqpq nq2 nqpq2 q byt i =
  let nqx = getx nq in
  let nqz = getz nq in
  let nqpqx = getx nqpq in
  let nqpqz = getz nqpq in
  let nqx2 = getx nq2 in
  let nqz2 = getz nq2 in
  let nqpqx2 = getx nqpq2 in
  let nqpqz2 = getz nqpq2 in
  if (U32.(i =^ 0ul)) then ()
  else (
    cmult_small_loop_step nq nqpq nq2 nqpq2 q byt i;
    let t = nq in
    let nq = nq2 in
    let nq2 = t in
    let t = nqpq in
    let nqpq = nqpq2 in
    let nqpq2 = t in
    let byt = H8.(byt <<^ 1ul) in
    cmult_small_loop nq nqpq nq2 nqpq2 q byt (U32.(i -^ 1ul))
  )


private val cmult_big_loop:
  n:uint8_p{length n = 32} ->
  nq:point ->
  nqpq:point ->
  nq2:point ->
  nqpq2:point ->
  q:point ->
  i:U32.t{U32.v i <= 32} ->
  Stack unit
    (requires (fun h -> Buffer.live h n /\ frameOf n <> frameOf nq2 /\ fmonty_pre h nq2 nqpq2 nq nqpq q))
    (ensures (fun h0 _ h1 -> fmonty_pre h0 nq2 nqpq2 nq nqpq q
      /\ HyperStack.modifies_one (frameOf nq2) h0 h1
      /\ fmonty_pre h1 nq2 nqpq2 nq nqpq q))
#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 1000"      
private let rec cmult_big_loop n nq nqpq nq2 nqpq2 q i =
  if (U32.(i =^ 0ul)) then ()
  else (
    let i = U32.(i -^ 1ul) in
    let byte = n.(i) in
    cmult_small_loop nq nqpq nq2 nqpq2 q byte 8ul;
    cmult_big_loop n nq nqpq nq2 nqpq2 q i
  )


#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 100"

assume private val lemma_seq: n:nat{n <= 30} -> Lemma
  ((Seq.slice (Seq.slice (Seq.create 40 limb_zero) n (n+10)) 0 5 == Seq.create 5 limb_zero)
  /\ (Seq.slice (Seq.slice (Seq.create 40 limb_zero) n (n+10)) 5 10 == Seq.create 5 limb_zero))
(* private let lemma_seq n = *)
(*   Seq.lemma_eq_intro (Seq.slice (Seq.create 40 (limb_zero)) n (n+10)) (Seq.create 10 limb_zero); *)
(*   Seq.lemma_eq_intro (Seq.slice (Seq.create 10 (limb_zero)) 0 (5)) (Seq.create 5 limb_zero); *)
(*   Seq.lemma_eq_intro (Seq.slice (Seq.create 10 (limb_zero)) 5 (10)) (Seq.create 5 limb_zero) *)


assume val lemma_cmult__modifies: buf:buffer limb -> result:point -> h0:mem -> h1:mem -> h2:mem -> Lemma
  (requires (Buffer.live h0 buf /\ live h0 result
    /\ modifies_one (frameOf buf) h0 h1 /\ modifies_1 result h1 h2 /\ frameOf buf <> frameOf result))
  (ensures (modifies (Set.union (Set.singleton (frameOf buf)) (Set.singleton (frameOf result))) h0 h2
    /\ modifies_buf_1 (frameOf result) result h0 h2))
(* let lemma_cmult__modifies buf result h0 h1 h2 = *)
(*   lemma_reveal_modifies_1 result h1 h2; *)
(*   cut (modifies_buf_1 (frameOf result) result h1 h2); *)
(*   cut (modifies_ref (frameOf result) !{as_ref result} h1 h2);   *)
(*   cut (forall (i:n *)
(*   cut (Map.sel h0.h (frameOf result) == Map.sel h1.h (frameOf result)); *)
(*   cut (modifies_buf_1 (frameOf result) result h0 h2); *)
(*   admit() *)
  


private inline_for_extraction val cmult_: result:point ->
  buf:buffer limb{length buf = 40} ->
  scalar:uint8_p{length scalar = keylen} ->
  q:point ->
  Stack unit
  (requires (fun h -> Buffer.live h scalar /\ live h q /\ live h result
    /\ Buffer.live h buf /\ frameOf buf <> frameOf q /\ frameOf buf <> frameOf scalar /\ frameOf buf <> frameOf result
    /\ as_seq h buf == Seq.create 40 limb_zero
    /\ red_513 (as_seq h (getx q))))
  (ensures (fun h0 _ h1 -> Buffer.live h0 scalar /\ live h0 q /\ live h0 result /\ Buffer.live h0 buf
    /\ live h1 result /\ Buffer.live h1 buf
    (* /\ modifies_2 result buf h0 h1 *)
    /\ modifies (Set.union (Set.singleton (frameOf buf)) (Set.singleton (frameOf result))) h0 h1
    /\ modifies_buf_1 (frameOf result) result h0 h1
    /\ red_513 (as_seq h1 (getx result))
    /\ red_513 (as_seq h1 (getz result))
  ))
private inline_for_extraction let cmult_ result point_buf n q =
  assert_norm(pow2 32 = 0x100000000);
  let nq = Buffer.sub point_buf 0ul 10ul in
  let nqpq = Buffer.sub point_buf 10ul 10ul in
  let nq2 = Buffer.sub point_buf 20ul 10ul in
  let nqpq2 = Buffer.sub point_buf 30ul 10ul in
  lemma_seq 0; lemma_seq 10; lemma_seq 20; lemma_seq 30;
  Hacl.EC.Point.copy nqpq q;
  let h = ST.get() in
  assume (fmonty_pre h nq2 nqpq2 nq nqpq q);
  cmult_big_loop n nq nqpq nq2 nqpq2 q 32ul;
  let h' = ST.get() in
  copy result nq;
  let h'' = ST.get() in
  lemma_cmult__modifies point_buf result h h' h'';
  cut (modifies_buf_1 (frameOf result) result h h'')


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
  push_frame();
  (* let nq    = result in *)
  let point_buf = create limb_zero 40ul in
  (* cmult_ result point_buf n q; *)
  let nq = Buffer.sub point_buf 0ul 10ul in
  nq.(0ul) <- limb_one;
  let nqpq = Buffer.sub point_buf 10ul 10ul in
  let nq2 = Buffer.sub point_buf 20ul 10ul in
  let nqpq2 = Buffer.sub point_buf 30ul 10ul in
  lemma_seq 0; lemma_seq 10; lemma_seq 20; lemma_seq 30;
  Hacl.EC.Point.copy nqpq q;
  let h = ST.get() in
  cut (red_513 (as_seq h (getx nq)));
  cut (red_513 (as_seq h (getz nq)));
  cmult_big_loop n nq nqpq nq2 nqpq2 q 32ul;
  copy result nq;
  pop_frame()
