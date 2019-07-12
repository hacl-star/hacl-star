module Hacl.EC.Ladder

module HS = FStar.HyperStack
module ST = FStar.HyperStack.ST

open FStar.HyperStack.All


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
  (requires (Buffer.live h00 buf /\ live h00 result /\ (HS.get_tip h00) = (HS.get_tip h0) /\ (HS.get_tip h0) = (HS.get_tip h1) /\ (HS.get_tip h1) = (HS.get_tip h2)
    /\ modifies_one (frameOf buf) h0 h1 /\ modifies_1 result h1 h2 /\ frameOf buf <> frameOf result
    /\ modifies_1 buf h00 h0))
  (ensures (modifies (Set.union (Set.singleton (frameOf buf)) (Set.singleton (frameOf result))) h00 h2
    /\ modifies_buf_1 (frameOf result) result h00 h2))
#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 100"
let lemma_cmult__modifies buf result h00 h0 h1 h2 =
  lemma_reveal_modifies_1 result h1 h2;
  lemma_reveal_modifies_1 buf h00 h0


type uint8_p = Buffer.buffer H8.t


private val lemma_seq_: #a:Type -> s:Seq.seq a -> n:nat -> l:nat{n + l <= Seq.length s} -> n':nat -> l':nat{n' >= n /\ n' + l' <= n + l} ->
  Lemma
  (requires (true))
  (ensures (Seq.slice s n' (n'+l') == Seq.slice (Seq.slice s n (n+l)) (n'-n) (n'-n+l')))
private let lemma_seq_ #a s n l n' l' =
  Seq.lemma_eq_intro (Seq.slice s n' (n'+l')) (Seq.slice (Seq.slice s n (n+l)) (n'-n) (n'-n+l'))


private val lemma_seq_': s:Seq.seq limb -> n:nat -> l:nat{n + l <= Seq.length s} -> n':nat -> l':nat{n' >= n /\ n' + l' <= n + l} ->
  Lemma
  (requires (Seq.slice s n (n+l) == Seq.create l limb_zero))
  (ensures (Seq.slice s n' (n'+l') == Seq.create l' limb_zero))
private let lemma_seq_' s n l n' l' =
  lemma_seq_ s n l n' l';
  let zeros = Seq.create l limb_zero in
  cut (Seq.slice s n' (n'+l') == Seq.slice zeros (n'-n) (n'-n+l'));
  Seq.lemma_eq_intro (Seq.create l' limb_zero) (Seq.slice zeros (n'-n) (n'-n+l'));
  cut (Seq.slice s n' (n'+l') == Seq.create l' limb_zero)


private val lemma_seq': h:mem -> b:buffer limb{Buffer.live h b /\ length b = 40} -> Lemma
  (requires (as_seq h b == Seq.create 40 limb_zero))
  (ensures (red_513 (as_seq h (getx (Buffer.sub b 0ul 10ul)))
    /\ red_513 (as_seq h (getz (Buffer.sub b 0ul 10ul)))
    /\ as_seq h (getx (Buffer.sub b 0ul 10ul)) == Seq.create 5 limb_zero
    /\ as_seq h (getz (Buffer.sub b 0ul 10ul)) == Seq.create 5 limb_zero
  ))
private let lemma_seq' h b =
  let s = sel h b in
  let i = idx b in
  let l = length b in
  lemma_seq_' s i 40 i 10;
  lemma_seq_' s i 10 i 5;
  lemma_seq_' s i 10 (i+5) 5


private val lemma_seq'': h:mem -> b:felem{Buffer.live h b /\ red_513 (as_seq h b)} -> Lemma
  (red_513 (Seq.upd (as_seq h b) 0 limb_one))
private let lemma_seq'' h b = ()


private val lemma_point_inf: s:seqelem -> s':seqelem -> Lemma
  (requires (s == Seq.upd (Seq.create 5 limb_zero) 0 limb_one /\ s' == Seq.create 5 limb_zero))
  (ensures ((s,s') == Hacl.Spec.EC.Format.point_inf())) 
private let lemma_point_inf s s' =
  let inf = Hacl.Spec.EC.Format.point_inf() in
  Seq.lemma_eq_intro (Seq.slice (Seq.create 10 limb_zero) 0 5) (Seq.create 5 limb_zero);
  Seq.lemma_eq_intro (Seq.slice (Seq.create 10 limb_zero) 5 10) (Seq.create 5 limb_zero);
  let ss = Seq.create 10 limb_zero in
  let x = Seq.slice ss 0 5 in
  let z = Seq.slice ss 5 10 in
  let x' = Seq.upd x 0 limb_one in
  cut (fst inf == x');
  Seq.lemma_eq_intro x (Seq.create 5 limb_zero);
  Seq.lemma_eq_intro z (Seq.create 5 limb_zero);
  cut (fst inf == Seq.upd (Seq.create 5 limb_zero) 0 limb_one);
  cut (snd inf == Seq.create 5 limb_zero)

#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 400"

[@"substitute"]
private val cmult_: result:point ->
  buf:buffer limb{length buf = 40} ->
  scalar:uint8_p{length scalar = keylen} ->
  q:point ->
  Stack unit
  (requires (fun h -> Buffer.live h scalar /\ live h q /\ live h result
    /\ Buffer.live h buf /\ frameOf buf <> frameOf q /\ frameOf buf <> frameOf scalar /\ frameOf buf <> frameOf result
    /\ as_seq h buf == Seq.create 40 limb_zero
    /\ red_513 (as_seq h (getx q)) /\ red_513 (as_seq h (getz q))
    /\ Hacl.Spec.Bignum.selem (as_seq h (getz q)) = 1
  ))
  (ensures (fun h0 _ h1 -> Buffer.live h0 scalar /\ live h0 q /\ live h0 result /\ Buffer.live h0 buf
    /\ red_513 (as_seq h0 (getx q)) /\ red_513 (as_seq h0 (getz q))
    /\ Hacl.Spec.Bignum.selem (as_seq h0 (getz q)) = 1
    /\ live h1 result /\ Buffer.live h1 buf
    /\ modifies (Set.union (Set.singleton (frameOf buf)) (Set.singleton (frameOf result))) h0 h1
    /\ modifies_buf_1 (frameOf result) result h0 h1
    /\ red_513 (as_seq h1 (getx result))
    /\ red_513 (as_seq h1 (getz result))
    /\ (let nq = (as_seq h1 (getx result), as_seq h1 (getz result)) in
       let n  = as_seq h0 scalar in
       let q  = (as_seq h0 (getx q), as_seq h0 (getz q)) in
       nq == Hacl.Spec.EC.Ladder.cmult_spec n q)
  ))
#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 2000"
[@"substitute"]
private let cmult_ result point_buf n q =
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
  lemma_seq'' hh (getx nq);
  (getx nq).(0ul) <- limb_one;
  let h = ST.get() in
  no_upd_lemma_1 hh h (getx nq) (getx nqpq);
  no_upd_lemma_1 hh h (getx nq) (getz nqpq);
  no_upd_lemma_1 hh h (getx nq) (getz nq);
  cut (as_seq h (getz nq) == Seq.create 5 limb_zero);
  cut (as_seq h (getx nq) == Seq.upd (Seq.create 5 limb_zero) 0 limb_one);
  lemma_point_inf (as_seq h (getx nq)) (as_seq h (getz nq));
  cut (let nq = (as_seq h (getx nq), as_seq h (getz nq)) in
    nq == Hacl.Spec.EC.Format.point_inf ());
  cmult_big_loop n nq nqpq nq2 nqpq2 q 32ul;
  let h' = ST.get() in
  copy result nq;
  let h'' = ST.get() in
  lemma_cmult__modifies point_buf result h0 h h' h''


#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 400"

val cmult: result:point ->
  scalar:uint8_p{length scalar = keylen} ->
  q:point ->
  Stack unit
  (requires (fun h -> Buffer.live h scalar /\ live h q /\ live h result
    /\ red_513 (as_seq h (getx q)) /\ red_513 (as_seq h (getz q))
    /\ Hacl.Spec.Bignum.selem (as_seq h (getz q)) = 1    
  ))
  (ensures (fun h0 _ h1 -> Buffer.live h0 scalar /\ live h0 q /\ live h0 result
    /\ red_513 (as_seq h0 (getx q)) /\ red_513 (as_seq h0 (getz q))
    /\ Hacl.Spec.Bignum.selem (as_seq h0 (getz q)) = 1
    /\ live h1 result
    /\ modifies_1 result h0 h1
    /\ red_513 (as_seq h1 (getx result))
    /\ red_513 (as_seq h1 (getz result))
    /\ (let nq = (as_seq h1 (getx result), as_seq h1 (getz result)) in
       let n  = as_seq h0 scalar in
       let q  = (as_seq h0 (getx q), as_seq h0 (getz q)) in
       nq == Hacl.Spec.EC.Ladder.cmult_spec n q)
  ))
let cmult result n q =
  let h0 = ST.get() in
  push_frame();
  let h1 = ST.get() in
  let point_buf = create limb_zero 40ul in
  let h2 = ST.get() in
  lemma_reveal_modifies_0 h1 h2;
  cmult_ result point_buf n q;
  pop_frame();
  let h4 = ST.get() in
  lemma_intro_modifies_1 result h0 h4
