module Hacl.Impl.Store56

module ST = FStar.HyperStack.ST

open FStar.HyperStack.All

open FStar.Buffer
open Hacl.UInt64
open Hacl.Endianness
open Hacl.Spec.BignumQ.Eval
open Hacl.Spec.Endianness

let hint8_p = buffer Hacl.UInt8.t
let qelem   = buffer Hacl.UInt64.t


#reset-options "--max_fuel 0 --z3rlimit 20"

inline_for_extraction
private
val hstore56_le:
  out:hint8_p{length out = 32} ->
  off:FStar.UInt32.t{UInt32.v off <= 21} ->
  x:Hacl.UInt64.t{v x < pow2 56} ->
  Stack unit
    (requires (fun h -> live h out))
    (ensures (fun h0 _ h1 ->
      live h1 out /\ modifies_1 (Buffer.sub out off 8ul) h0 h1 /\
      hlittle_endian (as_seq h1 (Buffer.sub out off 7ul)) == v x))
#reset-options "--max_fuel 0 --z3rlimit 200"
let hstore56_le out off x =
  let b8 = Buffer.sub out off 8ul in
  hstore64_le b8 x;
  let h = ST.get() in
  Seq.lemma_eq_intro (as_seq h b8) (Seq.append (Seq.slice (as_seq h b8) 0 7) (Seq.slice (as_seq h b8) 7 8));
  FStar.Old.Endianness.little_endian_append (reveal_sbytes (Seq.slice (as_seq h b8) 0 7)) (reveal_sbytes (Seq.slice (as_seq h b8) 7 8));
  FStar.Old.Endianness.lemma_little_endian_is_bounded (reveal_sbytes (Seq.slice (as_seq h b8) 0 7));
  Seq.lemma_eq_intro (as_seq h (Buffer.sub out off 7ul)) (Seq.slice (as_seq h b8) 0 7)


open FStar.Mul

private
val lemma_append_5:
  b0:Seq.seq Hacl.UInt8.t{Seq.length b0 = 7} ->
  b1:Seq.seq Hacl.UInt8.t{Seq.length b1 = 7} ->
  b2:Seq.seq Hacl.UInt8.t{Seq.length b2 = 7} ->
  b3:Seq.seq Hacl.UInt8.t{Seq.length b3 = 7} ->
  b4:Seq.seq Hacl.UInt8.t{Seq.length b4 = 4} ->
  Lemma (hlittle_endian FStar.Seq.(b0 @| b1 @| b2 @| b3 @| b4) ==
    hlittle_endian b0 + pow2 56 * hlittle_endian b1 + pow2 112 * hlittle_endian b2 + pow2 168 * hlittle_endian b3 + pow2 224 * hlittle_endian b4)
let lemma_append_5 b0 b1 b2 b3 b4 =
  let open FStar.Seq in
  let b = b0 @| b1 @| b2 @| b3 @| b4 in
  Seq.lemma_eq_intro (((b0 @| b1 @| b2 @| b3) @| b4)) (b);
  FStar.Old.Endianness.little_endian_append (reveal_sbytes (b0 @| b1 @| b2 @| b3)) (reveal_sbytes b4);
  Seq.lemma_eq_intro ((b0 @| b1 @| b2) @| b3) (b0 @| b1 @| b2 @| b3);
  FStar.Old.Endianness.little_endian_append (reveal_sbytes (b0 @| b1 @| b2)) (reveal_sbytes b3);
  Seq.lemma_eq_intro ((b0 @| b1) @| b2) (b0 @| b1 @| b2);
  FStar.Old.Endianness.little_endian_append (reveal_sbytes (b0 @| b1)) (reveal_sbytes b2);
  FStar.Old.Endianness.little_endian_append (reveal_sbytes b0) (reveal_sbytes b1)


private
let lemm_append_5' h (b:hint8_p{length b = 32 /\ live h b}) : Lemma
  (as_seq h b == FStar.Seq.(as_seq h (Buffer.sub b 0ul 7ul) @|
                            as_seq h (Buffer.sub b 7ul 7ul) @|
                            as_seq h (Buffer.sub b 14ul 7ul) @|
                            as_seq h (Buffer.sub b 21ul 7ul) @|
                            as_seq h (Buffer.sub b 28ul 4ul)))
  = let open FStar.Seq in
    Seq.lemma_eq_intro (as_seq h (Buffer.sub b 0ul 7ul) @|
                            as_seq h (Buffer.sub b 7ul 7ul) @|
                            as_seq h (Buffer.sub b 14ul 7ul) @|
                            as_seq h (Buffer.sub b 21ul 7ul) @|
                            as_seq h (Buffer.sub b 28ul 4ul)) (as_seq h b)


val store_56:
  out:hint8_p{length out = 32} ->
  b:qelem{length b = 5} ->
  Stack unit
    (requires (fun h -> live h out /\ live h b /\
      (let s = as_seq h b in
        v (Seq.index s 0) < pow2 56 /\
        v (Seq.index s 1) < pow2 56 /\
        v (Seq.index s 2) < pow2 56 /\
        v (Seq.index s 3) < pow2 56 /\
        v (Seq.index s 4) < pow2 32)))
    (ensures (fun h0 _ h1 -> live h1 out /\ live h0 b /\ modifies_1 out h0 h1 /\
      hlittle_endian (as_seq h1 out) == Hacl.Spec.BignumQ.Eval.eval_q (reveal_h64s (as_seq h0 b))))
let store_56 out b =
  assert_norm(pow2 56 = 0x100000000000000);
  assert_norm(pow2 112 = 0x10000000000000000000000000000);
  assert_norm(pow2 168 = 0x1000000000000000000000000000000000000000000);
  assert_norm(pow2 224 = 0x100000000000000000000000000000000000000000000000000000000);
  let b0 = b.(0ul) in
  let b1 = b.(1ul) in
  let b2 = b.(2ul) in
  let b3 = b.(3ul) in
  let b4 = b.(4ul) in
  let b4 = Hacl.Cast.sint64_to_sint32 b4 in
  Math.Lemmas.modulo_lemma (Hacl.UInt32.v b4) (pow2 32);
  let h0 = ST.get() in
  hstore56_le out 0ul b0;
  let h1 = ST.get() in
  (* assert(FStar.Old.Endianness.little_endian (as_seq h1 (Buffer.sub out 0ul 7ul)) = v b0); *)
  hstore56_le out 7ul b1;
  let h2 = ST.get() in
  no_upd_lemma_1 h1 h2 (Buffer.sub out 7ul 8ul) (Buffer.sub out 0ul 7ul);
  hstore56_le out 14ul b2;
  let h3 = ST.get() in
  no_upd_lemma_1 h2 h3 (Buffer.sub out 14ul 8ul) (Buffer.sub out 0ul 7ul);
  no_upd_lemma_1 h2 h3 (Buffer.sub out 14ul 8ul) (Buffer.sub out 7ul 7ul);
  hstore56_le out 21ul b3;
  let h4 = ST.get() in
  no_upd_lemma_1 h3 h4 (Buffer.sub out 21ul 8ul) (Buffer.sub out 0ul 7ul);
  no_upd_lemma_1 h3 h4 (Buffer.sub out 21ul 8ul) (Buffer.sub out 7ul 7ul);
  no_upd_lemma_1 h3 h4 (Buffer.sub out 21ul 8ul) (Buffer.sub out 14ul 7ul);
  hstore32_le (Buffer.sub out 28ul 4ul) b4;
  let h = ST.get() in
  no_upd_lemma_1 h4 h (Buffer.sub out 28ul 4ul) (Buffer.sub out 0ul 7ul);
  no_upd_lemma_1 h4 h (Buffer.sub out 28ul 4ul) (Buffer.sub out 7ul 7ul);
  no_upd_lemma_1 h4 h (Buffer.sub out 28ul 4ul) (Buffer.sub out 14ul 7ul);
  no_upd_lemma_1 h4 h (Buffer.sub out 28ul 4ul) (Buffer.sub out 21ul 7ul);
  assert(hlittle_endian (as_seq h (Buffer.sub out 0ul 7ul)) = v b0);
  assert(hlittle_endian (as_seq h (Buffer.sub out 7ul 7ul)) = v b1);
  assert(hlittle_endian (as_seq h (Buffer.sub out 14ul 7ul)) = v b2);
  assert(hlittle_endian (as_seq h (Buffer.sub out 21ul 7ul)) = v b3);
  assert(hlittle_endian (as_seq h (Buffer.sub out 28ul 4ul)) = Hacl.UInt32.v b4);
  lemma_append_5 (as_seq h (Buffer.sub out 0ul 7ul))
                 (as_seq h (Buffer.sub out 7ul 7ul))
                 (as_seq h (Buffer.sub out 14ul 7ul))
                 (as_seq h (Buffer.sub out 21ul 7ul))
                 (as_seq h (Buffer.sub out 28ul 4ul));
   lemm_append_5' h out
