module Hacl.Lib.Create128

module ST = FStar.HyperStack.ST

open FStar.HyperStack.All


#reset-options "--max_fuel 0 --z3rlimit 100"

open FStar.Buffer
open Seq.Create

let h128 = Hacl.UInt128.t

inline_for_extraction
val make_h128_9: b:buffer h128{length b = 9} ->
  s0:h128 -> s1:h128 -> s2:h128 -> s3:h128 -> s4:h128 ->
  s5:h128 -> s6:h128 -> s7:h128 -> s8:h128 ->
  Stack unit
    (requires (fun h -> live h b))
    (ensures (fun h0 _ h1 -> live h1 b /\ modifies_1 b h0 h1 /\
      as_seq h1 b == create_9 s0 s1 s2 s3 s4 s5 s6 s7 s8))
let make_h128_9 b s0 s1 s2 s3 s4 s5 s6 s7 s8 =
  b.(0ul) <- s0;  b.(1ul) <- s1;  b.(2ul) <- s2;  b.(3ul) <- s3; b.(4ul) <- s4;
  b.(5ul) <- s5;  b.(6ul) <- s6;  b.(7ul) <- s7;  b.(8ul) <- s8;
  let h = ST.get() in
  Seq.lemma_eq_intro (as_seq h b) (create_9 s0 s1 s2 s3 s4 s5 s6 s7 s8)
