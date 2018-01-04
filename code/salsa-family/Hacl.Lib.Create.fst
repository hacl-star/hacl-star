(* This module implements specialized functions mapped to the Seq.Create module *)
(* It should go away as soon as the normalizer can handle similar properties on sequences *)

module Hacl.Lib.Create

module ST = FStar.HyperStack.ST

open FStar.HyperStack.All

open FStar.Buffer
open Seq.Create


#reset-options "--max_fuel 0 --z3rlimit 100"

let h32 = Hacl.UInt32.t

[@ Substitute]
val make_h32_4: b:buffer h32{length b = 4} ->
  s0:h32 -> s1:h32 -> s2:h32 -> s3:h32 ->
  Stack unit
    (requires (fun h -> live h b))
    (ensures (fun h0 _ h1 -> live h1 b /\ modifies_1 b h0 h1 /\
      as_seq h1 b == create_4 s0 s1 s2 s3))
let make_h32_4 b s0 s1 s2 s3 =
  b.(0ul) <- s0;  b.(1ul) <- s1;  b.(2ul) <- s2;  b.(3ul) <- s3;
  let h = ST.get() in
  Seq.lemma_eq_intro (as_seq h b) (create_4 s0 s1 s2 s3)

[@ Substitute]
val make_h32_8: b:buffer h32{length b = 8} ->
  s0:h32 -> s1:h32 -> s2:h32 -> s3:h32 -> s4:h32 -> s5:h32 -> s6:h32 -> s7:h32 ->
  Stack unit
    (requires (fun h -> live h b))
    (ensures (fun h0 _ h1 -> live h1 b /\ modifies_1 b h0 h1 /\
      as_seq h1 b == create_8 s0 s1 s2 s3 s4 s5 s6 s7))
let make_h32_8 b s0 s1 s2 s3 s4  s5 s6 s7 =
  make_h32_4 (sub b 0ul 4ul) s0 s1 s2 s3;
  make_h32_4 (sub b 4ul 4ul) s4 s5 s6 s7;
  let h = ST.get() in
  Seq.lemma_eq_intro (as_seq h b) (create_8 s0 s1 s2 s3 s4 s5 s6 s7)

[@ Substitute]
val make_h32_16: b:buffer h32{length b = 16} ->
  s0:h32 -> s1:h32 -> s2:h32 -> s3:h32 -> s4:h32 -> s5:h32 -> s6:h32 -> s7:h32 ->
  s8:h32 -> s9:h32 -> s10:h32 -> s11:h32 -> s12:h32 -> s13:h32 -> s14:h32 -> s15:h32 ->
  Stack unit
    (requires (fun h -> live h b))
    (ensures (fun h0 _ h1 -> live h1 b /\ modifies_1 b h0 h1 /\
      as_seq h1 b == create_16 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15))
let make_h32_16 b s0 s1 s2 s3 s4  s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 =
  make_h32_8 (sub b 0ul 8ul) s0 s1 s2 s3 s4  s5 s6 s7;
  make_h32_8 (sub b 8ul 8ul) s8 s9 s10 s11 s12 s13 s14 s15;
  let h = ST.get() in
  Seq.lemma_eq_intro (as_seq h b) (create_16 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15)

