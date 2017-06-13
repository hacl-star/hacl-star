module Hacl.Lib.LoadStore32

module ST = FStar.HyperStack.ST

open FStar.HyperStack.All

open FStar.Mul
open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Buffer
open Hacl.UInt32
open Hacl.Spec.Endianness
open Hacl.Endianness

module U32 = FStar.UInt32
module H32 =  Hacl.UInt32

let uint8_p = b:buffer Hacl.UInt8.t

#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 100"


val uint32s_from_le_bytes:
  output:buffer H32.t ->
  input:uint8_p{disjoint output input} ->
  len:U32.t{length output = U32.v len /\ 4 * U32.v len = length input} ->
  Stack unit
    (requires (fun h -> live h output /\ live h input))
    (ensures  (fun h0 _ h1 -> live h1 output /\ live h0 input /\ modifies_1 output h0 h1 /\
      (let o = reveal_h32s (as_seq h1 output) in
       let i = reveal_sbytes (as_seq h0 input) in
       o == Spec.Lib.uint32s_from_le (U32.v len) i)))
let rec uint32s_from_le_bytes output input len =
  let h0 = ST.get() in
  let inv (h1: mem) (i: nat): Type0 =
    live h1 output /\ modifies_1 output h0 h1 /\ 0 <= i /\ i <= UInt32.v len
    /\ Seq.slice (reveal_h32s (as_seq h1 output)) 0 i == Spec.Lib.uint32s_from_le i (reveal_sbytes (Seq.slice (as_seq h0 input) 0 (4 * i)))
  in
  let f' (i:UInt32.t{ FStar.UInt32.( 0 <= v i /\ v i < v len ) }): Stack unit
    (requires (fun h -> inv h (UInt32.v i)))
    (ensures (fun h_1 _ h_2 -> FStar.UInt32.(inv h_2 (v i + 1))))
  = let h = ST.get() in
    let open FStar.UInt32 in
    assert(as_seq h input == as_seq h0 input);
    let inputi = hload32_le (Buffer.sub input (4ul*^i) (4ul)) in
    output.(i) <- inputi;
    let h' = ST.get() in
    Spec.Lib.lemma_uint32s_from_le_def_1 (UInt32.v i + 1) (reveal_sbytes (Seq.slice (as_seq h0 input) 0 (4 * v i + 4)));
    Seq.lemma_eq_intro (Seq.slice (as_seq h0 input) 0 (4 * v i + 4))
                       (Seq.append (Seq.slice (as_seq h0 input) 0 (4 * v i)) (as_seq h (Buffer.sub input (4ul *^ i) (4ul))));
    Seq.lemma_eq_intro (as_seq h0 (Buffer.sub input (4ul*^i) (4ul)))
                       (Seq.slice (as_seq h0 input) (4 * v i) (4 * v i + 4));
    Seq.lemma_eq_intro (Seq.slice (as_seq h0 input) (4 * v i) (4 * v i + 4))
                       (Seq.slice (Seq.slice (as_seq h0 input) 0 (4 * v i + 4)) (4 * v i) (4 * v i + 4));
    Seq.lemma_eq_intro (Seq.slice (as_seq h0 input) 0 (4 * v i))
                       (Seq.slice (Seq.slice (as_seq h0 input) 0 (4 * v i + 4)) 0 (4 * v i));
    Seq.lemma_eq_intro (Seq.slice (as_seq h' output) 0 (v i+1))
                       (Seq.snoc (Seq.slice (as_seq h output) 0 (v i)) inputi);
    Seq.lemma_eq_intro (reveal_h32s (Seq.slice (as_seq h' output) 0 (v i + 1)))
                       (Spec.Lib.uint32s_from_le (v i + 1) (reveal_sbytes (Seq.slice (as_seq h0 input) 0 (4 * (v i + 1)))))
  in
  Spec.Lib.lemma_uint32s_from_le_def_0 0 (reveal_sbytes (Seq.slice (as_seq h0 input) 0 0));
  Seq.lemma_eq_intro (Seq.slice (as_seq h0 output) 0 0) Seq.createEmpty;
  C.Loops.for 0ul len inv f';
  let h = ST.get() in
  Seq.lemma_eq_intro (Seq.slice (as_seq h output) 0 (UInt32.v len)) (as_seq h output);
  Seq.lemma_eq_intro (Seq.slice (as_seq h0 input) 0 (4 * UInt32.v len)) (as_seq h0 input)


#reset-options " --max_fuel 0 --z3rlimit 100"

val uint32s_to_le_bytes:
  output:uint8_p ->
  input:buffer H32.t{disjoint output input} ->
  len:U32.t{length input = U32.v len /\ 4 * U32.v len = length output} ->
  Stack unit
    (requires (fun h -> live h output /\ live h input))
    (ensures  (fun h0 _ h1 -> live h1 output /\ live h0 input /\ modifies_1 output h0 h1 /\
      (let o = reveal_sbytes (as_seq h1 output) in
       let i = reveal_h32s (as_seq h0 input) in
       o == Spec.Lib.uint32s_to_le (U32.v len) i)))
let rec uint32s_to_le_bytes output input len =
  let h0 = ST.get() in
  let inv (h1: mem) (i: nat): Type0 =
    live h1 output /\ modifies_1 output h0 h1 /\ 0 <= i /\ i <= UInt32.v len
    /\ reveal_sbytes (Seq.slice (as_seq h1 output) 0 (4 * i)) == Spec.Lib.uint32s_to_le i (reveal_h32s (Seq.slice (as_seq h0 input) 0 (i)))
  in
  let f' (i:UInt32.t{ FStar.UInt32.( 0 <= v i /\ v i < v len ) }): Stack unit
    (requires (fun h -> inv h (UInt32.v i)))
    (ensures (fun h_1 _ h_2 -> FStar.UInt32.(inv h_2 (v i + 1))))
  = let h = ST.get() in
    let open FStar.UInt32 in
    assert(as_seq h input == as_seq h0 input);
    let hd = input.(i) in
    hstore32_le (Buffer.sub output (4ul *^ i) 4ul) hd;
    let h' = ST.get() in
    Seq.lemma_eq_intro (as_seq h' (Buffer.sub output 0ul (4ul *^ i)))
                       (Seq.slice (as_seq h' output) 0 (4 * v i));
    Seq.lemma_eq_intro (as_seq h (Buffer.sub output 0ul (4ul *^ i)))
                       (Seq.slice (as_seq h output) 0 (4 * v i));
    no_upd_lemma_1 h h' (Buffer.sub output (4ul *^ i) 4ul) (Buffer.sub output 0ul (4ul *^ i));
    Seq.lemma_eq_intro (as_seq h' (Buffer.sub output (4ul*^ i) (4ul)))
                       (Seq.slice (as_seq h' output) (4 * v i) (4 * v i + 4));
    Seq.lemma_eq_intro (Seq.slice (as_seq h' output) (4 * v i) (4 * v i + 4))
                       (Seq.slice (Seq.slice (as_seq h' output) 0 (4 * v i + 4)) (4 * v i) (4 * v i + 4));
    Seq.lemma_eq_intro (Seq.slice (as_seq h' output) (4 * v i) (4 * v i + 4))
                       (Seq.slice (Seq.slice (as_seq h' output) 0 (4 * v i + 4)) (4 * v i) (4 * v i + 4));
    Seq.lemma_eq_intro (Seq.slice (as_seq h' output) 0 (4 * v i + 4))
                       (Seq.append (Seq.slice (Seq.slice (as_seq h' output) 0 (4 * v i + 4)) 0 (4 * v i))
                                   (Seq.slice (Seq.slice (as_seq h' output) 0 (4 * v i + 4)) (4 * v i) (4 * v i + 4)));
    Spec.Lib.lemma_uint32s_to_le_def_1 (UInt32.v i + 1) (reveal_h32s (Seq.slice (as_seq h0 input) 0 (v i + 1)));
    Seq.lemma_eq_intro (Seq.slice (as_seq h0 input) 0 (v i))
                       (Seq.slice (Seq.slice (as_seq h0 input) 0 (v i + 1)) 0 (v i));
    FStar.Endianness.lemma_little_endian_inj (Seq.slice (reveal_sbytes (as_seq h' output)) (4 * v i) (4 * v i + 4))
                                             (Spec.Lib.uint32_to_le (h32_to_u32 hd));
    Seq.lemma_eq_intro (reveal_sbytes (Seq.slice (as_seq h' output) 0 (4 * v i + 4)))
                       (Spec.Lib.uint32s_to_le (v i + 1) (reveal_h32s (Seq.slice (as_seq h0 input) 0 (v i + 1))))
  in
  Spec.Lib.lemma_uint32s_to_le_def_0 0 (reveal_h32s (Seq.slice (as_seq h0 input) 0 0));
  Seq.lemma_eq_intro (Seq.slice (as_seq h0 output) 0 0) Seq.createEmpty;
  C.Loops.for 0ul len inv f';
  let h = ST.get() in
  Seq.lemma_eq_intro (Seq.slice (as_seq h output) 0 (4 * UInt32.v len)) (as_seq h output);
  Seq.lemma_eq_intro (Seq.slice (as_seq h0 input) 0 (UInt32.v len)) (as_seq h0 input)
