module Hacl.Hash.Lib.LoadStore

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
module H64 =  Hacl.UInt64

let uint8_p = b:buffer Hacl.UInt8.t

#reset-options "--max_fuel 0 --z3rlimit 100"


val uint32s_from_be_bytes:
  output:buffer H32.t ->
  input:uint8_p{disjoint output input} ->
  len:U32.t{length output = U32.v len /\ 4 * U32.v len = length input} ->
  Stack unit
    (requires (fun h -> live h output /\ live h input))
    (ensures  (fun h0 _ h1 -> live h1 output /\ live h0 input /\ modifies_1 output h0 h1 /\
      (let o = reveal_h32s (as_seq h1 output) in
       let i = reveal_sbytes (as_seq h0 input) in
       o == Spec.Lib.uint32s_from_be (U32.v len) i)))
let uint32s_from_be_bytes output input len =
  let h0 = ST.get() in
  let inv (h1: mem) (i: nat): Type0 =
    live h1 output /\ modifies_1 output h0 h1 /\ 0 <= i /\ i <= UInt32.v len
    /\ Seq.slice (reveal_h32s (as_seq h1 output)) 0 i == Spec.Lib.uint32s_from_be i (reveal_sbytes (Seq.slice (as_seq h0 input) 0 (4 * i)))
  in
  let f' (i:UInt32.t{ FStar.UInt32.( 0 <= v i /\ v i < v len ) }): Stack unit
    (requires (fun h -> inv h (UInt32.v i)))
    (ensures (fun h_1 _ h_2 -> FStar.UInt32.(inv h_2 (v i + 1))))
  = let h = ST.get() in
    let open FStar.UInt32 in
    assert(as_seq h input == as_seq h0 input);
    let inputi = hload32_be (Buffer.sub input (4ul*^i) (4ul)) in
    output.(i) <- inputi;
    let h' = ST.get() in
    Spec.Lib.lemma_uint32s_from_be_def_1 (UInt32.v i + 1) (reveal_sbytes (Seq.slice (as_seq h0 input) 0 (4 * v i + 4)));
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
                       (Spec.Lib.uint32s_from_be (v i + 1) (reveal_sbytes (Seq.slice (as_seq h0 input) 0 (4 * (v i + 1)))))
  in
  Spec.Lib.lemma_uint32s_from_be_def_0 0 (reveal_sbytes (Seq.slice (as_seq h0 input) 0 0));
  Seq.lemma_eq_intro (Seq.slice (as_seq h0 output) 0 0) Seq.createEmpty;
  C.Loops.for 0ul len inv f';
  let h = ST.get() in
  Seq.lemma_eq_intro (Seq.slice (as_seq h output) 0 (UInt32.v len)) (as_seq h output);
  Seq.lemma_eq_intro (Seq.slice (as_seq h0 input) 0 (4 * UInt32.v len)) (as_seq h0 input)


#reset-options " --max_fuel 0 --z3rlimit 100"

val uint32s_to_be_bytes:
  output:uint8_p ->
  input:buffer H32.t{disjoint output input} ->
  len:U32.t{length input = U32.v len /\ 4 * U32.v len = length output} ->
  Stack unit
    (requires (fun h -> live h output /\ live h input))
    (ensures  (fun h0 _ h1 -> live h1 output /\ live h0 input /\ modifies_1 output h0 h1 /\
      (let o = reveal_sbytes (as_seq h1 output) in
       let i = reveal_h32s (as_seq h0 input) in
       o == Spec.Lib.uint32s_to_be (U32.v len) i)))
let uint32s_to_be_bytes output input len =
  let h0 = ST.get() in
  let inv (h1: mem) (i: nat): Type0 =
    live h1 output /\ modifies_1 output h0 h1 /\ 0 <= i /\ i <= UInt32.v len
    /\ reveal_sbytes (Seq.slice (as_seq h1 output) 0 (4 * i)) == Spec.Lib.uint32s_to_be i (reveal_h32s (Seq.slice (as_seq h0 input) 0 (i)))
  in
  let f' (i:UInt32.t{ FStar.UInt32.( 0 <= v i /\ v i < v len ) }): Stack unit
    (requires (fun h -> inv h (UInt32.v i)))
    (ensures (fun h_1 _ h_2 -> FStar.UInt32.(inv h_2 (v i + 1))))
  = let h = ST.get() in
    let open FStar.UInt32 in
    assert(as_seq h input == as_seq h0 input);
    let hd = input.(i) in
    hstore32_be (Buffer.sub output (4ul *^ i) 4ul) hd;
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
    Spec.Lib.lemma_uint32s_to_be_def_1 (UInt32.v i + 1) (reveal_h32s (Seq.slice (as_seq h0 input) 0 (v i + 1)));
    Seq.lemma_eq_intro (Seq.slice (as_seq h0 input) 0 (v i))
                       (Seq.slice (Seq.slice (as_seq h0 input) 0 (v i + 1)) 0 (v i));
    FStar.Endianness.lemma_big_endian_inj (Seq.slice (reveal_sbytes (as_seq h' output)) (4 * v i) (4 * v i + 4))
                                             (Spec.Lib.uint32_to_be (h32_to_u32 hd));
    Seq.lemma_eq_intro (reveal_sbytes (Seq.slice (as_seq h' output) 0 (4 * v i + 4)))
                       (Spec.Lib.uint32s_to_be (v i + 1) (reveal_h32s (Seq.slice (as_seq h0 input) 0 (v i + 1))))
  in
  Spec.Lib.lemma_uint32s_to_be_def_0 0 (reveal_h32s (Seq.slice (as_seq h0 input) 0 0));
  Seq.lemma_eq_intro (Seq.slice (as_seq h0 output) 0 0) Seq.createEmpty;
  C.Loops.for 0ul len inv f';
  let h = ST.get() in
  Seq.lemma_eq_intro (Seq.slice (as_seq h output) 0 (4 * UInt32.v len)) (as_seq h output);
  Seq.lemma_eq_intro (Seq.slice (as_seq h0 input) 0 (UInt32.v len)) (as_seq h0 input)

#reset-options " --max_fuel 0 --z3rlimit 100"


val uint64s_from_be_bytes:
  output:buffer H64.t ->
  input:uint8_p{disjoint output input} ->
  len:U32.t{length output = U32.v len /\ 8 * U32.v len = length input} ->
  Stack unit
    (requires (fun h -> live h output /\ live h input))
    (ensures  (fun h0 _ h1 -> live h1 output /\ live h0 input /\ modifies_1 output h0 h1 /\
      (let o = reveal_h64s (as_seq h1 output) in
       let i = reveal_sbytes (as_seq h0 input) in
       o == Spec.Lib.uint64s_from_be (U32.v len) i)))
let uint64s_from_be_bytes output input len =
  let h0 = ST.get() in
  let inv (h1: mem) (i: nat): Type0 =
    live h1 output /\ modifies_1 output h0 h1 /\ 0 <= i /\ i <= UInt32.v len
    /\ Seq.slice (reveal_h64s (as_seq h1 output)) 0 i == Spec.Lib.uint64s_from_be i (reveal_sbytes (Seq.slice (as_seq h0 input) 0 (8 * i)))
  in
  let f' (i:UInt32.t{ FStar.UInt32.( 0 <= v i /\ v i < v len ) }): Stack unit
    (requires (fun h -> inv h (UInt32.v i)))
    (ensures (fun h_1 _ h_2 -> FStar.UInt32.(inv h_2 (v i + 1))))
  = let h = ST.get() in
    let open FStar.UInt32 in
    assert(as_seq h input == as_seq h0 input);
    let inputi = hload64_be (Buffer.sub input (8ul*^i) (8ul)) in
    output.(i) <- inputi;
    let h' = ST.get() in
    Spec.Lib.lemma_uint64s_from_be_def_1 (UInt32.v i + 1) (reveal_sbytes (Seq.slice (as_seq h0 input) 0 (8 * v i + 8)));
    Seq.lemma_eq_intro (Seq.slice (as_seq h0 input) 0 (8 * v i + 8))
                       (Seq.append (Seq.slice (as_seq h0 input) 0 (8 * v i)) (as_seq h (Buffer.sub input (8ul *^ i) (8ul))));
    Seq.lemma_eq_intro (as_seq h0 (Buffer.sub input (8ul*^i) (8ul)))
                       (Seq.slice (as_seq h0 input) (8 * v i) (8 * v i + 8));
    Seq.lemma_eq_intro (Seq.slice (as_seq h0 input) (8 * v i) (8 * v i + 8))
                       (Seq.slice (Seq.slice (as_seq h0 input) 0 (8 * v i + 8)) (8 * v i) (8 * v i + 8));
    Seq.lemma_eq_intro (Seq.slice (as_seq h0 input) 0 (8 * v i))
                       (Seq.slice (Seq.slice (as_seq h0 input) 0 (8 * v i + 8)) 0 (8 * v i));
    Seq.lemma_eq_intro (Seq.slice (as_seq h' output) 0 (v i+1))
                       (Seq.snoc (Seq.slice (as_seq h output) 0 (v i)) inputi);
    Seq.lemma_eq_intro (reveal_h64s (Seq.slice (as_seq h' output) 0 (v i + 1)))
                       (Spec.Lib.uint64s_from_be (v i + 1) (reveal_sbytes (Seq.slice (as_seq h0 input) 0 (8 * (v i + 1)))))
  in
  Spec.Lib.lemma_uint64s_from_be_def_0 0 (reveal_sbytes (Seq.slice (as_seq h0 input) 0 0));
  Seq.lemma_eq_intro (Seq.slice (as_seq h0 output) 0 0) Seq.createEmpty;
  C.Loops.for 0ul len inv f';
  let h = ST.get() in
  Seq.lemma_eq_intro (Seq.slice (as_seq h output) 0 (UInt32.v len)) (as_seq h output);
  Seq.lemma_eq_intro (Seq.slice (as_seq h0 input) 0 (8 * UInt32.v len)) (as_seq h0 input)

#reset-options " --max_fuel 0 --z3rlimit 100"

val uint64s_to_be_bytes:
  output:uint8_p ->
  input:buffer H64.t{disjoint output input} ->
  len:U32.t{length input = U32.v len /\ 8 * U32.v len = length output} ->
  Stack unit
    (requires (fun h -> live h output /\ live h input))
    (ensures  (fun h0 _ h1 -> live h1 output /\ live h0 input /\ modifies_1 output h0 h1 /\
      (let o = reveal_sbytes (as_seq h1 output) in
       let i = reveal_h64s (as_seq h0 input) in
       o == Spec.Lib.uint64s_to_be (U32.v len) i)))
let uint64s_to_be_bytes output input len =
  let h0 = ST.get() in
  let inv (h1: mem) (i: nat): Type0 =
    live h1 output /\ modifies_1 output h0 h1 /\ 0 <= i /\ i <= UInt32.v len
    /\ reveal_sbytes (Seq.slice (as_seq h1 output) 0 (8 * i)) == Spec.Lib.uint64s_to_be i (reveal_h64s (Seq.slice (as_seq h0 input) 0 (i)))
  in
  let f' (i:UInt32.t{ FStar.UInt32.( 0 <= v i /\ v i < v len ) }): Stack unit
    (requires (fun h -> inv h (UInt32.v i)))
    (ensures (fun h_1 _ h_2 -> FStar.UInt32.(inv h_2 (v i + 1))))
  = let h = ST.get() in
    let open FStar.UInt32 in
    assert(as_seq h input == as_seq h0 input);
    let hd = input.(i) in
    hstore64_be (Buffer.sub output (8ul *^ i) 8ul) hd;
    let h' = ST.get() in
    Seq.lemma_eq_intro (as_seq h' (Buffer.sub output 0ul (8ul *^ i)))
                       (Seq.slice (as_seq h' output) 0 (8 * v i));
    Seq.lemma_eq_intro (as_seq h (Buffer.sub output 0ul (8ul *^ i)))
                       (Seq.slice (as_seq h output) 0 (8 * v i));
    no_upd_lemma_1 h h' (Buffer.sub output (8ul *^ i) 8ul) (Buffer.sub output 0ul (8ul *^ i));
    Seq.lemma_eq_intro (as_seq h' (Buffer.sub output (8ul*^ i) (8ul)))
                       (Seq.slice (as_seq h' output) (8 * v i) (8 * v i + 8));
    Seq.lemma_eq_intro (Seq.slice (as_seq h' output) (8 * v i) (8 * v i + 8))
                       (Seq.slice (Seq.slice (as_seq h' output) 0 (8 * v i + 8)) (8 * v i) (8 * v i + 8));
    Seq.lemma_eq_intro (Seq.slice (as_seq h' output) (8 * v i) (8 * v i + 8))
                       (Seq.slice (Seq.slice (as_seq h' output) 0 (8 * v i + 8)) (8 * v i) (8 * v i + 8));
    Seq.lemma_eq_intro (Seq.slice (as_seq h' output) 0 (8 * v i + 8))
                       (Seq.append (Seq.slice (Seq.slice (as_seq h' output) 0 (8 * v i + 8)) 0 (8 * v i))
                                   (Seq.slice (Seq.slice (as_seq h' output) 0 (8 * v i + 8)) (8 * v i) (8 * v i + 8)));
    Spec.Lib.lemma_uint64s_to_be_def_1 (UInt32.v i + 1) (reveal_h64s (Seq.slice (as_seq h0 input) 0 (v i + 1)));
    Seq.lemma_eq_intro (Seq.slice (as_seq h0 input) 0 (v i))
                       (Seq.slice (Seq.slice (as_seq h0 input) 0 (v i + 1)) 0 (v i));
    FStar.Endianness.lemma_big_endian_inj (Seq.slice (reveal_sbytes (as_seq h' output)) (8 * v i) (8 * v i + 8))
                                             (Spec.Lib.uint64_to_be (h64_to_u64 hd));
    Seq.lemma_eq_intro (reveal_sbytes (Seq.slice (as_seq h' output) 0 (8 * v i + 8)))
                       (Spec.Lib.uint64s_to_be (v i + 1) (reveal_h64s (Seq.slice (as_seq h0 input) 0 (v i + 1))))
  in
  Spec.Lib.lemma_uint64s_to_be_def_0 0 (reveal_h64s (Seq.slice (as_seq h0 input) 0 0));
  Seq.lemma_eq_intro (Seq.slice (as_seq h0 output) 0 0) Seq.createEmpty;
  C.Loops.for 0ul len inv f';
  let h = ST.get() in
  Seq.lemma_eq_intro (Seq.slice (as_seq h output) 0 (8 * UInt32.v len)) (as_seq h output);
  Seq.lemma_eq_intro (Seq.slice (as_seq h0 input) 0 (UInt32.v len)) (as_seq h0 input)
