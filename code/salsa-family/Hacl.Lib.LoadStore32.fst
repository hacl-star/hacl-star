module Hacl.Lib.LoadStore32

open FStar.Mul
open FStar.HyperStack
open FStar.ST
open FStar.Buffer
open Hacl.UInt32
open Hacl.Spec.Endianness
open Hacl.Endianness

module U32 = FStar.UInt32
module H32 =  Hacl.UInt32

let uint8_p = b:buffer Hacl.UInt8.t

#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 100"

private val lemma_uint32s_from_le_bytes: h:mem -> output:buffer H32.t{live h output} ->
  h':mem -> input:uint8_p{live h' input} ->
  len:U32.t{length output = U32.v len /\ 4 * U32.v len = length input /\ U32.v len > 0} ->
  Lemma
    (requires (H32.v (Seq.index (as_seq h output) 0) =
        U32.v (Spec.Lib.uint32_from_le (reveal_sbytes (as_seq h' (Buffer.sub input 0ul 4ul))))
      /\ reveal_h32s (as_seq h (Buffer.offset output 1ul)) == 
        Spec.Lib.uint32s_from_le (UInt32.v len - 1) (reveal_sbytes (as_seq h' (Buffer.offset input 4ul)))))
    (ensures (reveal_h32s (as_seq h output)
      == Spec.Lib.uint32s_from_le (U32.v len) (reveal_sbytes ((as_seq h' input)))))
let lemma_uint32s_from_le_bytes h output h' input len =
  let i' = reveal_sbytes (as_seq h' input) in
  Spec.Lib.lemma_uint32s_from_le_def_1 (U32.v len) i';
  Seq.lemma_eq_intro (as_seq h' (Buffer.sub input 0ul 4ul)) (Seq.slice (as_seq h' input) 0 4);
  Seq.lemma_eq_intro (as_seq h' (Buffer.offset input 4ul)) (Seq.slice (as_seq h' input) 4 (length input));
  Seq.lemma_eq_intro (as_seq h (Buffer.offset output 1ul)) (Seq.slice (as_seq h output) 1 (length output));
  cut (Seq.index (Spec.Lib.uint32s_from_le (U32.v len) i') 0 == Spec.Lib.uint32_from_le (Seq.slice i' 0 4));
  Seq.lemma_eq_intro (reveal_h32s (as_seq h output)) (Spec.Lib.uint32s_from_le (U32.v len) i')


private val lemma_uint32s_from_le_bytes': h:mem -> h':mem -> output:buffer H32.t{live h output /\ live h' output /\ length output > 0} -> Lemma
  (requires (modifies_1 (Buffer.offset output 1ul) h h'))
  (ensures (Seq.index (as_seq h output) 0 == Seq.index (as_seq h' output) 0))
private let lemma_uint32s_from_le_bytes' h h' output =
  let output' = Buffer.sub output 0ul 1ul in
  let output'' = Buffer.offset output 1ul in
  no_upd_lemma_1 h h' output'' output';
  Seq.lemma_eq_intro (Seq.slice (as_seq h output) 0 1) (as_seq h output');
  Seq.lemma_eq_intro (Seq.append (as_seq h' output') (as_seq h' output'')) (as_seq h' output)


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
  if U32.(len =^ 0ul) then (
    Spec.Lib.lemma_uint32s_from_le_def_0 0 (reveal_sbytes (as_seq h0 input));
    Seq.lemma_eq_intro (as_seq h0 output) Seq.createEmpty
  )
  else (
    cut (U32.v len > 0);
    output.(0ul) <- hload32_le (Buffer.sub input 0ul 4ul);
    let h = ST.get() in
    let output' = Buffer.offset output 1ul in
    let input'  = Buffer.offset input 4ul in
    uint32s_from_le_bytes output' input' U32.(len -^ 1ul);
    let h1 = ST.get() in
    lemma_uint32s_from_le_bytes' h h1 output;
    lemma_uint32s_from_le_bytes h1 output h0 input len
  )


private val lemma_uint32s_to_le_bytes: h:mem -> output:uint8_p{live h output} ->
  h':mem -> input:buffer H32.t{live h' input} ->
  len:U32.t{length input = U32.v len /\ 4 * U32.v len = length output /\ U32.v len > 0} ->
  Lemma
    (requires (Seq.slice (reveal_sbytes (as_seq h output)) 0 4 = Spec.Lib.uint32_to_le (Seq.index (reveal_h32s (as_seq h' input)) 0)
      /\ reveal_sbytes (as_seq h (Buffer.offset output 4ul)) == Spec.Lib.uint32s_to_le (UInt32.v len - 1) (reveal_h32s (as_seq h' (Buffer.offset input 1ul)))))
    (ensures (reveal_sbytes (as_seq h output) == Spec.Lib.uint32s_to_le (U32.v len) (reveal_h32s ((as_seq h' input)))))
let lemma_uint32s_to_le_bytes h output h' input len =
  let i' = reveal_h32s (as_seq h' input) in
  Spec.Lib.lemma_uint32s_to_le_def_1 (U32.v len) i';
  Seq.lemma_eq_intro (as_seq h (Buffer.sub output 0ul 4ul)) (Seq.slice (as_seq h output) 0 4);
  Seq.lemma_eq_intro (as_seq h (Buffer.offset output 4ul)) (Seq.slice (as_seq h output) 4 (length output));
  Seq.lemma_eq_intro (as_seq h' (Buffer.offset input 1ul)) (Seq.slice (as_seq h' input) 1 (length input));
  Seq.lemma_eq_intro (Seq.slice (Spec.Lib.uint32s_to_le (U32.v len) i') 0 4)
                     (Spec.Lib.uint32_to_le (Seq.index i' 0));
  Seq.lemma_eq_intro (reveal_sbytes (as_seq h output)) (Spec.Lib.uint32s_to_le (U32.v len) i')


private val lemma_uint32s_to_le_bytes': h:mem -> h':mem -> output:uint8_p{live h output /\ live h' output /\ length output >= 4} -> Lemma
  (requires (modifies_1 (Buffer.offset output 4ul) h h'))
  (ensures (Seq.slice (as_seq h output) 0 4 == Seq.slice (as_seq h' output) 0 4))
private let lemma_uint32s_to_le_bytes' h h' output =
  let output' = Buffer.sub output 0ul 4ul in
  let output'' = Buffer.offset output 4ul in
  no_upd_lemma_1 h h' output'' output';
  Seq.lemma_eq_intro (Seq.slice (as_seq h output) 0 4) (as_seq h output')


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
  if U32.(len =^ 0ul) then (
    Spec.Lib.lemma_uint32s_to_le_def_0 0 (reveal_h32s (as_seq h0 input));
    Seq.lemma_eq_intro (as_seq h0 output) Seq.createEmpty
  )
  else (
    cut (U32.v len > 0);
    let hd = input.(0ul) in
    hstore32_le (Buffer.sub output 0ul 4ul) hd;
    let h = ST.get() in
    FStar.Endianness.lemma_little_endian_inj (Seq.slice (reveal_sbytes (as_seq h output)) 0 4)
                                             (Spec.Lib.uint32_to_le (h32_to_u32 hd));
    cut (Seq.slice (reveal_sbytes (as_seq h output)) 0 4 == Spec.Lib.uint32_to_le (h32_to_u32 hd));
    let output' = Buffer.offset output 4ul in
    let input'  = Buffer.offset input 1ul in
    uint32s_to_le_bytes output' input' U32.(len -^ 1ul);
    let h1 = ST.get() in
    lemma_uint32s_to_le_bytes' h h1 output;
    lemma_uint32s_to_le_bytes h1 output h0 input len
  )
