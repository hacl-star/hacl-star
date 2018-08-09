module Hacl.Impl.SHA512.Ed25519_3

open FStar.HyperStack.All

module ST = FStar.HyperStack.ST


open FStar.Mul
open FStar.UInt32
open FStar.HyperStack
open FStar.Seq
open FStar.Buffer

open Hacl.Impl.SHA2_512
open Hacl.Impl.SHA512.Ed25519_1
open Hacl.Impl.SHA512.Ed25519_2

let op_String_Access h (b:buffer Hacl.UInt8.t{live h b}) = Hacl.Spec.Endianness.reveal_sbytes (as_seq h b)

#reset-options "--max_fuel 0 --z3rlimit 20"


val lemma_append_1:
  #a:Type ->
  pre:seq a ->
  input:seq a{Seq.length input > 96} ->
  Lemma (pre @| input == (pre @| slice input 0 96) @| slice input 96 (Seq.length input))
let lemma_append_1 #a pre input =
  lemma_eq_intro (slice input 0 96 @| slice input 96 (Seq.length input)) input;
  lemma_eq_intro (slice input 0 96 @| slice input 96 (Seq.length input)) input;
  lemma_eq_intro ((pre @| slice input 0 96) @| slice input 96 (Seq.length input))
                 (pre @| (slice input 0 96) @| slice input 96 (Seq.length input))


val lemma_append_2:
  #a:Type ->
  pre:seq a ->
  pre2:seq a ->
  input:seq a{Seq.length input > 64} ->
  Lemma (pre @| pre2 @| input == (pre @| pre2 @| slice input 0 64) @| slice input 64 (Seq.length input))

#reset-options "--max_fuel 0 --z3rlimit 200"

let lemma_append_2 #a pre pre2 input =
  lemma_eq_intro (slice input 0 64 @| slice input 64 (Seq.length input)) input;
  lemma_eq_intro (slice input 0 64 @| slice input 64 (Seq.length input)) input;
  lemma_eq_intro ((pre @| pre2 @| slice input 0 64) @| slice input 64 (Seq.length input))
                 (pre @| pre2 @| (slice input 0 64) @| slice input 64 (Seq.length input))

#reset-options "--max_fuel 0 --z3rlimit 20"

val sha512_pre_msg_2:
  hash:hint8_p{length hash = 64} ->
  prefix:hint8_p{length prefix = 32 /\ disjoint prefix hash} ->
  input:hint8_p{disjoint input hash} ->
  len:UInt32.t{v len = length input /\ length input > 96} ->
  Stack unit
    (requires (fun h -> live h hash /\ live h prefix /\ live h input))
    (ensures (fun h0 _ h1 -> live h0 hash /\ live h0 prefix /\ live h0 input /\
      live h1 hash /\ live h1 prefix /\ live h1 input /\ modifies_1 hash h0 h1 /\
      h1.[hash] == Spec.SHA2_512.hash FStar.Seq.(h0.[prefix] @| h0.[input])))

#reset-options "--max_fuel 0 --z3rlimit 200"

let sha512_pre_msg_2 h prefix input len =
  let input1 = Buffer.sub input 0ul 96ul in
  let input2 = Buffer.sub input 96ul (len -^ 96ul) in
  let h0 = ST.get() in
  lemma_eq_intro (as_seq h0 input1) (slice (as_seq h0 input) 0 96);
  lemma_eq_intro (as_seq h0 input2) (slice (as_seq h0 input) 96 (v len));
  push_frame();
  let h1 = ST.get() in
  let block = create (Hacl.Cast.uint8_to_sint8 0uy) 128ul in
  let h2 = ST.get() in
  no_upd_lemma_0 h1 h2 input1;
  no_upd_lemma_0 h1 h2 input2;
  no_upd_lemma_0 h1 h2 prefix;
  concat_2 block prefix input1 96ul;
  let h3 = ST.get() in
  no_upd_lemma_1 h2 h3 block input2;
  hash_block_and_rest h block input2 (len -^ 96ul);
  let h4 = ST.get() in
  lemma_append_1 (as_seq h0 prefix) (as_seq h0 input);
  pop_frame()


#reset-options "--max_fuel 0 --z3rlimit 20"

val sha512_pre_msg:
  hash:hint8_p{length hash = 64} ->
  prefix:hint8_p{length prefix = 32 /\ disjoint prefix hash} ->
  input:hint8_p{disjoint input hash} ->
  len:UInt32.t{UInt32.v len = length input /\ length input < pow2 32 - 32} ->
  Stack unit
    (requires (fun h -> live h hash /\ live h prefix /\ live h input))
    (ensures (fun h0 _ h1 -> live h0 hash /\ live h0 prefix /\ live h0 input /\
      live h1 hash /\ live h1 prefix /\ live h1 input /\ modifies_1 hash h0 h1 /\
      h1.[hash] == Spec.SHA2_512.hash FStar.Seq.(h0.[prefix] @| h0.[input])))


let sha512_pre_msg h prefix input len =
  if len <=^ 96ul then sha512_pre_msg_1 h prefix input len
  else sha512_pre_msg_2 h prefix input len


val sha512_pre_pre2_msg_2:
  hash:hint8_p{length hash = 64} ->
  prefix:hint8_p{length prefix = 32 /\ disjoint prefix hash} ->
  prefix2:hint8_p{length prefix2 = 32 /\ disjoint prefix2 hash} ->
  input:hint8_p{disjoint input hash} ->
  len:UInt32.t{v len = length input /\ length input > 64} ->
  Stack unit
    (requires (fun h -> live h hash /\ live h prefix /\ live h prefix2 /\ live h input))
    (ensures (fun h0 _ h1 -> live h0 hash /\ live h0 prefix /\ live h0 prefix2 /\ live h0 input /\
      live h1 hash /\ live h1 prefix /\ live h1 prefix2 /\ live h1 input /\ modifies_1 hash h0 h1 /\
      h1.[hash] == Spec.SHA2_512.hash FStar.Seq.(h0.[prefix] @| h0.[prefix2] @| h0.[input])))


#reset-options "--max_fuel 0 --z3rlimit 200"

let sha512_pre_pre2_msg_2 h prefix prefix2 input len =
  let input1 = Buffer.sub input 0ul 64ul in
  let input2 = Buffer.sub input 64ul (len -^ 64ul) in
  let h0 = ST.get() in
  lemma_eq_intro (as_seq h0 input1) (slice (as_seq h0 input) 0 64);
  lemma_eq_intro (as_seq h0 input2) (slice (as_seq h0 input) 64 (v len));
  push_frame();
  let h1 = ST.get() in
  let block = create (Hacl.Cast.uint8_to_sint8 0uy) 128ul in
  let h2 = ST.get() in
  no_upd_lemma_0 h1 h2 prefix;
  no_upd_lemma_0 h1 h2 prefix2;
  no_upd_lemma_0 h1 h2 input1;
  no_upd_lemma_0 h1 h2 input2;
  no_upd_lemma_0 h1 h2 input;
  concat_3 block prefix prefix2 input1 64ul;
  let h3 = ST.get() in
  no_upd_lemma_1 h2 h3 block input2;
  lemma_append_2 (as_seq h0 prefix) (as_seq h0 prefix2) (as_seq h0 input);
  hash_block_and_rest h block input2 (len -^ 64ul);
  let h4 = ST.get() in
  pop_frame()


#reset-options "--max_fuel 0 --z3rlimit 20"

val sha512_pre_pre2_msg:
  hash:hint8_p{length hash = 64} ->
  prefix:hint8_p{length prefix = 32 /\ disjoint prefix hash} ->
  prefix2:hint8_p{length prefix2 = 32 /\ disjoint prefix2 hash} ->
  input:hint8_p{disjoint input hash} ->
  len:UInt32.t{UInt32.v len = length input /\ length input < pow2 32 - 64} ->
  Stack unit
    (requires (fun h -> live h hash /\ live h prefix /\ live h prefix2 /\ live h input))
    (ensures (fun h0 _ h1 -> live h0 hash /\ live h0 prefix /\ live h0 input /\ live h0 prefix2 /\
      live h1 hash /\ live h1 prefix /\ live h1 input /\ modifies_1 hash h0 h1 /\
      h1.[hash] == Spec.SHA2_512.hash (h0.[prefix] @| h0.[prefix2] @| h0.[input])))

#reset-options "--max_fuel 0 --z3rlimit 200"

let sha512_pre_pre2_msg h prefix prefix2 input len =
  if len <=^ 64ul then sha512_pre_pre2_msg_1 h prefix prefix2 input len
  else sha512_pre_pre2_msg_2 h prefix prefix2 input len
