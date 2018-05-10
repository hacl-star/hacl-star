module Hacl.Impl.SHA512.Ed25519_1

open FStar.HyperStack.All

module ST = FStar.HyperStack.ST

open FStar.Mul
open FStar.UInt32
open FStar.HyperStack
open FStar.Seq
open FStar.Buffer

open Hacl.Impl.SHA2_512

#reset-options "--max_fuel 0 --z3rlimit 20"

let hint8_p = buffer Hacl.UInt8.t
let op_String_Access h b = Hacl.Spec.Endianness.reveal_sbytes (as_seq h b)


[@ Substitute]
val copy_bytes:
  output:hint8_p ->
  input:hint8_p{disjoint input output} ->
  len:UInt32.t{length output = UInt32.v len /\ length input = UInt32.v len} ->
  Stack unit
    (requires (fun h -> live h output /\ live h input))
    (ensures (fun h0 _ h1 -> live h0 input /\ live h1 input /\ live h1 output /\ modifies_1 output h0 h1
      /\ as_seq h1 output == as_seq h0 input))

#reset-options "--max_fuel 0 --z3rlimit 200"

let copy_bytes output input len =
  let h0 = ST.get() in
  blit input 0ul output 0ul len;
  let h1 = ST.get() in
  Seq.lemma_eq_intro (as_seq h0 input) (Seq.slice (as_seq h0 input) 0 (UInt32.v len));
  Seq.lemma_eq_intro (as_seq h1 output) (Seq.slice (as_seq h1 output) 0 (UInt32.v len))

#reset-options "--max_fuel 0 --z3rlimit 20"

val concat_2:
  out:hint8_p ->
  pre:hint8_p{length pre = 32 /\ disjoint pre out} ->
  msg:hint8_p{disjoint msg out} ->
  len:t{v len = length msg /\ length out = 32 + length msg} ->
  Stack unit
    (requires (fun h -> live h out /\ live h pre /\ live h msg))
    (ensures (fun h0 _ h1 -> live h1 out /\ live h0 pre /\ live h0 msg /\ modifies_1 out h0 h1 /\
      as_seq h1 out == (as_seq h0 pre @| as_seq h0 msg)))

#reset-options "--max_fuel 0 --z3rlimit 200"

let concat_2 out pre msg len =
  let h0 = ST.get() in
  copy_bytes (sub out 0ul 32ul) pre 32ul;
  let h1 = ST.get() in
  no_upd_lemma_1 h0 h1 out msg;
  copy_bytes (sub out 32ul len) msg len;
  let h2 = ST.get() in
  no_upd_lemma_1 h1 h2 (sub out 32ul len) (sub out 0ul 32ul);
  lemma_eq_intro (as_seq h2 out) FStar.Seq.(as_seq h0 pre @| as_seq h0 msg)

#reset-options "--max_fuel 0 --z3rlimit 20"

private
val lemma_append:
  h:HyperStack.mem ->
  buf:hint8_p{live h buf} ->
  len1:UInt32.t ->
  len2:UInt32.t ->
  len3:UInt32.t{UInt32.v len3 + UInt32.v len2 + UInt32.v len1 = length buf} ->
  Lemma (as_seq h buf == FStar.Seq.(as_seq h (Buffer.sub buf 0ul len1) @| as_seq h (Buffer.sub buf len1 len2) @| (as_seq h (Buffer.sub buf FStar.UInt32.(len1 +^ len2) len3))))

#reset-options "--max_fuel 0 --z3rlimit 200"

let lemma_append h buf len1 len2 len3 =
  let open FStar.UInt32 in
  let b = as_seq h buf in
  Seq.lemma_eq_intro (as_seq h (Buffer.sub buf 0ul len1)) (Seq.slice b 0 (v len1));
  Seq.lemma_eq_intro (as_seq h (Buffer.sub buf len1 len2)) (Seq.slice b (v len1) (v len1 + v len2));
  Seq.lemma_eq_intro (as_seq h (Buffer.sub buf FStar.UInt32.(len1 +^ len2) len3)) (Seq.slice b (v len1 + v len2) (v len1 + v len2 + v len3));
  Seq.lemma_eq_intro b FStar.Seq.(slice b 0 (v len1) @| slice b (v len1) (v len1 + v len2) @| slice b (v len1 + v len2) (v len1 + v len2 + v len3))

#reset-options "--max_fuel 0 --z3rlimit 20"

val concat_3:
  out:hint8_p ->
  pre:hint8_p{length pre = 32 /\ disjoint pre out} ->
  pre2:hint8_p{length pre2 = 32 /\ disjoint pre2 out} ->
  msg:hint8_p{disjoint msg out} ->
  len:t{v len = length msg /\ length out = 64 + length msg} ->
  Stack unit
    (requires (fun h -> live h out /\ live h pre /\ live h pre2 /\ live h msg))
    (ensures (fun h0 _ h1 -> live h1 out /\ live h0 pre /\ live h0 pre2 /\ live h0 msg /\
      modifies_1 out h0 h1 /\ as_seq h1 out == (as_seq h0 pre @| as_seq h0 pre2 @| as_seq h0 msg)))

#reset-options "--max_fuel 0 --z3rlimit 200"

let concat_3 out pre pre2 msg len =
  let h0 = ST.get() in
  copy_bytes (sub out 0ul 32ul) pre 32ul;
  let h1 = ST.get() in
  no_upd_lemma_1 h0 h1 out msg;
  no_upd_lemma_1 h0 h1 out pre2;
  copy_bytes (sub out 32ul 32ul) pre2 32ul;
  let h2 = ST.get() in
  no_upd_lemma_1 h1 h2 (sub out 32ul 32ul) (sub out 0ul 32ul);
  no_upd_lemma_1 h1 h2 (sub out 32ul 32ul) msg;
  copy_bytes (sub out 64ul len) msg len;
  let h3 = ST.get() in
  no_upd_lemma_1 h2 h3 (sub out 64ul len) (sub out 0ul 32ul);
  no_upd_lemma_1 h2 h3 (sub out 64ul len) (sub out 32ul 32ul);
  lemma_append h3 out 32ul 32ul len;
  lemma_eq_intro (as_seq h3 out) FStar.Seq.(as_seq h0 pre @| as_seq h0 pre2 @| as_seq h0 msg)

#reset-options "--max_fuel 0 --z3rlimit 20"

val sha512_pre_msg_1:
  hash:hint8_p{length hash = 64} ->
  prefix:hint8_p{length prefix = 32 /\ disjoint prefix hash} ->
  input:hint8_p{disjoint input hash} ->
  len:UInt32.t{UInt32.v len = length input /\ length input <= 96} ->
  Stack unit
    (requires (fun h -> live h hash /\ live h prefix /\ live h input))
    (ensures (fun h0 _ h1 -> live h0 hash /\ live h0 prefix /\ live h0 input /\
      live h1 hash /\ live h1 prefix /\ live h1 input /\ modifies_1 hash h0 h1 /\
      h1.[hash] == Spec.SHA2_512.hash FStar.Seq.(h0.[prefix] @| h0.[input])))

#reset-options "--max_fuel 0 --z3rlimit 200"

let sha512_pre_msg_1 h prefix input len =
  assert_norm(pow2 32 = 0x100000000);
  assert_norm(pow2 125 = 42535295865117307932921825928971026432);
  push_frame();
  let h0 = ST.get() in
  let block = create (Hacl.Cast.uint8_to_sint8 0uy) 128ul in
  let block' = sub block 0ul (32ul +^ len) in
  let h1 = ST.get() in
  no_upd_lemma_0 h0 h1 prefix;
  no_upd_lemma_0 h0 h1 input;
  concat_2 block' prefix input len;
  let h2 = ST.get() in
  hash h block' (len +^ 32ul);
  let h3 = ST.get() in
  pop_frame()

#reset-options "--max_fuel 0 --z3rlimit 20"

val sha512_pre_pre2_msg_1:
  hash:hint8_p{length hash = 64} ->
  prefix:hint8_p{length prefix = 32 /\ disjoint prefix hash} ->
  prefix2:hint8_p{length prefix2 = 32 /\ disjoint prefix2 hash} ->
  input:hint8_p{disjoint input hash} ->
  len:UInt32.t{UInt32.v len = length input /\ length input <= 64} ->
  Stack unit
    (requires (fun h -> live h hash /\ live h prefix /\ live h input /\ live h prefix2))
    (ensures (fun h0 _ h1 -> live h0 hash /\ live h0 prefix /\ live h0 input /\ live h0 prefix2 /\
      live h1 hash /\ live h1 prefix /\ live h1 prefix2 /\ live h1 input /\ modifies_1 hash h0 h1 /\
      h1.[hash] == Spec.SHA2_512.hash (h0.[prefix] @| h0.[prefix2] @| h0.[input])))

#reset-options "--max_fuel 0 --z3rlimit 200"

let sha512_pre_pre2_msg_1 h prefix prefix2 input len =
 assert_norm(pow2 32 = 0x100000000);
  assert_norm(pow2 125 = 42535295865117307932921825928971026432);
  push_frame();
  let h0 = ST.get() in
  let block = create (Hacl.Cast.uint8_to_sint8 0uy) 128ul in
  let block' = sub block 0ul (64ul +^ len) in
  let h1 = ST.get() in
  no_upd_lemma_0 h0 h1 prefix;
  no_upd_lemma_0 h0 h1 prefix2;
  no_upd_lemma_0 h0 h1 input;
  concat_3 block' prefix prefix2 input len;
  let h2 = ST.get() in
  hash h block' (len +^ 64ul);
  let h3 = ST.get() in
  pop_frame()
