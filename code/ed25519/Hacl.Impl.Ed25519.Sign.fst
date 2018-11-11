module Hacl.Impl.Ed25519.Sign

module ST = FStar.HyperStack.ST

open FStar.HyperStack.All


open FStar.Mul
open FStar.Buffer
open FStar.UInt32

open Hacl.Impl.Ed25519.ExtPoint
open Hacl.Impl.Ed25519.Ladder.Step

let hint8_p = buffer Hacl.UInt8.t

inline_for_extraction
let op_String_Access (h:HyperStack.mem) (b:hint8_p{live h b}) =
  Hacl.Spec.Endianness.reveal_sbytes (as_seq h b)

open Hacl.Impl.Ed25519.Sign.Steps
open Hacl.Spec.Endianness

#reset-options "--max_fuel 0 --z3rlimit 20"

val lemma_modifies_3:
  h0:HyperStack.mem ->
  h1:HyperStack.mem ->
  h2:HyperStack.mem ->
  h3:HyperStack.mem ->
  h4:HyperStack.mem ->
  h5:HyperStack.mem ->
  h6:HyperStack.mem ->
  a:hint8_p -> b:hint8_p{disjoint a b} -> c:buffer Hacl.UInt64.t{disjoint b c /\ disjoint a c} ->
  Lemma (requires (live h0 a /\ live h0 b /\ live h0 c /\ modifies_1 b h0 h1 /\ modifies_1 c h1 h2 /\ modifies_1 b h2 h3 /\ modifies_1 c h3 h4 /\ modifies_2 b c h4 h5 /\ modifies_1 a h5 h6 /\ ST.equal_domains h0 h1 /\ ST.equal_domains h1 h2 /\ ST.equal_domains h2 h3 /\ ST.equal_domains h3 h4 /\ ST.equal_domains h4 h5 /\ ST.equal_domains h5 h6))
        (ensures (modifies_3 a b c h0 h6))

#reset-options "--max_fuel 0 --z3rlimit 200"

let lemma_modifies_3 h0 h1 h2 h3 h4 h5 h6 a b c =
  assert(modifies_2 b c h0 h2);
  assert(live h2 b /\ live h2 c);
  assert(modifies_2 b c h2 h4);
  assert(modifies_2 b c h0 h5);
  lemma_reveal_modifies_2 b c h0 h5;
  lemma_reveal_modifies_1 a h5 h6;
  lemma_intro_modifies_3 a b c h0 h6

#reset-options "--max_fuel 0 --z3rlimit 20"

inline_for_extraction
val append_to_sig:
  signature:hint8_p{length signature = 64} ->
  a:hint8_p{length a = 32 /\ disjoint a signature} ->
  b:hint8_p{length b = 32 /\ disjoint b signature} ->
  Stack unit
    (requires (fun h -> live h signature /\ live h a /\ live h b))
    (ensures (fun h0 _ h1 -> live h1 signature /\ live h0 a /\ live h0 b /\ modifies_1 signature h0 h1
      /\ as_seq h1 signature == FStar.Seq.(as_seq h0 a @| as_seq h0 b)))

#reset-options "--max_fuel 0 --z3rlimit 200"

let append_to_sig signature a b =
  let h0 = ST.get() in
  copy_bytes (Buffer.sub signature 0ul 32ul) a 32ul;
  let h1 = ST.get() in
  no_upd_lemma_1 h0 h1 signature b;
  copy_bytes (Buffer.sub signature 32ul 32ul) b 32ul;
  let h2 = ST.get() in
  no_upd_lemma_1 h1 h2 (Buffer.sub signature 32ul 32ul) (Buffer.sub signature 0ul 32ul);
  Seq.lemma_eq_intro (as_seq h2 signature) FStar.Seq.(as_seq h0 a @| as_seq h0 b)


#reset-options "--max_fuel 0 --z3rlimit 20"

inline_for_extraction
private
val sign__:
  signature:hint8_p{length signature = 64} ->
  secret:hint8_p{length secret = 32} ->
  msg:hint8_p{length msg < pow2 32 - 64} ->
  len:UInt32.t{UInt32.v len = length msg} ->
  tmp_bytes:hint8_p{length tmp_bytes = 352 /\ disjoint tmp_bytes signature /\ disjoint tmp_bytes secret /\ disjoint tmp_bytes msg} ->
  tmp_ints:buffer Hacl.UInt64.t{length tmp_ints = 65 /\ disjoint tmp_ints tmp_bytes /\ disjoint tmp_ints signature /\ disjoint tmp_ints secret /\ disjoint tmp_ints msg} ->
  Stack unit
    (requires (fun h -> live h signature /\ live h msg /\ live h secret /\
      live h tmp_bytes /\ live h tmp_ints))
    (ensures (fun h0 _ h1 -> live h0 signature /\ live h0 msg /\ live h0 secret /\
      live h1 signature /\ modifies_3 signature tmp_bytes tmp_ints h0 h1 /\
      h1.[signature] == Spec.Ed25519.sign h0.[secret] h0.[msg]))


#reset-options "--max_fuel 0 --z3rlimit 500"

let sign__ signature secret msg len tmp_bytes tmp_ints =
  assert_norm(pow2 56 = 0x100000000000000);
  assert_norm(Spec.Ed25519.q = 0x1000000000000000000000000000000014def9dea2f79cd65812631a5cf5d3ed);
  assert_norm(pow2 256 = 0x10000000000000000000000000000000000000000000000000000000000000000);
  let r    = Buffer.sub tmp_ints 20ul 5ul  in
  let h    = Buffer.sub tmp_ints 60ul 5ul  in
  let rs'  = Buffer.sub tmp_bytes 160ul 32ul in
  let s'   = Buffer.sub tmp_bytes 192ul 32ul in
  let h0 = ST.get() in
  sign_step_1 secret tmp_bytes;
  let h1 = ST.get() in
  no_upd_lemma_1 h0 h1 tmp_bytes msg;
  no_upd_lemma_1 h0 h1 tmp_bytes tmp_ints;
  sign_step_2 msg len tmp_bytes tmp_ints;
  let h2 = ST.get() in
  no_upd_lemma_1 h1 h2 tmp_ints msg;
  no_upd_lemma_1 h1 h2 tmp_ints tmp_bytes;
  sign_step_3 tmp_bytes tmp_ints;
  let h3 = ST.get() in
  no_upd_lemma_1 h2 h3 tmp_bytes msg;
  no_upd_lemma_1 h2 h3 tmp_bytes tmp_ints;
  sign_step_4 msg len tmp_bytes tmp_ints;
  let h4 = ST.get() in
  no_upd_lemma_1 h2 h3 tmp_bytes msg;
  no_upd_lemma_1 h2 h3 tmp_bytes tmp_ints;
  assert(Hacl.Spec.BignumQ.Eval.eval_q (reveal_h64s (as_seq h4 r)) < 0x1000000000000000000000000000000014def9dea2f79cd65812631a5cf5d3ed);
  assert(Hacl.Spec.BignumQ.Eval.eval_q (reveal_h64s (as_seq h4 h)) < 0x1000000000000000000000000000000014def9dea2f79cd65812631a5cf5d3ed);
  sign_step_5 tmp_bytes tmp_ints;
  let h5 = ST.get() in
  append_to_sig signature rs' s';
  let h6 = ST.get() in
  lemma_modifies_3 h0 h1 h2 h3 h4 h5 h6 signature tmp_bytes tmp_ints;
  ()


#reset-options "--max_fuel 0 --z3rlimit 20"


val lemma_modifies_3_to_modifies_2:
  #a:Type -> #a':Type -> #a'':Type ->
  h0:HyperStack.mem ->
  h1:HyperStack.mem ->
  h2:HyperStack.mem ->
  h3:HyperStack.mem ->
  h4:HyperStack.mem ->
  b:buffer a -> b':buffer a' -> b'':buffer a'' ->
  Lemma (requires (live h0 b /\ live h0 b' /\ HyperStack.fresh_frame h0 h1 /\ modifies_0 h1 h2 /\
    b'' `unused_in` h1 /\ live h2 b'' /\ frameOf b'' = (FStar.HyperStack.get_tip h1) /\ modifies_3 b b' b'' h2 h3 /\
    HyperStack.popped h3 h4 /\ ST.equal_domains h2 h3))
        (ensures (modifies_2 b b' h0 h4))

#reset-options "--max_fuel 0 --z3rlimit 200"

let lemma_modifies_3_to_modifies_2 #a #a' #a'' h0 h1 h2 h3 h4 b b' b'' =
  lemma_reveal_modifies_0 h1 h2;
  lemma_reveal_modifies_3 b b' b'' h2 h3;
  lemma_intro_modifies_2 b b' h0 h4

#reset-options "--max_fuel 0 --z3rlimit 20"

inline_for_extraction
private
val sign_:
  signature:hint8_p{length signature = 64} ->
  secret:hint8_p{length secret = 32} ->
  msg:hint8_p{length msg < pow2 32 - 64} ->
  len:UInt32.t{UInt32.v len = length msg} ->
  Stack unit
    (requires (fun h -> live h signature /\ live h msg /\ live h secret))
    (ensures (fun h0 _ h1 -> live h0 signature /\ live h0 msg /\ live h0 secret /\
      live h1 signature /\ modifies_1 signature h0 h1 /\
      h1.[signature] == Spec.Ed25519.sign h0.[secret] h0.[msg]))

#reset-options "--max_fuel 0 --z3rlimit 100"
let sign_ signature secret msg len =
  let hh0 = ST.get() in
  push_frame();
  let hh1 = ST.get() in
  let tmp_bytes = Buffer.create (Hacl.Cast.uint8_to_sint8 0uy) (352ul) in
  let h0 = ST.get() in
  push_frame();
  let h1 = ST.get() in
  let tmp_ints  = Buffer.create (Hacl.Cast.uint64_to_sint64 0uL) 65ul in
  let h2 = ST.get() in
  no_upd_lemma_0 h1 h2 secret;
  no_upd_lemma_0 h1 h2 msg;
  sign__ signature secret msg len tmp_bytes tmp_ints;
  let h3 = ST.get() in
  pop_frame();
  let h4 = ST.get() in
  lemma_modifies_3_to_modifies_2 h0 h1 h2 h3 h4 signature tmp_bytes tmp_ints;
  pop_frame();
  let hh1 = ST.get() in
  ()


inline_for_extraction
val sign:
  signature:hint8_p{length signature = 64} ->
  secret:hint8_p{length secret = 32} ->
  msg:hint8_p{length msg < pow2 32 - 64} ->
  len:UInt32.t{UInt32.v len = length msg} ->
  Stack unit
    (requires (fun h -> live h signature /\ live h msg /\ live h secret))
    (ensures (fun h0 _ h1 -> live h0 signature /\ live h0 msg /\ live h0 secret /\
      live h1 signature /\ modifies_1 signature h0 h1 /\
      h1.[signature] == Spec.Ed25519.sign h0.[secret] h0.[msg]))

#reset-options "--max_fuel 0 --z3rlimit 20"

let sign signature secret msg len =
  sign_ signature secret msg len
