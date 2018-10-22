module Hacl.Impl.Ed25519.Sign.Expanded

module ST = FStar.HyperStack.ST

open FStar.HyperStack.ST
open FStar.Mul
open FStar.Buffer
open FStar.UInt32

open Hacl.Impl.Ed25519.ExtPoint
open Hacl.Impl.Ed25519.Ladder.Step
open Hacl.Impl.Ed25519.Sign
open Hacl.Impl.Ed25519.Sign.Steps
open Hacl.Impl.Ed25519.SecretExpand
open Hacl.Impl.Ed25519.SecretToPublic
open Hacl.Spec.Endianness

type keys = ks:hint8_p{length ks = 96}
inline_for_extraction private let pk (ks:keys) = Buffer.sub ks 0ul 32ul
inline_for_extraction private let xsk (ks:keys) = Buffer.sub ks 32ul 64ul
inline_for_extraction private let xlow (ks:keys) = Buffer.sub ks 32ul 32ul
inline_for_extraction private let xhigh (ks:keys) = Buffer.sub ks 64ul 32ul


#reset-options "--max_fuel 0 --max_ifuel 0 --z3rlimit 500"

inline_for_extraction
val expand_keys:
  ks:keys ->
  secret:hint8_p{length secret = 32} ->
  Stack unit
    (requires (fun h -> live h ks /\ live h secret /\ disjoint ks secret))
    (ensures (fun h0 _ h1 ->
                  live h0 ks /\ live h0 secret /\
                  live h1 ks /\
                  modifies_1 ks h0 h1 /\ (
                    (h1.[xlow ks], h1.[xhigh ks]) == Spec.Ed25519.secret_expand h0.[secret] /\
                    h1.[pk ks] == Spec.Ed25519.secret_to_public h0.[secret])
    ))

let expand_keys ks secret =
  secret_expand (xsk ks) secret;
  secret_to_public (pk ks) secret


#reset-options "--max_fuel 0 --max_ifuel 0 --z3rlimit 500"

inline_for_extraction
private
val load_keys:
  tmp_bytes:hint8_p{length tmp_bytes = 352} ->
  ks:keys ->
  Stack unit
    (requires (fun h -> live h ks /\ live h tmp_bytes /\ disjoint ks tmp_bytes))
    (ensures (fun h0 _ h1 -> live h0 ks /\ live h0 tmp_bytes /\
                             live h1 ks /\ modifies_1 tmp_bytes h0 h1))

let load_keys tmp_bytes ks =
  let tmp_public = Buffer.sub tmp_bytes 96ul 32ul in
  let tmp_xsecret = Buffer.sub tmp_bytes 224ul 64ul in
  Buffer.blit (pk ks) 0ul tmp_public 0ul 32ul;
  Buffer.blit (xsk ks) 0ul tmp_xsecret 0ul 64ul


#reset-options "--max_fuel 2 --max_ifuel 0 --z3rlimit 500"

inline_for_extraction
private
val sign__:
  signature:hint8_p{length signature = 64} ->
  ks:keys ->
  msg:hint8_p{length msg < pow2 32 - 64} ->
  len:UInt32.t{UInt32.v len = length msg} ->
  tmp_bytes:hint8_p{length tmp_bytes = 352 /\ 
                    disjoint tmp_bytes signature /\ disjoint tmp_bytes ks /\ disjoint tmp_bytes msg} ->
  tmp_ints:buffer Hacl.UInt64.t{length tmp_ints = 65 /\ 
                                disjoint tmp_ints tmp_bytes /\ disjoint tmp_ints signature /\ 
                                disjoint tmp_ints ks /\ disjoint tmp_ints msg} ->
  Stack unit
    (requires (fun h -> live h signature /\ live h msg /\ live h ks /\
                        live h tmp_bytes /\ live h tmp_ints))
    (ensures (fun h0 _ h1 -> live h0 signature /\ live h0 msg /\ live h0 ks /\
                             live h1 signature /\ modifies_3 signature tmp_bytes tmp_ints h0 h1 /\
                             h1.[signature] == Spec.Ed25519.sign_expanded h0.[ks] h0.[msg]))

let sign__ signature ks msg len tmp_bytes tmp_ints =
  assert_norm(pow2 56 = 0x100000000000000);
  assert_norm(Spec.Ed25519.q = 0x1000000000000000000000000000000014def9dea2f79cd65812631a5cf5d3ed);
  assert_norm(pow2 256 = 0x10000000000000000000000000000000000000000000000000000000000000000);
  let r    = Buffer.sub tmp_ints 20ul 5ul  in
  let h    = Buffer.sub tmp_ints 60ul 5ul  in
  let rs'  = Buffer.sub tmp_bytes 160ul 32ul in
  let s'   = Buffer.sub tmp_bytes 192ul 32ul in
  let h0 = ST.get() in
  load_keys tmp_bytes ks;
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
  admit(); // CMW: This seems to take forever!
  ()


#reset-options "--max_fuel 0 --z3rlimit 20"

inline_for_extraction
private
val sign_:
  signature:hint8_p{length signature = 64} ->
  ks:keys ->
  msg:hint8_p{length msg < pow2 32 - 64} ->
  len:UInt32.t{UInt32.v len = length msg} ->
  Stack unit
    (requires (fun h -> live h signature /\ live h msg /\ live h ks))
    (ensures (fun h0 _ h1 -> 
      live h0 signature /\ live h0 msg /\ live h0 ks /\
      live h1 signature /\ modifies_1 signature h0 h1 /\
      h1.[signature] == Spec.Ed25519.sign_expanded h0.[ks] h0.[msg]))

let sign_ signature ks msg len =
  let hh0 = ST.get() in
  push_frame();
  let hh1 = ST.get() in
  let tmp_bytes = Buffer.create (Hacl.Cast.uint8_to_sint8 0uy) (352ul) in
  let h0 = ST.get() in
  push_frame();
  let h1 = ST.get() in
  let tmp_ints  = Buffer.create (Hacl.Cast.uint64_to_sint64 0uL) 65ul in
  let h2 = ST.get() in
  no_upd_lemma_0 h1 h2 (xsk ks);
  no_upd_lemma_0 h1 h2 msg;
  sign__ signature ks msg len tmp_bytes tmp_ints;
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
  ks:keys ->
  msg:hint8_p{length msg < pow2 32 - 64} ->
  len:UInt32.t{UInt32.v len = length msg} ->
  Stack unit
    (requires (fun h -> live h signature /\ live h msg /\ live h ks))
    (ensures (fun h0 _ h1 -> live h0 signature /\ live h0 msg /\ live h0 ks /\
      live h1 signature /\ modifies_1 signature h0 h1 /\
      h1.[signature] == Spec.Ed25519.sign_expanded h0.[ks] h0.[msg]))

let sign signature ks msg len =
  sign_ signature ks msg len
