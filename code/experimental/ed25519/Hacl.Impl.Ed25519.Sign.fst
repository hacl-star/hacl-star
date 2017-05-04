module Hacl.Impl.Ed25519.Sign


open FStar.Mul
open FStar.Buffer
open FStar.UInt32

open Hacl.Impl.Ed25519.ExtPoint
open Hacl.Impl.Ed25519.Ladder.Step

let hint8_p = buffer Hacl.UInt8.t
let op_String_Access h b = Hacl.Spec.Endianness.reveal_sbytes (as_seq h b)


open Hacl.Impl.Ed25519.Sign.Steps

[@ "substitute"]
private
val sign__:
  signature:hint8_p{length signature = 64} ->
  secret:hint8_p{length secret = 32} ->
  msg:hint8_p{length msg < pow2 32 - 64} ->
  len:UInt32.t{UInt32.v len = length msg} ->
  g:point ->
  tmp_bytes:hint8_p{length tmp_bytes = 352 + UInt32.v len} ->
  tmp_ints:buffer Hacl.UInt64.t{length tmp_ints = 65} ->
  Stack unit
    (requires (fun h -> live h signature /\ live h msg /\ live h secret /\ live h g /\ 
      live h tmp_bytes /\ live h tmp_ints /\ as_point h g == Spec.Ed25519.g /\
      as_seq h (Buffer.sub tmp_bytes 64ul len) == as_seq h msg))
    (ensures (fun h0 _ h1 -> live h0 signature /\ live h0 msg /\ live h0 secret /\
      live h1 signature /\ modifies_3 signature tmp_bytes tmp_ints h0 h1 /\
      h1.[signature] == Spec.Ed25519.sign h0.[secret] h0.[msg]))


#reset-options "--max_fuel 0 --z3rlimit 200"

let sign__ signature secret msg len g tmp_bytes tmp_ints =
  let tmp_bytes' = tmp_bytes in
  let tmpa = Buffer.sub tmp_ints 0ul  20ul in
  let r    = Buffer.sub tmp_ints 20ul 5ul  in
  let r'   = Buffer.sub tmp_ints 25ul 20ul in
  let aq   = Buffer.sub tmp_ints 45ul 5ul  in
  let ha   = Buffer.sub tmp_ints 50ul 5ul  in
  let s    = Buffer.sub tmp_ints 55ul 5ul  in
  let h    = Buffer.sub tmp_ints 60ul 5ul  in
  let prefix_at_message = Buffer.sub tmp_bytes 0ul FStar.UInt32.(64ul +^ len) in
  let tmp_bytes         = Buffer.offset tmp_bytes FStar.UInt32.(64ul +^ len) in
  let buf  = Buffer.sub tmp_bytes 0ul   96ul in
  let a''  = Buffer.sub tmp_bytes 96ul  32ul in
  let rb   = Buffer.sub tmp_bytes 128ul 32ul in
  let rs'  = Buffer.sub tmp_bytes 160ul 32ul in
  let s'   = Buffer.sub tmp_bytes 192ul 32ul in
  let apre = Buffer.sub tmp_bytes 224ul 64ul in
  
  sign_step_1 signature secret msg len g tmp_bytes' tmp_ints;

  (* TODO: use an incremental version of SHA instead so as to minimize
  the copies and enable compilation with CompCert *)

  sign_step_2 signature secret msg len g tmp_bytes' tmp_ints;

  sign_step_3 signature secret msg len tmp_bytes' tmp_ints;

  sign_step_4 signature secret msg len g tmp_bytes' tmp_ints;

  sign_step_5 len tmp_bytes' tmp_ints;

  copy_bytes (Buffer.sub signature 0ul 32ul) rs' 32ul;
  copy_bytes (Buffer.sub signature 32ul 32ul) s' 32ul;
  let h'' = ST.get() in
  (* lemma_append2 h'' signature 32ul 32ul; *)
  ()


#reset-options "--max_fuel 0 --z3rlimit 20"

val sign_:
  signature:hint8_p{length signature = 64} ->
  secret:hint8_p{length secret = 32} ->
  msg:hint8_p{length msg < pow2 32 - 64} ->
  len:UInt32.t{UInt32.v len = length msg /\ UInt32.v len + 352 < pow2 32} ->
  g:point ->
  Stack unit
    (requires (fun h -> live h signature /\ live h msg /\ live h secret /\ live h g /\ 
      as_point h g == Spec.Ed25519.g))
    (ensures (fun h0 _ h1 -> live h0 signature /\ live h0 msg /\ live h0 secret /\
      live h1 signature /\ modifies_1 signature h0 h1 /\
      h1.[signature] == Spec.Ed25519.sign h0.[secret] h0.[msg]))

#reset-options "--max_fuel 0 --z3rlimit 50"

let sign_ signature secret msg len g =
  push_frame();
  let tmp_bytes = Buffer.create 0uy (352ul +^ len) in
  push_frame();
  let h0 = ST.get() in
  let tmp_ints  = Buffer.create 0uL 65ul in
  let msg'      = Buffer.sub tmp_bytes 64ul len in
  let h1 = ST.get() in
  no_upd_lemma_0 h0 h1 g;
  no_upd_lemma_0 h0 h1 msg;
  copy_bytes msg' msg len;
  let h2 = ST.get() in
  no_upd_lemma_1 h1 h2 msg' g;
  assert(modifies_0 h0 h2);
  sign__ signature secret msg len g tmp_bytes tmp_ints;
  let h3 = ST.get() in
  pop_frame();
  pop_frame()


val sign:
  signature:hint8_p{length signature = 64} ->
  secret:hint8_p{length secret = 32} ->
  msg:hint8_p{length msg < pow2 32 - 64} ->
  len:UInt32.t{UInt32.v len = length msg /\ UInt32.v len + 352 < pow2 32} ->
  Stack unit
    (requires (fun h -> live h signature /\ live h msg /\ live h secret))
    (ensures (fun h0 _ h1 -> live h0 signature /\ live h0 msg /\ live h0 secret /\
      live h1 signature /\ modifies_1 signature h0 h1 /\
      h1.[signature] == Spec.Ed25519.sign h0.[secret] h0.[msg]))

#reset-options "--max_fuel 0 --z3rlimit 20"

let sign signature secret msg len =
  push_frame();
  let h0 = ST.get() in
  let g = create 0uL 20ul in
  Hacl.Impl.Ed25519.G.make_g g;
  let h1 = ST.get() in
  assume (as_point h1 g == Spec.Ed25519.g);
  sign_ signature secret msg len g;
  let h2 = ST.get() in
  pop_frame()
