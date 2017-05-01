module Hacl.Impl.Ed25519.Sign

open FStar.Buffer
open FStar.UInt32

open Hacl.Impl.Ed25519.ExtPoint
open Hacl.Impl.Ed25519.Ladder.Step

let hint8_p = buffer Hacl.UInt8.t
let op_String_Access h b = Hacl.Spec.Endianness.reveal_sbytes (as_seq h b)


#reset-options "--max_fuel 0 --z3rlimit 20"

[@ "substitute"]
private
val point_mul_compress:
  out:hint8_p{length out = 32} ->
  s:hint8_p{length s = 32} ->
  p:point ->
  Stack unit
    (requires (fun h -> live h out /\ live h s /\ live h p /\ point_inv h p))
    (ensures (fun h0 _ h1 -> live h1 out /\ live h0 s /\ live h0 p /\ modifies_1 out h0 h1 /\
      h1.[out] == Spec.Ed25519.(point_compress (point_mul h0.[s] (as_point h0 p)))))

#reset-options "--max_fuel 0 --z3rlimit 200"

let point_mul_compress out s p =
  push_frame();
  let tmp:point = Buffer.create 0uL 20ul in
  Hacl.Impl.Ed25519.Ladder.point_mul tmp s p;
  Hacl.Impl.Ed25519.PointCompress.point_compress out tmp;
  pop_frame()


#reset-options "--max_fuel 0 --z3rlimit 20"

[@ "substitute"]
private
val copy_bytes:
  output:hint8_p ->
  input:hint8_p{disjoint input output} ->
  len:UInt32.t{length output = UInt32.v len /\ length input = UInt32.v len} ->
  Stack unit
    (requires (fun h -> live h output /\ live h input))
    (ensures (fun h0 _ h1 -> live h0 input /\ live h1 output /\ modifies_1 output h0 h1
      /\ as_seq h1 output == as_seq h0 input))
let copy_bytes output input len =
  let h0 = ST.get() in
  blit input 0ul output 0ul len;
  let h1 = ST.get() in
  Seq.lemma_eq_intro (as_seq h0 input) (Seq.slice (as_seq h0 input) 0 (UInt32.v len));
  Seq.lemma_eq_intro (as_seq h1 output) (Seq.slice (as_seq h1 output) 0 (UInt32.v len))


#reset-options "--max_fuel 0 --z3rlimit 200"


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


private
val lemma_append2:
  h:HyperStack.mem ->
  buf:hint8_p{live h buf} ->
  len1:UInt32.t ->
  len2:UInt32.t{UInt32.v len1 + UInt32.v len2 = length buf} ->
  Lemma (as_seq h buf == FStar.Seq.(as_seq h (Buffer.sub buf 0ul len1) @| as_seq h (Buffer.sub buf len1 len2)))

let lemma_append2 h buf len1 len2 =
  let open FStar.UInt32 in
  let b = as_seq h buf in
  Seq.lemma_eq_intro (as_seq h (Buffer.sub buf 0ul len1)) (Seq.slice b 0 (v len1));
  Seq.lemma_eq_intro (as_seq h (Buffer.sub buf len1 len2)) (Seq.slice b (v len1) (v len1 + v len2));
  Seq.lemma_eq_intro b FStar.Seq.(slice b 0 (v len1) @| slice b (v len1) (v len1 + v len2))


#reset-options "--max_fuel 0 --z3rlimit 20"

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
  push_frame();
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
  Hacl.Impl.Ed25519.SecretExpand.secret_expand apre secret;
  let a      = Buffer.sub apre 0ul 32ul in
  let prefix = Buffer.sub apre 32ul 64ul in
  point_mul_compress a'' a g;
  (* TODO: use an incremental version of SHA instead so as to minimize
  the copies and enable compilation with CompCert *)
  let prefix_at_msg = Buffer.sub prefix_at_message 32ul FStar.UInt32.(32ul +^ len) in
  let message       = Buffer.sub prefix_at_msg 32ul len in
  let prefix'       = Buffer.sub prefix_at_msg 0ul 32ul in
  copy_bytes prefix' prefix 32ul;
  let h0 = ST.get() in
  lemma_append2 h0 prefix_at_msg 32ul len;
  Hacl.Impl.SHA512.ModQ.sha512_modq r prefix_at_msg (len+^32ul);
  Hacl.Impl.Store56.store_56 rb r;
  point_mul_compress rs' rb g;
  (* Hacl.Impl.Ed25519.Ladder.point_mul r' rb g; *)
  (* Hacl.Impl.Ed25519.PointCompress.point_compress rs' r'; *)
  let rs_bytes = Buffer.sub prefix_at_message 0ul  32ul in
  let a_bytes  = Buffer.sub prefix_at_message 32ul 32ul in
  copy_bytes rs_bytes rs' 32ul;
  copy_bytes a_bytes a'' 32ul;
  (* blit rs'  0ul prefix_at_message 0ul 32ul; *)
  (* blit a''  0ul prefix_at_message 32ul 32ul; *)
  let h' = ST.get() in
  lemma_append h' prefix_at_message 32ul 32ul len;
  Hacl.Impl.SHA512.ModQ.sha512_modq h prefix_at_message (len+^64ul);
  Hacl.Impl.Load56.load_32_bytes aq a;
  Hacl.Impl.BignumQ.Mul.mul_modq ha h aq;
  Hacl.Impl.BignumQ.Mul.add_modq s r ha;
  Hacl.Impl.Store56.store_56 s' s;
  copy_bytes (Buffer.sub signature 0ul 32ul) rs' 32ul;
  copy_bytes (Buffer.sub signature 32ul 32ul) s' 32ul;
  let h'' = ST.get() in
  lemma_append2 h'' signature 32ul 32ul;
  admit();
  (* blit rs' 0ul signature 0ul 32ul; *)
  (* blit s' 0ul signature 32ul 32ul; *)
  pop_frame()


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

#reset-options "--max_fuel 0 --z3rlimit 100"

let sign_ signature secret msg len g =
  push_frame();
  let tmp_bytes = Buffer.create 0uy (352ul +^ len) in
  push_frame();
  let h0 = ST.get() in  
  let tmp_ints  = Buffer.create 0uL 65ul in
  let msg'      = Buffer.sub tmp_bytes 64ul len in
  let h1 = ST.get() in
  copy_bytes msg' msg len;
  let h2 = ST.get() in
  sign__ signature secret msg len g tmp_bytes tmp_ints;
  let h3 = ST.get() in
  pop_frame();
  pop_frame()


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

let sign signature secret msg len =
  push_frame();
  let g = create 0uL 20ul in
  Hacl.Impl.Ed25519.G.make_g g;
  sign_ signature secret msg len g;  
  pop_frame()
