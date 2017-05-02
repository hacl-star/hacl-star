module Hacl.Impl.Ed25519.Sign.Steps


open FStar.Mul
open FStar.Buffer
open FStar.UInt32

open Hacl.Impl.Ed25519.ExtPoint
open Hacl.Impl.Ed25519.Ladder.Step


let hint8_p = buffer Hacl.UInt8.t
let op_String_Access h b = Hacl.Spec.Endianness.reveal_sbytes (as_seq h b)


#reset-options "--max_fuel 0 --z3rlimit 200"

val lemma_point_inv:
  h:HyperStack.mem -> p:point{live h p} -> h':HyperStack.mem -> p':point{live h' p'} ->
  Lemma (requires (as_seq h p == as_seq h' p' /\ point_inv h p))
        (ensures (point_inv h' p'))
let lemma_point_inv h p h' p' = ()


#reset-options "--max_fuel 0 --z3rlimit 20"

[@ "substitute"]
val point_mul_compress:
  out:hint8_p{length out = 32} ->
  s:hint8_p{length s = 32 /\ disjoint s out} ->
  p:point{disjoint p out} ->
  Stack unit
    (requires (fun h -> live h out /\ live h s /\ live h p /\ point_inv h p))
    (ensures (fun h0 _ h1 -> live h1 out /\ live h0 s /\ live h0 p /\ modifies_1 out h0 h1 /\
      live h1 p /\ live h1 s /\
      h1.[out] == Spec.Ed25519.(point_compress (point_mul h0.[s] (as_point h0 p)))))

#reset-options "--max_fuel 0 --z3rlimit 200"

let point_mul_compress out s p =
  let h = ST.get() in
  push_frame();
  let h0 = ST.get() in
  let tmp:point = Buffer.create 0uL 20ul in
  let h' = ST.get() in
  lemma_point_inv h p h' p;
  Hacl.Impl.Ed25519.Ladder.point_mul tmp s p;
  let h1 = ST.get() in
  no_upd_lemma_0 h0 h1 s;
  no_upd_lemma_0 h0 h1 p;
  Hacl.Impl.Ed25519.PointCompress.point_compress out tmp;
  let h2 = ST.get() in
  no_upd_lemma_1 h1 h2 out s;
  no_upd_lemma_1 h1 h2 out p;
  pop_frame()


#reset-options "--max_fuel 0 --z3rlimit 20"

[@ "substitute"]
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
val sign_step_1:
  signature:hint8_p{length signature = 64} ->
  secret:hint8_p{length secret = 32} ->
  msg:hint8_p{length msg < pow2 32 - 64} ->
  len:UInt32.t{UInt32.v len = length msg} ->
  g:point ->
  tmp_bytes:hint8_p{length tmp_bytes = 352 + UInt32.v len /\ disjoint tmp_bytes g /\ disjoint tmp_bytes signature /\ disjoint tmp_bytes secret /\ disjoint tmp_bytes msg} ->
  tmp_ints:buffer Hacl.UInt64.t{length tmp_ints = 65 /\ disjoint tmp_bytes tmp_ints /\ disjoint tmp_ints g /\ disjoint tmp_ints signature /\ disjoint tmp_ints secret /\ disjoint tmp_ints msg} ->
  Stack unit
    (requires (fun h -> live h signature /\ live h msg /\ live h secret /\ live h g /\ point_inv h g /\
      live h tmp_bytes /\ live h tmp_ints /\ as_point h g == Spec.Ed25519.g /\
      as_seq h (Buffer.sub tmp_bytes 64ul len) == as_seq h msg))
    (ensures (fun h0 _ h1 -> live h0 signature /\ live h0 msg /\ live h0 secret /\ live h0 tmp_bytes /\
      live h0 tmp_ints /\ live h1 tmp_bytes /\ live h1 tmp_ints /\
      live h1 signature /\ modifies_1 tmp_bytes h0 h1 /\ (
        let tmp_bytes         = Buffer.offset tmp_bytes FStar.UInt32.(64ul +^ len) in
        let a''  = Buffer.sub tmp_bytes 96ul  32ul in
        let apre = Buffer.sub tmp_bytes 224ul 64ul in
        let a      = Buffer.sub apre 0ul 32ul in
        let prefix = Buffer.sub apre 32ul 32ul in
        (as_seq h1 a, as_seq h1 prefix) == Spec.Ed25519.(secret_expand (as_seq h0 secret)) /\
        as_seq h1 a'' == Spec.Ed25519.(point_compress (point_mul (as_seq h1 a) g))) /\
     as_seq h1 (Buffer.sub tmp_bytes 64ul len) == as_seq h0 msg
   ))


#reset-options "--max_fuel 0 --z3rlimit 200"

let sign_step_1 signature secret msg len g tmp_bytes tmp_ints =
  let msg' = Buffer.sub tmp_bytes 64ul len in
  let tmp_bytes         = Buffer.offset tmp_bytes FStar.UInt32.(64ul +^ len) in
  let a''  = Buffer.sub tmp_bytes 96ul  32ul in
  let apre = Buffer.sub tmp_bytes 224ul 64ul in
  let a      = Buffer.sub apre 0ul 32ul in
  let prefix = Buffer.sub apre 32ul 32ul in
  let h0 = ST.get() in
  Hacl.Impl.Ed25519.SecretExpand.secret_expand apre secret;
  let h1 = ST.get() in
  no_upd_lemma_1 h0 h1 apre g;
  no_upd_lemma_1 h0 h1 apre msg';
  point_mul_compress a'' a g;
  let h2 = ST.get() in
  no_upd_lemma_1 h1 h2 a'' a;
  no_upd_lemma_1 h1 h2 a'' msg';
  no_upd_lemma_1 h1 h2 a'' prefix


#reset-options "--max_fuel 0 --z3rlimit 20"

[@ "substitute"]
val sign_step_2:
  signature:hint8_p{length signature = 64} ->
  secret:hint8_p{length secret = 32} ->
  msg:hint8_p{length msg < pow2 32 - 64} ->
  len:UInt32.t{UInt32.v len = length msg} ->
  g:point ->
  tmp_bytes:hint8_p{length tmp_bytes = 352 + UInt32.v len /\ disjoint tmp_bytes signature /\ disjoint tmp_bytes secret /\ disjoint tmp_bytes msg /\ disjoint tmp_bytes g} ->
  tmp_ints:buffer Hacl.UInt64.t{length tmp_ints = 65 /\ disjoint tmp_bytes tmp_ints /\ disjoint tmp_ints signature /\ disjoint tmp_ints secret /\ disjoint tmp_ints msg /\ disjoint tmp_ints g} ->
  Stack unit
    (requires (fun h -> live h signature /\ live h msg /\ live h secret /\ live h g /\
      live h tmp_bytes /\ live h tmp_ints /\ as_point h g == Spec.Ed25519.g /\
      as_seq h (Buffer.sub tmp_bytes 64ul len) == as_seq h msg))
    (ensures (fun h0 _ h1 -> live h0 signature /\ live h0 msg /\ live h0 secret /\
      live h0 tmp_bytes /\ live h1 tmp_bytes /\ live h0 tmp_ints /\ live h1 tmp_ints /\
      live h1 signature /\ modifies_2 tmp_bytes tmp_ints h0 h1 /\ (
        let r    = Buffer.sub tmp_ints 20ul 5ul  in
        let prefix_at_message = Buffer.sub tmp_bytes 0ul FStar.UInt32.(64ul +^ len) in
        let tmp_bytes         = Buffer.offset tmp_bytes FStar.UInt32.(64ul +^ len) in
        let a''  = Buffer.sub tmp_bytes 96ul  32ul in
        let rb   = Buffer.sub tmp_bytes 128ul 32ul in
        let apre = Buffer.sub tmp_bytes 224ul 64ul in
        let a      = Buffer.sub apre 0ul  32ul in
        let prefix = Buffer.sub apre 32ul 32ul in
        Hacl.Spec.BignumQ.Eval.eval_q (as_seq h1 r) == 
          Spec.Ed25519.(sha512_modq FStar.Seq.(as_seq h0 prefix @| as_seq h0 msg)) /\
        as_seq h1 a == as_seq h0 a /\
        as_seq h1 a'' == as_seq h0 a''
        )
    ))


#reset-options "--max_fuel 0 --z3rlimit 500"


let lemma_sub (len:UInt32.t) (tmp:buffer Hacl.UInt8.t{length tmp = 352 + v len}) : Lemma
  (let prefix_at_message = Buffer.sub tmp 0ul FStar.UInt32.(64ul +^ len) in
   let prefix_at_msg     = Buffer.sub prefix_at_message 32ul FStar.UInt32.(32ul +^ len) in
   let message           = Buffer.sub prefix_at_msg 32ul len in
   message == Buffer.sub tmp 64ul len)
   = ()


let sign_step_2 signature secret msg len g tmp_bytes tmp_ints =
  let tmp_bytes' = tmp_bytes in
  let r    = Buffer.sub tmp_ints 20ul 5ul  in
  let prefix_at_message = Buffer.sub tmp_bytes 0ul FStar.UInt32.(64ul +^ len) in
  let tmp_bytes         = Buffer.offset tmp_bytes FStar.UInt32.(64ul +^ len) in
  let a''  = Buffer.sub tmp_bytes 96ul  32ul in
  let rb   = Buffer.sub tmp_bytes 128ul 32ul in
  let apre = Buffer.sub tmp_bytes 224ul 64ul in
  let a      = Buffer.sub apre 0ul 32ul in
  let prefix = Buffer.sub apre 32ul 32ul in
  let prefix_at_msg = Buffer.sub prefix_at_message 32ul FStar.UInt32.(32ul +^ len) in
  let message       = Buffer.sub prefix_at_msg 32ul len in
  let prefix'       = Buffer.sub prefix_at_msg 0ul 32ul in
  lemma_sub len tmp_bytes';
  let h0 = ST.get() in
  copy_bytes prefix' prefix 32ul;
  let h1 = ST.get() in
  no_upd_lemma_1 h0 h1 prefix' message;
  no_upd_lemma_1 h0 h1 prefix' a;
  no_upd_lemma_1 h0 h1 prefix' a'';
  lemma_append2 h1 prefix_at_msg 32ul len;
  assert(as_seq h1 prefix' == as_seq h0 prefix);
  assert(as_seq h1 message == as_seq h0 message);
  assert(as_seq h1 prefix_at_msg == FStar.Seq.(as_seq h1 prefix' @| as_seq h1 message));
  assert(as_seq h1 prefix_at_msg == FStar.Seq.(as_seq h0 prefix @| as_seq h0 msg));
  assert(live h1 r);
  assert(live h1 prefix_at_msg);
  Hacl.Impl.SHA512.ModQ.sha512_modq r prefix_at_msg (len+^32ul);
  let h2 = ST.get() in
  no_upd_lemma_1 h1 h2 r message;
  no_upd_lemma_1 h1 h2 r a;
  no_upd_lemma_1 h1 h2 r a'';
  ()


#reset-options "--max_fuel 0 --z3rlimit 50"

[@ "substitute"]
val sign_step_4:
  signature:hint8_p{length signature = 64} ->
  secret:hint8_p{length secret = 32} ->
  msg:hint8_p{length msg < pow2 32 - 64} ->
  len:UInt32.t{UInt32.v len = length msg} ->
  g:point ->
  tmp_bytes:hint8_p{length tmp_bytes = 352 + UInt32.v len /\ disjoint tmp_bytes signature /\ disjoint tmp_bytes secret /\ disjoint tmp_bytes msg /\ disjoint tmp_bytes g} ->
  tmp_ints:buffer Hacl.UInt64.t{length tmp_ints = 65 /\ disjoint tmp_bytes tmp_ints /\ disjoint tmp_ints signature /\ disjoint tmp_ints secret /\ disjoint tmp_ints msg /\ disjoint tmp_ints g} ->
  Stack unit
    (requires (fun h -> live h signature /\ live h msg /\ live h secret /\ live h g /\
      live h tmp_bytes /\ live h tmp_ints /\ as_point h g == Spec.Ed25519.g /\
      as_seq h (Buffer.sub tmp_bytes 64ul len) == as_seq h msg))
    (ensures (fun h0 _ h1 -> live h0 signature /\ live h0 msg /\ live h0 secret /\
      live h0 tmp_bytes /\ live h1 tmp_bytes /\ live h0 tmp_ints /\ live h1 tmp_ints /\
      live h1 signature /\ modifies_2 tmp_bytes tmp_ints h0 h1 /\ (
        let tmpa = Buffer.sub tmp_ints 0ul  20ul in
        let r    = Buffer.sub tmp_ints 20ul 5ul  in
        let r'   = Buffer.sub tmp_ints 25ul 20ul in
        let aq   = Buffer.sub tmp_ints 45ul 5ul  in
        let ha   = Buffer.sub tmp_ints 50ul 5ul  in
        let s    = Buffer.sub tmp_ints 55ul 5ul  in
        let h    = Buffer.sub tmp_ints 60ul 5ul  in
        let prefix_at_message = Buffer.sub tmp_bytes 0ul FStar.UInt32.(64ul +^ len) in
        let tmp_bytes         = Buffer.offset tmp_bytes FStar.UInt32.(64ul +^ len) in
        (* let buf  = Buffer.sub tmp_bytes 0ul   96ul in *)
        let a''  = Buffer.sub tmp_bytes 96ul  32ul in
        let rb   = Buffer.sub tmp_bytes 128ul 32ul in
        let rs'  = Buffer.sub tmp_bytes 160ul 32ul in
        let s'   = Buffer.sub tmp_bytes 192ul 32ul in
        let apre = Buffer.sub tmp_bytes 224ul 64ul in
        let a      = Buffer.sub apre 0ul 32ul in
        let prefix = Buffer.sub apre 32ul 32ul in
        Hacl.Spec.BignumQ.Eval.eval_q (as_seq h1 h) == 
          Spec.Ed25519.(sha512_modq FStar.Seq.(as_seq h0 rs' @| as_seq h0 a'' @| as_seq h0 msg)) /\
        as_seq h1 a == as_seq h0 a /\
        as_seq h1 rs' == as_seq h0 rs' /\
        as_seq h1 r == as_seq h0 r
        )
    ))


#reset-options "--max_fuel 0 --z3rlimit 20"

val append_before_sha:
  msg:hint8_p ->
  len:UInt32.t{UInt32.v len = length msg} ->
  msg':hint8_p{length msg' = 64 + UInt32.v len /\ disjoint msg msg'} ->
  rs':hint8_p{length rs' = 32 /\ disjoint rs' msg'} ->
  a'':hint8_p{length a'' = 32 /\ disjoint a'' msg'} ->
  Stack unit
    (requires (fun h -> live h msg' /\ live h msg /\ live h rs' /\ live h a'' /\
      as_seq h (Buffer.sub msg' 64ul len) == as_seq h msg))
    (ensures (fun h0 _ h1 -> live h1 msg' /\ modifies_1 msg' h0 h1 /\ live h0 msg /\ live h0 rs' /\
      live h0 a'' /\
      as_seq h1 msg' == FStar.Seq.(as_seq h0 rs' @| as_seq h0 a'' @| as_seq h0 msg)))

#reset-options "--max_fuel 0 --z3rlimit 10"

let append_before_sha msg len msg' rs' a'' =
  let h0 = ST.get() in
  copy_bytes (Buffer.sub msg' 0ul 32ul) rs' 32ul;
  let h1 = ST.get() in
  no_upd_lemma_1 h0 h1 (Buffer.sub msg' 0ul 32ul) (Buffer.sub msg' 64ul len);
  no_upd_lemma_1 h0 h1 (Buffer.sub msg' 0ul 32ul) a'';
  copy_bytes (Buffer.sub msg' 32ul 32ul) a'' 32ul;
  let h2 = ST.get() in
  no_upd_lemma_1 h1 h2 (Buffer.sub msg' 32ul 32ul) (Buffer.sub msg' 64ul len);
  no_upd_lemma_1 h1 h2 (Buffer.sub msg' 32ul 32ul) (Buffer.sub msg' 0ul 32ul);
  lemma_append h2 msg' 32ul 32ul len


#reset-options "--max_fuel 0 --z3rlimit 200"

let sign_step_4 signature secret msg len g tmp_bytes tmp_ints =
  let tmp_bytes' = tmp_bytes in
  let r    = Buffer.sub tmp_ints 20ul 5ul  in
  let h    = Buffer.sub tmp_ints 60ul 5ul  in
  let prefix_at_message = Buffer.sub tmp_bytes 0ul FStar.UInt32.(64ul +^ len) in
  let tmp_bytes         = Buffer.offset tmp_bytes FStar.UInt32.(64ul +^ len) in
  let a''  = Buffer.sub tmp_bytes 96ul  32ul in
  let rb   = Buffer.sub tmp_bytes 128ul 32ul in
  let rs'  = Buffer.sub tmp_bytes 160ul 32ul in
  let apre = Buffer.sub tmp_bytes 224ul 64ul in
  let a      = Buffer.sub apre 0ul 32ul in
  let prefix = Buffer.sub apre 32ul 32ul in
  let rs_bytes = Buffer.sub prefix_at_message 0ul  32ul in
  let a_bytes  = Buffer.sub prefix_at_message 32ul 32ul in
  let message = Buffer.sub prefix_at_message 64ul len in
  lemma_sub len tmp_bytes';
  let h0 = ST.get() in
  assume(as_seq h0 (Buffer.sub prefix_at_message 64ul len) == as_seq h0 msg);
  append_before_sha msg len prefix_at_message rs' a'';
  let h1 = ST.get() in
  no_upd_lemma_1 h0 h1 prefix_at_message a;
  no_upd_lemma_1 h0 h1 prefix_at_message rs';
  no_upd_lemma_1 h0 h1 prefix_at_message r;
  Hacl.Impl.SHA512.ModQ.sha512_modq h prefix_at_message (len+^64ul);
  let h2 = ST.get() in
  no_upd_lemma_1 h1 h2 h a;
  no_upd_lemma_1 h1 h2 h rs';
  no_upd_lemma_1 h1 h2 h r


#reset-options "--max_fuel 0 --z3rlimit 20"

val sign_step_3:
  signature:hint8_p{length signature = 64} ->
  secret:hint8_p{length secret = 32} ->
  msg:hint8_p{length msg < pow2 32 - 64} ->
  len:UInt32.t{UInt32.v len = length msg} ->
  g:point ->
  tmp_bytes:hint8_p{length tmp_bytes = 352 + UInt32.v len /\ disjoint tmp_bytes signature /\ disjoint tmp_bytes secret /\ disjoint tmp_bytes msg /\ disjoint tmp_bytes g} ->
  tmp_ints:buffer Hacl.UInt64.t{length tmp_ints = 65 /\ disjoint tmp_bytes tmp_ints /\ disjoint tmp_ints signature /\ disjoint tmp_ints secret /\ disjoint tmp_ints msg /\ disjoint tmp_ints g} ->
  Stack unit
    (requires (fun h -> live h signature /\ live h msg /\ live h secret /\ live h g /\
      live h tmp_bytes /\ live h tmp_ints /\ as_point h g == Spec.Ed25519.g /\
      as_seq h (Buffer.sub tmp_bytes 64ul len) == as_seq h msg /\ (
        let r    = Buffer.sub tmp_ints 20ul 5ul  in
        Hacl.Spec.BignumQ.Eval.eval_q (as_seq h r) < pow2 256)
      ))
    (ensures (fun h0 _ h1 -> live h0 signature /\ live h0 msg /\ live h0 secret /\ live h0 g /\
      live h0 tmp_bytes /\ live h1 tmp_bytes /\ live h0 tmp_ints /\ live h1 tmp_ints /\
      live h1 signature /\ modifies_1 tmp_bytes h0 h1 /\ (
        let g' = g in
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
        let a      = Buffer.sub apre 0ul 32ul in
        let prefix = Buffer.sub apre 32ul 32ul in
        Hacl.Spec.BignumQ.Eval.eval_q (as_seq h0 r) < pow2 256 /\
        as_seq h1 rs' == Spec.Ed25519.(
            let r = Hacl.Spec.BignumQ.Eval.eval_q (as_seq h0 r) in
            let x = point_mul (Endianness.little_bytes 32ul r) (as_point h0 g') in
            point_compress x) /\
        as_seq h1 r == as_seq h0 r
        )
    ))

let sign_step_3 signature secret msg len g tmp_bytes tmp_ints =
  push_frame();
  let h0 = ST.get() in
  let rb = create 0uy 32ul in
  let h1 = ST.get() in
  let r    = Buffer.sub tmp_ints 20ul 5ul  in
  let tmp_bytes         = Buffer.offset tmp_bytes FStar.UInt32.(64ul +^ len) in
  let rs'  = Buffer.sub tmp_bytes 160ul 32ul in  
  Hacl.Impl.Store56.store_56 rb r;
  let h2 = ST.get() in
  no_upd_lemma_0 h0 h2 r;
  no_upd_lemma_0 h0 h2 signature;
  no_upd_lemma_0 h0 h2 g;
  no_upd_lemma_0 h0 h2 tmp_ints;
  point_mul_compress rs' rb g;
  let h3 = ST.get() in
  pop_frame()


val sign_step_5:
  signature:hint8_p{length signature = 64} ->
  secret:hint8_p{length secret = 32} ->
  msg:hint8_p{length msg < pow2 32 - 64} ->
  len:UInt32.t{UInt32.v len = length msg} ->
  g:point ->
  tmp_bytes:hint8_p{length tmp_bytes = 352 + UInt32.v len /\ disjoint tmp_bytes signature /\ disjoint tmp_bytes secret /\ disjoint tmp_bytes msg /\ disjoint tmp_bytes g} ->
  tmp_ints:buffer Hacl.UInt64.t{length tmp_ints = 65 /\ disjoint tmp_bytes tmp_ints /\ disjoint tmp_ints signature /\ disjoint tmp_ints secret /\ disjoint tmp_ints msg /\ disjoint tmp_ints g} ->
  Stack unit
    (requires (fun h -> live h signature /\ live h msg /\ live h secret /\ live h g /\
      live h tmp_bytes /\ live h tmp_ints /\ as_point h g == Spec.Ed25519.g /\
      as_seq h (Buffer.sub tmp_bytes 64ul len) == as_seq h msg))
    (ensures (fun h0 _ h1 -> live h0 signature /\ live h0 msg /\ live h0 secret /\
      live h0 tmp_bytes /\ live h1 tmp_bytes /\ live h0 tmp_ints /\ live h1 tmp_ints /\
      live h1 signature /\ modifies_2 tmp_bytes tmp_ints h0 h1 /\ (
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
        let a      = Buffer.sub apre 0ul 32ul in
        let prefix = Buffer.sub apre 32ul 32ul in
        Endianness.little_endian (as_seq h1 s') ==
          Spec.Ed25519.((Hacl.Spec.BignumQ.Eval.eval_q (as_seq h0 r) +
                          (Hacl.Spec.BignumQ.Eval.eval_q (as_seq h0 h) * (Endianness.little_endian (as_seq h0 a)))) % q) /\
        as_seq h1 rs' == as_seq h0 rs'
        )
    ))

let sign_step_5 signature secret msg len g tmp_bytes tmp_ints =
  let r    = Buffer.sub tmp_ints 20ul 5ul  in
  let aq   = Buffer.sub tmp_ints 45ul 5ul  in
  let ha   = Buffer.sub tmp_ints 50ul 5ul  in
  let s    = Buffer.sub tmp_ints 55ul 5ul  in
  let h    = Buffer.sub tmp_ints 60ul 5ul  in
  let tmp_bytes         = Buffer.offset tmp_bytes FStar.UInt32.(64ul +^ len) in
  let s'   = Buffer.sub tmp_bytes 192ul 32ul in
  let apre = Buffer.sub tmp_bytes 224ul 64ul in
  let a      = Buffer.sub apre 0ul 32ul in
  Hacl.Impl.Load56.load_32_bytes aq a;
  Hacl.Impl.BignumQ.Mul.mul_modq ha h aq;
  Hacl.Impl.BignumQ.Mul.add_modq s r ha;
  Hacl.Impl.Store56.store_56 s' s

  (* copy_bytes (Buffer.sub signature 0ul 32ul) rs' 32ul; *)
  (* copy_bytes (Buffer.sub signature 32ul 32ul) s' 32ul; *)
  (* let h'' = ST.get() in *)
  (* lemma_append2 h'' signature 32ul 32ul; *)
  (* admit(); *)
  (* (\* blit rs' 0ul signature 0ul 32ul; *\) *)
  (* (\* blit s' 0ul signature 32ul 32ul; *\) *)
  (* pop_frame() *)



(* [@ "substitute"] *)
(* private *)
(* val sign__: *)
(*   signature:hint8_p{length signature = 64} -> *)
(*   secret:hint8_p{length secret = 32} -> *)
(*   msg:hint8_p{length msg < pow2 32 - 64} -> *)
(*   len:UInt32.t{UInt32.v len = length msg} -> *)
(*   g:point -> *)
(*   tmp_bytes:hint8_p{length tmp_bytes = 352 + UInt32.v len} -> *)
(*   tmp_ints:buffer Hacl.UInt64.t{length tmp_ints = 65} -> *)
(*   Stack unit *)
(*     (requires (fun h -> live h signature /\ live h msg /\ live h secret /\ live h g /\  *)
(*       live h tmp_bytes /\ live h tmp_ints /\ as_point h g == Spec.Ed25519.g /\ *)
(*       as_seq h (Buffer.sub tmp_bytes 64ul len) == as_seq h msg)) *)
(*     (ensures (fun h0 _ h1 -> live h0 signature /\ live h0 msg /\ live h0 secret /\ *)
(*       live h1 signature /\ modifies_3 signature tmp_bytes tmp_ints h0 h1 /\ *)
(*       h1.[signature] == Spec.Ed25519.sign h0.[secret] h0.[msg])) *)


(* #reset-options "--max_fuel 0 --z3rlimit 200" *)

(* let sign__ signature secret msg len g tmp_bytes tmp_ints = *)
(*   (\* push_frame(); *\) *)
(*   let tmpa = Buffer.sub tmp_ints 0ul  20ul in *)
(*   let r    = Buffer.sub tmp_ints 20ul 5ul  in *)
(*   let r'   = Buffer.sub tmp_ints 25ul 20ul in *)
(*   let aq   = Buffer.sub tmp_ints 45ul 5ul  in *)
(*   let ha   = Buffer.sub tmp_ints 50ul 5ul  in *)
(*   let s    = Buffer.sub tmp_ints 55ul 5ul  in *)
(*   let h    = Buffer.sub tmp_ints 60ul 5ul  in *)
(*   let prefix_at_message = Buffer.sub tmp_bytes 0ul FStar.UInt32.(64ul +^ len) in *)
(*   let tmp_bytes         = Buffer.offset tmp_bytes FStar.UInt32.(64ul +^ len) in *)
(*   let buf  = Buffer.sub tmp_bytes 0ul   96ul in *)
(*   let a''  = Buffer.sub tmp_bytes 96ul  32ul in *)
(*   let rb   = Buffer.sub tmp_bytes 128ul 32ul in *)
(*   let rs'  = Buffer.sub tmp_bytes 160ul 32ul in *)
(*   let s'   = Buffer.sub tmp_bytes 192ul 32ul in *)
(*   let apre = Buffer.sub tmp_bytes 224ul 64ul in *)
(*   (\* Hacl.Impl.Ed25519.SecretExpand.secret_expand apre secret; *\) *)
(*   (\* let a      = Buffer.sub apre 0ul 32ul in *\) *)
(*   (\* let prefix = Buffer.sub apre 32ul 64ul in *\) *)
(*   (\* point_mul_compress a'' a g; *\) *)
(*   sign_step_1 signature secret msg len g tmp_bytes tmp_ints; *)
(*   (\* TODO: use an incremental version of SHA instead so as to minimize *)
(*   the copies and enable compilation with CompCert *\) *)

(*   (\* let prefix_at_msg = Buffer.sub prefix_at_message 32ul FStar.UInt32.(32ul +^ len) in *\) *)
(*   (\* let message       = Buffer.sub prefix_at_msg 32ul len in *\) *)
(*   (\* let prefix'       = Buffer.sub prefix_at_msg 0ul 32ul in *\) *)
(*   (\* copy_bytes prefix' prefix 32ul; *\) *)
(*   (\* let h0 = ST.get() in *\) *)
(*   (\* lemma_append2 h0 prefix_at_msg 32ul len; *\) *)
(*   (\* Hacl.Impl.SHA512.ModQ.sha512_modq r prefix_at_msg (len+^32ul); *\) *)
(*   sign_step_2 signature secret msg len g tmp_bytes tmp_ints; *)


(*   sign_step_3 signature secret msg len g tmp_bytes tmp_ints; *)

(*   (\* Hacl.Impl.Store56.store_56 rb r; *\) *)
(*   (\* point_mul_compress rs' rb g; *\) *)
(*   (\* Hacl.Impl.Ed25519.Ladder.point_mul r' rb g; *\) *)
(*   (\* Hacl.Impl.Ed25519.PointCompress.point_compress rs' r'; *\) *)

(*   (\* let rs_bytes = Buffer.sub prefix_at_message 0ul  32ul in *\) *)
(*   (\* let a_bytes  = Buffer.sub prefix_at_message 32ul 32ul in *\) *)
(*   (\* copy_bytes rs_bytes rs' 32ul; *\) *)
(*   (\* copy_bytes a_bytes a'' 32ul; *\) *)
(*   (\* (\\* blit rs'  0ul prefix_at_message 0ul 32ul; *\\) *\) *)
(*   (\* (\\* blit a''  0ul prefix_at_message 32ul 32ul; *\\) *\) *)
(*   (\* let h' = ST.get() in *\) *)
(*   (\* lemma_append h' prefix_at_message 32ul 32ul len; *\) *)
(*   (\* Hacl.Impl.SHA512.ModQ.sha512_modq h prefix_at_message (len+^64ul); *\) *)

(*   sign_step_3 signature secret msg len g tmp_bytes tmp_ints; *)

(*   sign_step_4 signature secret msg len g tmp_bytes tmp_ints; *)

(*   (\* Hacl.Impl.Load56.load_32_bytes aq a; *\) *)
(*   (\* Hacl.Impl.BignumQ.Mul.mul_modq ha h aq; *\) *)
(*   (\* Hacl.Impl.BignumQ.Mul.add_modq s r ha; *\) *)
(*   (\* Hacl.Impl.Store56.store_56 s' s; *\) *)

(*   copy_bytes (Buffer.sub signature 0ul 32ul) rs' 32ul; *)
(*   copy_bytes (Buffer.sub signature 32ul 32ul) s' 32ul; *)
(*   let h'' = ST.get() in *)
(*   lemma_append2 h'' signature 32ul 32ul; *)
(*   () *)
(*   (\* pop_frame() *\) *)


(* #reset-options "--max_fuel 0 --z3rlimit 20" *)

(* val sign_: *)
(*   signature:hint8_p{length signature = 64} -> *)
(*   secret:hint8_p{length secret = 32} -> *)
(*   msg:hint8_p{length msg < pow2 32 - 64} -> *)
(*   len:UInt32.t{UInt32.v len = length msg /\ UInt32.v len + 352 < pow2 32} -> *)
(*   g:point{disjoint g signature} -> *)
(*   Stack unit *)
(*     (requires (fun h -> live h signature /\ live h msg /\ live h secret /\ live h g /\  *)
(*       as_point h g == Spec.Ed25519.g)) *)
(*     (ensures (fun h0 _ h1 -> live h0 signature /\ live h0 msg /\ live h0 secret /\ *)
(*       live h1 signature /\ modifies_1 signature h0 h1 /\ *)
(*       h1.[signature] == Spec.Ed25519.sign h0.[secret] h0.[msg])) *)

(* #reset-options "--max_fuel 0 --z3rlimit 50" *)

(* let sign_ signature secret msg len g = *)
(*   push_frame(); *)
(*   let tmp_bytes = Buffer.create 0uy (352ul +^ len) in *)
(*   push_frame(); *)
(*   let h0 = ST.get() in *)
(*   let tmp_ints  = Buffer.create 0uL 65ul in *)
(*   let msg'      = Buffer.sub tmp_bytes 64ul len in *)
(*   let h1 = ST.get() in *)
(*   no_upd_lemma_0 h0 h1 g; *)
(*   no_upd_lemma_0 h0 h1 msg; *)
(*   copy_bytes msg' msg len; *)
(*   let h2 = ST.get() in *)
(*   no_upd_lemma_1 h1 h2 msg' g; *)
(*   assert(modifies_0 h0 h2); *)
(*   sign__ signature secret msg len g tmp_bytes tmp_ints; *)
(*   let h3 = ST.get() in *)
(*   pop_frame(); *)
(*   pop_frame() *)


(* val sign: *)
(*   signature:hint8_p{length signature = 64} -> *)
(*   secret:hint8_p{length secret = 32} -> *)
(*   msg:hint8_p{length msg < pow2 32 - 64} -> *)
(*   len:UInt32.t{UInt32.v len = length msg /\ UInt32.v len + 352 < pow2 32} -> *)
(*   Stack unit *)
(*     (requires (fun h -> live h signature /\ live h msg /\ live h secret)) *)
(*     (ensures (fun h0 _ h1 -> live h0 signature /\ live h0 msg /\ live h0 secret /\ *)
(*       live h1 signature /\ modifies_1 signature h0 h1 /\ *)
(*       h1.[signature] == Spec.Ed25519.sign h0.[secret] h0.[msg])) *)

(* #reset-options "--max_fuel 0 --z3rlimit 20" *)

(* let sign signature secret msg len = *)
(*   push_frame(); *)
(*   let h0 = ST.get() in *)
(*   let g = create 0uL 20ul in *)
(*   Hacl.Impl.Ed25519.G.make_g g; *)
(*   let h1 = ST.get() in *)
(*   assume (as_point h1 g == Spec.Ed25519.g); *)
(*   sign_ signature secret msg len g; *)
(*   let h2 = ST.get() in *)
(*   pop_frame() *)
