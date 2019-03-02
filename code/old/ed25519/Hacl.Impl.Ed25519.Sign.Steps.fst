module Hacl.Impl.Ed25519.Sign.Steps

module ST = FStar.HyperStack.ST

open FStar.HyperStack.All


open FStar.Mul
open FStar.Buffer
open FStar.UInt32

open Hacl.Impl.Ed25519.ExtPoint


let hint8_p = buffer Hacl.UInt8.t

let op_String_Access (h:HyperStack.mem) (b:hint8_p{live h b}) =
  Hacl.Spec.Endianness.reveal_sbytes (as_seq h b)



#reset-options "--max_fuel 0 --z3rlimit 200"

private
val lemma_point_inv:
  h:HyperStack.mem -> p:point{live h p} -> h':HyperStack.mem -> p':point{live h' p'} ->
  Lemma (requires (as_seq h p == as_seq h' p' /\ point_inv h p))
        (ensures (point_inv h' p'))
let lemma_point_inv h p h' p' = ()


#reset-options "--max_fuel 0 --z3rlimit 20"

inline_for_extraction
private
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
  let tmp:point = Buffer.create (Hacl.Cast.uint64_to_sint64 0uL) 20ul in
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


open Hacl.Spec.Endianness

inline_for_extraction
private
val point_mul_g:
  result:point ->
  scalar:buffer Hacl.UInt8.t{length scalar = 32 /\ disjoint result scalar} ->
  Stack unit
  (requires (fun h -> Buffer.live h scalar /\ live h result))
  (ensures (fun h0 _ h1 -> Buffer.live h0 scalar /\ live h0 result /\
    live h1 result /\ modifies_1 result h0 h1 /\ point_inv h1 result /\
    (let r = as_point h1 result in
     let n  = reveal_sbytes (as_seq h0 scalar) in
     r == Spec.Ed25519.point_mul n Spec.Ed25519.g) ))

#reset-options "--max_fuel 0 --z3rlimit 20"

let point_mul_g result scalar =
  push_frame();
  let h0 = ST.get() in
  let g = create (Hacl.Cast.uint64_to_sint64 0uL) 20ul in
  Hacl.Impl.Ed25519.G.make_g g;
  let h1 = ST.get() in
  no_upd_lemma_0 h0 h1 scalar;
  Hacl.Impl.Ed25519.Ladder.point_mul result scalar g;
  let h2 = ST.get() in
  no_upd_lemma_1 h1 h2 result scalar;
  pop_frame()


#reset-options "--max_fuel 0 --z3rlimit 20"

inline_for_extraction
val point_mul_g_compress:
  out:hint8_p{length out = 32} ->
  s:hint8_p{length s = 32 /\ disjoint s out} ->
  Stack unit
    (requires (fun h -> live h out /\ live h s))
    (ensures (fun h0 _ h1 -> live h1 out /\ live h0 s /\ modifies_1 out h0 h1 /\ live h1 s /\
      h1.[out] == Spec.Ed25519.(point_compress (point_mul h0.[s] g))))

#reset-options "--max_fuel 0 --z3rlimit 200"

let point_mul_g_compress out s =
  let h = ST.get() in
  push_frame();
  let h0 = ST.get() in
  let tmp:point = Buffer.create (Hacl.Cast.uint64_to_sint64 0uL) 20ul in
  let h' = ST.get() in
  point_mul_g tmp s;
  let h1 = ST.get() in
  no_upd_lemma_0 h0 h1 s;
  Hacl.Impl.Ed25519.PointCompress.point_compress out tmp;
  let h2 = ST.get() in
  no_upd_lemma_1 h1 h2 out s;
  pop_frame()


#reset-options "--max_fuel 0 --z3rlimit 20"

inline_for_extraction
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

inline_for_extraction
val sign_step_1:
  secret:hint8_p{length secret = 32} ->
  tmp_bytes:hint8_p{length tmp_bytes = 352 /\ disjoint tmp_bytes secret} ->
  Stack unit
    (requires (fun h -> live h secret /\  live h tmp_bytes))
    (ensures (fun h0 _ h1 -> live h0 secret /\ live h0 tmp_bytes /\ live h1 tmp_bytes /\
      modifies_1 tmp_bytes h0 h1 /\ (
        let a''  = Buffer.sub tmp_bytes 96ul  32ul in
        let apre = Buffer.sub tmp_bytes 224ul 64ul in
        let a      = Buffer.sub apre 0ul 32ul in
        let prefix = Buffer.sub apre 32ul 32ul in
        (reveal_sbytes (as_seq h1 a), reveal_sbytes (as_seq h1 prefix)) == Spec.Ed25519.(secret_expand (reveal_sbytes (as_seq h0 secret))) /\
        (reveal_sbytes (as_seq h1 a'') == Spec.Ed25519.(point_compress (point_mul (reveal_sbytes (as_seq h1 a)) g))))
   ))


#reset-options "--max_fuel 0 --z3rlimit 200"

let sign_step_1 secret tmp_bytes =
  let a''  = Buffer.sub tmp_bytes 96ul  32ul in
  let apre = Buffer.sub tmp_bytes 224ul 64ul in
  let a      = Buffer.sub apre 0ul 32ul in
  let prefix = Buffer.sub apre 32ul 32ul in
  let h0 = ST.get() in
  Hacl.Impl.Ed25519.SecretExpand.secret_expand apre secret;
  let h1 = ST.get() in
  point_mul_g_compress a'' a;
  let h2 = ST.get() in
  no_upd_lemma_1 h1 h2 a'' a;
  no_upd_lemma_1 h1 h2 a'' prefix


#reset-options "--max_fuel 0 --z3rlimit 20"

inline_for_extraction
val sign_step_2:
  msg:hint8_p{length msg < pow2 32 - 64} ->
  len:UInt32.t{UInt32.v len = length msg} ->
  tmp_bytes:hint8_p{length tmp_bytes = 352 /\ disjoint tmp_bytes msg} ->
  tmp_ints:buffer Hacl.UInt64.t{length tmp_ints = 65 /\ disjoint tmp_bytes tmp_ints /\ disjoint tmp_ints msg} ->
  Stack unit
    (requires (fun h -> live h msg /\ live h tmp_bytes /\ live h tmp_ints))
    (ensures (fun h0 _ h1 -> live h0 msg /\ live h0 tmp_bytes /\ live h1 tmp_bytes /\ live h0 tmp_ints /\
      live h1 tmp_ints /\ modifies_1 tmp_ints h0 h1 /\ (
        let r    = Buffer.sub tmp_ints 20ul 5ul  in
        let a''  = Buffer.sub tmp_bytes 96ul  32ul in
        let rb   = Buffer.sub tmp_bytes 128ul 32ul in
        let apre = Buffer.sub tmp_bytes 224ul 64ul in
        let a      = Buffer.sub apre 0ul  32ul in
        let prefix = Buffer.sub apre 32ul 32ul in
        let s = reveal_h64s (as_seq h1 r) in
        Hacl.Spec.BignumQ.Eval.eval_q s ==
          Spec.Ed25519.(sha512_modq FStar.Seq.(reveal_sbytes (as_seq h0 prefix @| as_seq h0 msg))) /\
        Hacl.Impl.BignumQ.Mul.within_56 h1 r /\
        Hacl.Spec.BignumQ.Eval.eval_q s < pow2 256 /\ UInt64.v (Seq.index s 0) < pow2 56 /\
        UInt64.v (Seq.index s 1) < pow2 56 /\ UInt64.v (Seq.index s 2) < pow2 56 /\
        UInt64.v (Seq.index s 3) < pow2 56 /\ UInt64.v (Seq.index s 4) < pow2 32 /\
        as_seq h1 a == as_seq h0 a /\
        as_seq h1 a'' == as_seq h0 a''
        )
    ))


#reset-options "--max_fuel 0 --z3rlimit 20"

let sign_step_2 msg len tmp_bytes tmp_ints =
  assert_norm(pow2 56 = 0x100000000000000);
  assert_norm(Spec.Ed25519.q = 0x1000000000000000000000000000000014def9dea2f79cd65812631a5cf5d3ed);
  assert_norm(pow2 256 = 0x10000000000000000000000000000000000000000000000000000000000000000);
  let r      = Buffer.sub tmp_ints 20ul 5ul  in
  let a''    = Buffer.sub tmp_bytes 96ul  32ul in
  let apre   = Buffer.sub tmp_bytes 224ul 64ul in
  let a      = Buffer.sub apre 0ul 32ul in
  let prefix = Buffer.sub apre 32ul 32ul in 
  let h0 = ST.get() in
  Hacl.Impl.SHA512.ModQ.sha512_modq_pre r prefix msg len;
  let h1 = ST.get() in
  no_upd_lemma_1 h0 h1 r a;
  no_upd_lemma_1 h0 h1 r a'';
  no_upd_lemma_1 h0 h1 r tmp_bytes


#reset-options "--max_fuel 0 --z3rlimit 50"

inline_for_extraction
val sign_step_4:
  msg:hint8_p{length msg < pow2 32 - 64} ->
  len:UInt32.t{UInt32.v len = length msg} ->
  tmp_bytes:hint8_p{length tmp_bytes = 352 /\ disjoint tmp_bytes msg} ->
  tmp_ints:buffer Hacl.UInt64.t{length tmp_ints = 65 /\ disjoint tmp_bytes tmp_ints /\ disjoint tmp_ints msg} ->
  Stack unit
    (requires (fun h -> live h msg /\ live h tmp_bytes /\ live h tmp_ints))
    (ensures (fun h0 _ h1 -> live h0 msg /\ live h0 tmp_bytes /\ live h1 tmp_bytes /\ live h0 tmp_ints /\
      live h1 tmp_ints /\ modifies_1 tmp_ints h0 h1 /\ (
        let tmpa = Buffer.sub tmp_ints 0ul  20ul in
        let r    = Buffer.sub tmp_ints 20ul 5ul  in
        let r'   = Buffer.sub tmp_ints 25ul 20ul in
        let aq   = Buffer.sub tmp_ints 45ul 5ul  in
        let ha   = Buffer.sub tmp_ints 50ul 5ul  in
        let s    = Buffer.sub tmp_ints 55ul 5ul  in
        let h    = Buffer.sub tmp_ints 60ul 5ul  in
        let a''  = Buffer.sub tmp_bytes 96ul  32ul in
        let rb   = Buffer.sub tmp_bytes 128ul 32ul in
        let rs'  = Buffer.sub tmp_bytes 160ul 32ul in
        let s'   = Buffer.sub tmp_bytes 192ul 32ul in
        let apre = Buffer.sub tmp_bytes 224ul 64ul in
        let a      = Buffer.sub apre 0ul 32ul in
        let prefix = Buffer.sub apre 32ul 32ul in
        Hacl.Spec.BignumQ.Eval.eval_q (reveal_h64s (as_seq h1 h)) ==
          Spec.Ed25519.(sha512_modq FStar.Seq.(reveal_sbytes (as_seq h0 rs' @| as_seq h0 a'' @| as_seq h0 msg))) /\
        Hacl.Impl.BignumQ.Mul.within_56 h1 h /\
        as_seq h1 a == as_seq h0 a /\
        as_seq h1 rs' == as_seq h0 rs' /\
        as_seq h1 r == as_seq h0 r
        )
    ))


#reset-options "--max_fuel 0 --z3rlimit 20"

(* val append_before_sha: *)
(*   msg:hint8_p -> *)
(*   len:UInt32.t{UInt32.v len = length msg} -> *)
(*   msg':hint8_p{length msg' = 64 + UInt32.v len /\ disjoint msg msg'} -> *)
(*   rs':hint8_p{length rs' = 32 /\ disjoint rs' msg'} -> *)
(*   a'':hint8_p{length a'' = 32 /\ disjoint a'' msg'} -> *)
(*   Stack unit *)
(*     (requires (fun h -> live h msg' /\ live h msg /\ live h rs' /\ live h a'' /\ *)
(*       as_seq h (Buffer.sub msg' 64ul len) == as_seq h msg)) *)
(*     (ensures (fun h0 _ h1 -> live h1 msg' /\ modifies_1 msg' h0 h1 /\ live h0 msg /\ live h0 rs' /\ *)
(*       live h0 a'' /\ *)
(*       as_seq h1 msg' == FStar.Seq.(as_seq h0 rs' @| as_seq h0 a'' @| as_seq h0 msg))) *)

(* #reset-options "--max_fuel 0 --z3rlimit 10" *)

(* let append_before_sha msg len msg' rs' a'' = *)
(*   let h0 = ST.get() in *)
(*   copy_bytes (Buffer.sub msg' 0ul 32ul) rs' 32ul; *)
(*   let h1 = ST.get() in *)
(*   no_upd_lemma_1 h0 h1 (Buffer.sub msg' 0ul 32ul) (Buffer.sub msg' 64ul len); *)
(*   no_upd_lemma_1 h0 h1 (Buffer.sub msg' 0ul 32ul) a''; *)
(*   copy_bytes (Buffer.sub msg' 32ul 32ul) a'' 32ul; *)
(*   let h2 = ST.get() in *)
(*   no_upd_lemma_1 h1 h2 (Buffer.sub msg' 32ul 32ul) (Buffer.sub msg' 64ul len); *)
(*   no_upd_lemma_1 h1 h2 (Buffer.sub msg' 32ul 32ul) (Buffer.sub msg' 0ul 32ul); *)
(*   lemma_append h2 msg' 32ul 32ul len *)


(* #reset-options "--max_fuel 0 --z3rlimit 200" *)

let sign_step_4 msg len tmp_bytes tmp_ints =
  let tmp_bytes' = tmp_bytes in
  let r    = Buffer.sub tmp_ints 20ul 5ul  in
  let h    = Buffer.sub tmp_ints 60ul 5ul  in
  let a''  = Buffer.sub tmp_bytes 96ul  32ul in
  let rb   = Buffer.sub tmp_bytes 128ul 32ul in
  let rs'  = Buffer.sub tmp_bytes 160ul 32ul in
  let apre = Buffer.sub tmp_bytes 224ul 64ul in
  let a      = Buffer.sub apre 0ul 32ul in
  let h0 = ST.get() in
  Hacl.Impl.SHA512.ModQ.sha512_modq_pre_pre2 h rs' a'' msg len;
  let h1 = ST.get() in
  no_upd_lemma_1 h0 h1 h r;
  no_upd_lemma_1 h0 h1 h rs';
  no_upd_lemma_1 h0 h1 h a;
  ()


#reset-options "--max_fuel 0 --z3rlimit 20"

val sign_step_3:
  tmp_bytes:hint8_p{length tmp_bytes = 352} ->
  tmp_ints:buffer Hacl.UInt64.t{length tmp_ints = 65 /\ disjoint tmp_bytes tmp_ints} ->
  Stack unit
    (requires (fun h -> live h tmp_bytes /\ live h tmp_ints /\ (
        let s = as_seq h (Buffer.sub tmp_ints 20ul 5ul) in
        Hacl.Spec.BignumQ.Eval.eval_q (reveal_h64s s) < pow2 256 /\ Hacl.UInt64.v (Seq.index s 0) < pow2 56 /\
        Hacl.UInt64.v (Seq.index s 1) < pow2 56 /\ Hacl.UInt64.v (Seq.index s 2) < pow2 56 /\
        Hacl.UInt64.v (Seq.index s 3) < pow2 56 /\ Hacl.UInt64.v (Seq.index s 4) < pow2 32)
      ))
    (ensures (fun h0 _ h1 -> live h0 tmp_bytes /\ live h1 tmp_bytes /\
      live h0 tmp_ints /\ live h1 tmp_ints /\ modifies_1 tmp_bytes h0 h1 /\ (
        let tmpa = Buffer.sub tmp_ints 0ul  20ul in
        let r    = Buffer.sub tmp_ints 20ul 5ul  in
        let r'   = Buffer.sub tmp_ints 25ul 20ul in
        let aq   = Buffer.sub tmp_ints 45ul 5ul  in
        let ha   = Buffer.sub tmp_ints 50ul 5ul  in
        let s    = Buffer.sub tmp_ints 55ul 5ul  in
        let h    = Buffer.sub tmp_ints 60ul 5ul  in
        let buf  = Buffer.sub tmp_bytes 0ul   96ul in
        let a''  = Buffer.sub tmp_bytes 96ul  32ul in
        let rb   = Buffer.sub tmp_bytes 128ul 32ul in
        let rs'  = Buffer.sub tmp_bytes 160ul 32ul in
        let s'   = Buffer.sub tmp_bytes 192ul 32ul in
        let apre = Buffer.sub tmp_bytes 224ul 64ul in
        let a      = Buffer.sub apre 0ul 32ul in
        let prefix = Buffer.sub apre 32ul 32ul in
        Hacl.Spec.BignumQ.Eval.eval_q (reveal_h64s (as_seq h0 r)) < pow2 256 /\
        reveal_sbytes (as_seq h1 rs') == Spec.Ed25519.(
            let r = Hacl.Spec.BignumQ.Eval.eval_q (reveal_h64s (as_seq h0 r)) in
            let x = point_mul (FStar.Old.Endianness.little_bytes 32ul r) g in
            point_compress x) /\
        as_seq h1 r == as_seq h0 r /\
        as_seq h1 a'' == as_seq h0 a'' /\
        as_seq h1 a == as_seq h0 a
        )
    ))

#reset-options "--max_fuel 0 --z3rlimit 100"

let sign_step_3 tmp_bytes tmp_ints =
  let a''  = Buffer.sub tmp_bytes 96ul  32ul in
  let apre = Buffer.sub tmp_bytes 224ul 64ul in
  let a      = Buffer.sub apre 0ul 32ul in
  push_frame();
  let h0 = ST.get() in
  let rb = create (Hacl.Cast.uint8_to_sint8 0uy) 32ul in
  let h1 = ST.get() in
  let r    = Buffer.sub tmp_ints 20ul 5ul  in
  no_upd_lemma_0 h0 h1 r;
  no_upd_lemma_0 h0 h1 a;
  no_upd_lemma_0 h0 h1 a'';
  let rs'  = Buffer.sub tmp_bytes 160ul 32ul in
  Hacl.Impl.Store56.store_56 rb r;
  let h2 = ST.get() in
  FStar.Old.Endianness.lemma_little_endian_inj (reveal_sbytes (as_seq h2 rb))
                                     (FStar.Old.Endianness.little_bytes 32ul (Hacl.Spec.BignumQ.Eval.eval_q (reveal_h64s (as_seq h0 r))));
  no_upd_lemma_0 h0 h2 r;
  no_upd_lemma_0 h0 h2 a;
  no_upd_lemma_0 h0 h2 a'';
  no_upd_lemma_0 h0 h2 tmp_ints;
  point_mul_g_compress rs' rb;
  let h3 = ST.get() in
  no_upd_lemma_1 h2 h3 rs' r;
  no_upd_lemma_1 h2 h3 rs' a;
  no_upd_lemma_1 h2 h3 rs' a'';
  pop_frame()


#reset-options "--max_fuel 0 --z3rlimit 20"

val sign_step_5:
  tmp_bytes:hint8_p{length tmp_bytes = 352} ->
  tmp_ints:buffer Hacl.UInt64.t{length tmp_ints = 65 /\ disjoint tmp_bytes tmp_ints} ->
  Stack unit
    (requires (fun h -> live h tmp_bytes /\ live h tmp_ints /\ (
      let h'    = Buffer.sub tmp_ints 60ul 5ul in
      let r    = Buffer.sub tmp_ints 20ul 5ul  in
      Hacl.Impl.BignumQ.Mul.within_56 h r /\ Hacl.Spec.BignumQ.Eval.eval_q (reveal_h64s (as_seq h r)) < 0x1000000000000000000000000000000014def9dea2f79cd65812631a5cf5d3ed /\
      Hacl.Impl.BignumQ.Mul.within_56 h h' /\ Hacl.Spec.BignumQ.Eval.eval_q (reveal_h64s (as_seq h h')) < pow2 256)
    ))
    (ensures (fun h0 _ h1 -> live h0 tmp_bytes /\ live h1 tmp_bytes /\
      live h0 tmp_ints /\ live h1 tmp_ints /\ modifies_2 tmp_bytes tmp_ints h0 h1 /\ (
        let tmpa = Buffer.sub tmp_ints 0ul  20ul in
        let r    = Buffer.sub tmp_ints 20ul 5ul  in
        let r'   = Buffer.sub tmp_ints 25ul 20ul in
        let aq   = Buffer.sub tmp_ints 45ul 5ul  in
        let ha   = Buffer.sub tmp_ints 50ul 5ul  in
        let s    = Buffer.sub tmp_ints 55ul 5ul  in
        let h    = Buffer.sub tmp_ints 60ul 5ul  in
        let buf  = Buffer.sub tmp_bytes 0ul   96ul in
        let a''  = Buffer.sub tmp_bytes 96ul  32ul in
        let rb   = Buffer.sub tmp_bytes 128ul 32ul in
        let rs'  = Buffer.sub tmp_bytes 160ul 32ul in
        let s'   = Buffer.sub tmp_bytes 192ul 32ul in
        let apre = Buffer.sub tmp_bytes 224ul 64ul in
        let a      = Buffer.sub apre 0ul 32ul in
        let prefix = Buffer.sub apre 32ul 32ul in
        reveal_sbytes (as_seq h1 s') ==
          FStar.Old.Endianness.little_bytes 32ul (Spec.Ed25519.((Hacl.Spec.BignumQ.Eval.eval_q (reveal_h64s (as_seq h0 r)) +
                          ((Hacl.Spec.BignumQ.Eval.eval_q (reveal_h64s (as_seq h0 h)) * (hlittle_endian (as_seq h0 a))) % q)) % q)) /\
        as_seq h1 rs' == as_seq h0 rs'
        )
    ))


#reset-options "--max_fuel 0 --z3rlimit 200"

let sign_step_5 tmp_bytes tmp_ints =
  assert_norm(pow2 56 = 0x100000000000000);
  assert_norm(Spec.Ed25519.q = 0x1000000000000000000000000000000014def9dea2f79cd65812631a5cf5d3ed);
  assert_norm(pow2 256 = 0x10000000000000000000000000000000000000000000000000000000000000000);
  let r    = Buffer.sub tmp_ints 20ul 5ul  in
  let aq   = Buffer.sub tmp_ints 45ul 5ul  in
  let ha   = Buffer.sub tmp_ints 50ul 5ul  in
  let s    = Buffer.sub tmp_ints 55ul 5ul  in
  let h    = Buffer.sub tmp_ints 60ul 5ul  in
  let s'   = Buffer.sub tmp_bytes 192ul 32ul in
  let rs'  = Buffer.sub tmp_bytes 160ul 32ul in
  let a = Buffer.sub tmp_bytes 224ul 32ul in
  let h0 = ST.get() in
  FStar.Old.Endianness.lemma_little_endian_is_bounded (reveal_sbytes (as_seq h0 a));
  Hacl.Impl.Load56.load_32_bytes aq a;
  let h1 = ST.get() in
  assert(Hacl.Spec.BignumQ.Eval.eval_q (reveal_h64s (as_seq h1 aq)) < pow2 256);
  no_upd_lemma_1 h0 h1 aq h;
  no_upd_lemma_1 h0 h1 aq ha;
  no_upd_lemma_1 h0 h1 aq r;
  no_upd_lemma_1 h0 h1 aq rs';
  Hacl.Impl.BignumQ.Mul.mul_modq ha h aq;
  let h2 = ST.get() in
  no_upd_lemma_1 h1 h2 ha r;
  no_upd_lemma_1 h1 h2 ha rs';
  Hacl.Impl.BignumQ.Mul.add_modq s r ha;
  let h3 = ST.get() in
  no_upd_lemma_1 h2 h3 s rs';
  Hacl.Impl.Store56.store_56 s' s;
  let h4 = ST.get() in
  no_upd_lemma_1 h3 h4 s' rs';
  FStar.Old.Endianness.lemma_little_endian_inj (reveal_sbytes (as_seq h4 s')) (FStar.Old.Endianness.little_bytes 32ul (Spec.Ed25519.((Hacl.Spec.BignumQ.Eval.eval_q (reveal_h64s (as_seq h0 r)) +
                          ((Hacl.Spec.BignumQ.Eval.eval_q (reveal_h64s (as_seq h0 h)) * (hlittle_endian (as_seq h0 a))) % q)) % q)));
  ()
