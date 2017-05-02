module Hacl.Impl.Sha512


open FStar.UInt32
open FStar.Buffer

open SHA2_512


#set-options "--lax"

let hint8_p = buffer Hacl.UInt8.t
let op_String_Access h b = Hacl.Spec.Endianness.reveal_sbytes (as_seq h b)


val sha512_pre_msg_1:
  hash:hint8_p{length hash = 64} ->
  prefix:hint8_p{length prefix = 32 /\ disjoint prefix hash} ->
  input:hint8_p{disjoint input hash} ->
  len:UInt32.t{UInt32.v len = length input /\ length input <= 96} ->
  Stack unit
    (requires (fun h -> live h hash /\ live h prefix /\ live h input))
    (ensures (fun h0 _ h1 -> live h0 hash /\ live h0 prefix /\ live h0 input /\
      live h1 hash /\ live h1 prefix /\ live h1 input /\ modifies_1 hash h0 h1 /\
      as_seq h1 hash == Spec.Ed25519.sha512 FStar.Seq.(as_seq h0 prefix @| as_seq h0 input)))


let sha512_pre_msg_1 h prefix input len =
  push_frame();
  let block = create 0uy 128ul in
  blit prefix 0ul block 0ul 32ul;
  blit input 0ul block 32ul len;
  hash h block (len +^ 32ul);
  pop_frame()


val sha512_pre_msg_2:
  hash:hint8_p{length hash = 64} ->
  prefix:hint8_p{length prefix = 32 /\ disjoint prefix hash} ->
  input:hint8_p{disjoint input hash} ->
  len:UInt32.t{v len = length input /\ length input > 96} ->
  Stack unit
    (requires (fun h -> live h hash /\ live h prefix /\ live h input))
    (ensures (fun h0 _ h1 -> live h0 hash /\ live h0 prefix /\ live h0 input /\
      live h1 hash /\ live h1 prefix /\ live h1 input /\ modifies_1 hash h0 h1 /\
      as_seq h1 hash == Spec.Ed25519.sha512 FStar.Seq.(as_seq h0 prefix @| as_seq h0 input)))

let sha512_pre_msg_2 h prefix input len =
  push_frame();
  let block = create 0uy 128ul in
  blit prefix 0ul block 0ul 32ul;
  blit input  0ul block 32ul 96ul;
  let len'  = len -^ 96ul in
  let nblocks = len' >>^ 7ul in
  let rest    = Int.Cast.uint32_to_uint64 (len' &^ 127ul) in
  let st      = create 0uL 169ul in
  (* let st      = alloc () in *)
  init st;
  update st block;
  update_multi st (Buffer.sub input 96ul (128ul *^ nblocks)) nblocks;
  update_last st (Buffer.offset input (96ul +^ 128ul *^ nblocks)) rest;
  finish st h;
  pop_frame()


val sha512_pre_msg:
  hash:hint8_p{length hash = 64} ->
  prefix:hint8_p{length prefix = 32 /\ disjoint prefix hash} ->
  input:hint8_p{disjoint input hash} ->
  len:UInt32.t{UInt32.v len = length input /\ length input < pow2 32 - 32} ->
  Stack unit
    (requires (fun h -> live h hash /\ live h prefix /\ live h input))
    (ensures (fun h0 _ h1 -> live h0 hash /\ live h0 prefix /\ live h0 input /\
      live h1 hash /\ live h1 prefix /\ live h1 input /\ modifies_1 hash h0 h1 /\
      as_seq h1 hash == Spec.Ed25519.sha512 FStar.Seq.(as_seq h0 prefix @| as_seq h0 input)))


let sha512_pre_msg h prefix input len =
  (* push_frame(); *)
  (* let bla = create 0uy (len +^ 32ul) in *)
  (* blit prefix 0ul bla 0ul 32ul; *)
  (* blit input  0ul bla 32ul len; *)
  (* hash h bla (len +^ 32ul); *)
  (* pop_frame() *)
  if len <=^ 96ul then sha512_pre_msg_1 h prefix input len
  else sha512_pre_msg_2 h prefix input len


val sha512_pre_pre2_msg_1:
  hash:hint8_p{length hash = 64} ->
  prefix:hint8_p{length prefix = 32 /\ disjoint prefix hash} ->
  prefix2:hint8_p{length prefix = 32 /\ disjoint prefix2 hash} ->
  input:hint8_p{disjoint input hash} ->
  len:UInt32.t{UInt32.v len = length input /\ length input <= 64} ->
  Stack unit
    (requires (fun h -> live h hash /\ live h prefix /\ live h input /\ live h prefix2))
    (ensures (fun h0 _ h1 -> live h0 hash /\ live h0 prefix /\ live h0 input /\ live h0 prefix2 /\
      live h1 hash /\ live h1 prefix /\ live h1 prefix2 /\ live h1 input /\ modifies_1 hash h0 h1 /\
      as_seq h1 hash == Spec.Ed25519.sha512 FStar.Seq.(as_seq h0 prefix @| as_seq h0 prefix2 @| as_seq h0 input)))


let sha512_pre_pre2_msg_1 h prefix prefix2 input len =
  push_frame();
  let block = create 0uy 128ul in
  blit prefix 0ul block 0ul 32ul;
  blit prefix2 0ul block 32ul 32ul;
  blit input 0ul block 64ul len;
  hash h block (len +^ 64ul);
  pop_frame()


val sha512_pre_pre2_msg_2:
  hash:hint8_p{length hash = 64} ->
  prefix:hint8_p{length prefix = 32 /\ disjoint prefix hash} ->
  prefix2:hint8_p{length prefix = 32 /\ disjoint prefix2 hash} ->
  input:hint8_p{disjoint input hash} ->
  len:UInt32.t{v len = length input /\ length input > 64} ->
  Stack unit
    (requires (fun h -> live h hash /\ live h prefix /\ live h prefix2 /\ live h input))
    (ensures (fun h0 _ h1 -> live h0 hash /\ live h0 prefix /\ live h0 prefix2 /\ live h0 input /\
      live h1 hash /\ live h1 prefix /\ live h1 prefix2 /\ live h1 input /\ modifies_1 hash h0 h1 /\
      as_seq h1 hash == Spec.Ed25519.sha512 FStar.Seq.(as_seq h0 prefix @| as_seq h0 prefix2 @| as_seq h0 input)))


let sha512_pre_pre2_msg_2 h prefix prefix2 input len =
  push_frame();
  let block = create 0uy 128ul in
  blit prefix 0ul block 0ul 32ul;
  blit prefix2 0ul block 32ul 32ul;
  blit input 0ul block 64ul 64ul;
  let len'  = len -^ 64ul in
  let nblocks = len' >>^ 7ul in
  let rest    = Int.Cast.uint32_to_uint64 (len' &^ 127ul) in
  let st      = create 0uL 169ul in
  init st;
  update st block;
  update_multi st (Buffer.sub input 64ul (128ul *^ nblocks)) nblocks;
  update_last st (Buffer.offset input (64ul +^ 128ul *^ nblocks)) rest;
  finish st h;
  pop_frame()



val sha512_pre_pre2_msg:
  hash:hint8_p{length hash = 64} ->
  prefix:hint8_p{length prefix = 32 /\ disjoint prefix hash} ->
  prefix2:hint8_p{length prefix = 32 /\ disjoint prefix2 hash} ->
  input:hint8_p{disjoint input hash} ->
  len:UInt32.t{UInt32.v len = length input /\ length input < pow2 32 - 64} ->
  Stack unit
    (requires (fun h -> live h hash /\ live h prefix /\ live h prefix2 /\ live h input))
    (ensures (fun h0 _ h1 -> live h0 hash /\ live h0 prefix /\ live h0 input /\
      live h1 hash /\ live h1 prefix /\ live h1 input /\ modifies_1 hash h0 h1 /\
      as_seq h1 hash == Spec.Ed25519.sha512 FStar.Seq.(as_seq h0 prefix @| as_seq h0 prefix2 @| as_seq h0 input)))


let sha512_pre_pre2_msg h prefix prefix2 input len =
  (* push_frame(); *)
  (* let bla = create 0uy (len +^ 64ul) in *)
  (* blit prefix  0ul bla 0ul 32ul; *)
  (* blit prefix2 0ul bla 32ul 32ul; *)
  (* blit input   0ul bla 64ul len; *)
  (* hash h bla (len +^ 64ul); *)
  (* pop_frame() *)
  if len <=^ 64ul then sha512_pre_pre2_msg_1 h prefix prefix2 input len
  else sha512_pre_pre2_msg_2 h prefix prefix2 input len
