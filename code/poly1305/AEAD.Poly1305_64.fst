module AEAD.Poly1305_64


open FStar.Mul
open FStar.ST
open FStar.Ghost
open FStar.Seq
open FStar.HyperStack
open FStar.Endianness
open FStar.Buffer

open Hacl.Spec.Endianness
open Hacl.Endianness

open Hacl.Cast
open Hacl.Bignum.Parameters
open Hacl.Spec.Bignum.Bigint
open Hacl.Spec.Bignum.AddAndMultiply
open Hacl.Spe.Poly1305_64
open Hacl.Bignum.AddAndMultiply
open Hacl.Impl.Poly1305_64

module H8   = Hacl.UInt8
module Limb = Hacl.Bignum.Limb
module Wide = Hacl.Bignum.Wide
module U8   = FStar.UInt8
module U32  = FStar.UInt32
module U64  = FStar.UInt64


module Spec = Spec.Chacha20Poly1305

#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 100"


#set-options "--lax"

val pad_16_bytes:
  input:uint8_p ->
  len:U32.t{length input = U32.v len /\ U32.v len < 16 /\ U32.v len > 0} ->
  StackInline (uint8_p)
    (requires (fun h -> live h input))
    (ensures (fun h0 output h1 -> live h0 input /\ live h1 output /\ frameOf output = h1.tip
      /\ modifies_0 h0 h1 /\ length output = 16
      /\ (let o = as_seq h1 output in let i = as_seq h0 input in
         o == Spec.pad_16 i)))
let pad_16_bytes input len =
  let h0 = ST.get() in
  let b = Buffer.create (uint8_to_sint8 0uy) 16ul in
  Buffer.blit input 0ul b 0ul len;
  let h = ST.get() in
  no_upd_lemma_0 h0 h input;
  Seq.lemma_eq_intro (as_seq h input) (Seq.slice (as_seq h input) 0 (U32.v len));
  Seq.lemma_eq_intro (Seq.slice (as_seq h b) (U32.v len) 16) (Seq.create (16 - U32.v len) (uint8_to_sint8 0uy));
  Seq.lemma_eq_intro (as_seq h b) (Spec.pad_16 (as_seq h0 input));
  b


module Poly = Hacl.Standalone.Poly1305_64
module Impl = Hacl.Impl.Poly1305_64

val poly1305_alloc:
  unit -> StackInline poly1305_state
    (requires (fun h -> True))
    (ensures (fun h0 st h1 -> modifies_0 h0 h1 /\ live_st h1 st))
let poly1305_alloc () = Impl.alloc ()


val poly1305_blocks_init:
  st:poly1305_state ->
  input:uint8_p{disjoint st.r input /\ disjoint st.h input} ->
  len:U32.t{U32.v len = length input} ->
  k:uint8_p{length k = 32 /\ disjoint k st.r /\ disjoint k st.h} ->
  Stack unit
    (requires (fun h -> live_st h st /\ live h input /\ live h k))
    (ensures (fun h0 _ h1 -> live_st h1 st /\ live h0 input /\ live h0 k /\ modifies_2 st.r st.h h0 h1))
let poly1305_blocks_init st input len k =
  let l = Impl.poly1305_init_ st (Buffer.sub k 0ul 16ul) in
  let len_16 = U32.(len >>^ 4ul) in
  let rem_16 = U32.(len &^ 4ul)  in
  let l = Poly.poly1305_blocks l st (Buffer.sub input 0ul U32.(16ul *^ len_16)) (Int.Cast.uint32_to_uint64 len_16) in
  if U32.(rem_16 =^ 0ul) then ()
  else (
    push_frame();
    let b = pad_16_bytes (Buffer.offset input U32.(len -^ rem_16)) rem_16 in
    let _ = poly1305_update l st b in
    pop_frame()
  )


let fake_log : Impl.log_t = Ghost.hide (Seq.createEmpty)


val poly1305_blocks_continue:
  st:poly1305_state ->
  input:uint8_p{disjoint st.h input} ->
  len:U32.t{U32.v len = length input} ->
  Stack unit
    (requires (fun h -> live_st h st /\ live h input))
    (ensures (fun h0 _ h1 -> live_st h1 st /\ live h0 input /\ modifies_1 st.h h0 h1))
let poly1305_blocks_continue st input len =
  let len_16 = U32.(len >>^ 4ul) in
  let rem_16 = U32.(len &^ 4ul)  in
  let l = Poly.poly1305_blocks fake_log st (Buffer.sub input 0ul U32.(16ul *^ len_16)) (Int.Cast.uint32_to_uint64 len_16) in
  if U32.(rem_16 =^ 0ul) then ()
  else (
    push_frame();
    let b = pad_16_bytes (Buffer.offset input U32.(len -^ rem_16)) rem_16 in
    let _ = poly1305_update l st b in
    pop_frame()
  )


val poly1305_blocks_finish:
  st:poly1305_state ->
  input:uint8_p{disjoint st.h input} ->
  mac:uint8_p{disjoint st.h mac /\ disjoint mac input} ->
  key_s:uint8_p{disjoint key_s st.h /\ disjoint key_s mac} ->
  Stack unit
    (requires (fun h -> live_st h st /\ live h input /\ live h mac))
    (ensures (fun h0 _ h1 -> live h0 input /\ modifies_2 mac st.h h0 h1 /\ live h1 mac))
let poly1305_blocks_finish st input mac key_s =
  let _ = Impl.poly1305_update fake_log st input in
  let _ = Impl.poly1305_update_last fake_log st (Buffer.offset input 16ul) 0uL in
  let _ = Impl.poly1305_finish st mac key_s in
  ()


