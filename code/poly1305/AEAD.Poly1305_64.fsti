module AEAD.Poly1305_64

open FStar.HyperStack.All

module ST = FStar.HyperStack.ST

open FStar.Mul
open FStar.HyperStack.ST
open FStar.Ghost
open FStar.Seq
open FStar.HyperStack
open FStar.Endianness
open FStar.Buffer
open Hacl.Cast
open Spec.Chacha20Poly1305
open Hacl.Spec.Endianness


module H8   = Hacl.UInt8
module U8   = FStar.UInt8
module U32  = FStar.UInt32
module U64  = FStar.UInt64

module I = Hacl.Impl.Poly1305_64.State
module S = Hacl.Spec.Poly1305_64.State

type uint8_p = Buffer.buffer Hacl.UInt8.t
type key = k:uint8_p{length k = 32}

noextract let seval (b:Hacl.Spec.Poly1305_64.State.seqelem) : GTot nat =
  Hacl.Spec.Poly1305_64.State.seval b 
noextract let selem (s:Hacl.Spec.Poly1305_64.State.seqelem) : GTot Spec.Poly1305.elem =
  Hacl.Spec.Poly1305_64.State.selem s
type state = I.poly1305_state

#reset-options "--max_fuel 0 --z3rlimit 100"

val mk_state:
  r:buffer Hacl.UInt64.t{length r = 3} -> acc:buffer Hacl.UInt64.t{length acc = 3 /\ disjoint r acc} ->
  Stack state
    (requires (fun h -> live h r /\ live h acc))
    (ensures (fun h0 st h1 -> h0 == h1 /\ I.(st.r) == r /\ I.(st.h) == acc /\ I.live_st h1 st))


#reset-options "--max_fuel 0 --z3rlimit 200"

val poly1305_blocks_init:
  st:I.poly1305_state ->
  input:uint8_p{disjoint I.(st.r) input /\ disjoint I.(st.h) input} ->
  len:U32.t{U32.v len = length input} ->
  k:uint8_p{length k = 32 /\ disjoint k I.(st.r) /\ disjoint k I.(st.h)} ->
  Stack I.log_t
    (requires (fun h -> I.live_st h st /\ live h input /\ live h k))
    (ensures (fun h0 log h1 -> I.live_st h1 st /\ live h0 input /\ live h0 k
      /\ modifies_2 I.(st.r) I.(st.h) h0 h1
      /\ (let r   = as_seq h1 I.(st.r) in
         let acc = as_seq h1 I.(st.h) in
         let log = Ghost.reveal log in
         let m   = reveal_sbytes (as_seq h0 input) in
         let kr  = reveal_sbytes (as_seq h0 (Buffer.sub k 0ul 16ul)) in
         Hacl.Spec.Poly1305_64.State.invariant (Hacl.Spec.Poly1305_64.State.MkState r acc log)
         /\ seval r = Spec.Poly1305.encode_r kr
         /\ log == Spec.Poly1305.encode_bytes (pad_16 m))
    ))


val poly1305_blocks_continue:
  log:I.log_t ->
  st:I.poly1305_state ->
  input:uint8_p{disjoint I.(st.h) input /\ disjoint I.(st.r) input} ->
  len:U32.t{U32.v len = length input} ->
  Stack I.log_t
    (requires (fun h -> I.live_st h st /\ live h input
      /\ (let r = as_seq h I.(st.r) in
         let acc = as_seq h I.(st.h) in
         let log = Ghost.reveal log in
         Hacl.Spec.Poly1305_64.State.invariant (Hacl.Spec.Poly1305_64.State.MkState r acc log))
    ))
    (ensures (fun h0 log' h1 -> I.live_st h0 st /\ I.live_st h1 st /\ live h0 input
      /\ modifies_1 I.(st.h) h0 h1
      /\ (let r = as_seq h0 I.(st.r) in
         let acc = as_seq h0 I.(st.h) in
         let log = Ghost.reveal log in
         let acc' = as_seq h1 I.(st.h) in
         let log' = Ghost.reveal log' in
         let m    = reveal_sbytes (as_seq h0 input) in
         Hacl.Spec.Poly1305_64.State.invariant (Hacl.Spec.Poly1305_64.State.MkState r acc log)
         /\ Hacl.Spec.Poly1305_64.State.invariant (Hacl.Spec.Poly1305_64.State.MkState r acc' log')
         /\ log' == Seq.append (Spec.Poly1305.encode_bytes (pad_16 m)) log)
    ))


val poly1305_blocks_finish:
  log:I.log_t ->
  st:I.poly1305_state ->
  input:uint8_p{disjoint I.(st.h) input /\ length input = 16} ->
  mac:uint8_p{disjoint I.(st.h) mac /\ disjoint mac input /\ length mac = 16} ->
  key_s:uint8_p{disjoint key_s I.(st.h) /\ disjoint key_s mac /\ length key_s = 16} ->
  Stack unit
    (requires (fun h -> I.live_st h st /\ live h input /\ live h mac /\ live h key_s
      /\ (let r = as_seq h I.(st.r) in
         let acc = as_seq h I.(st.h) in
         let log = Ghost.reveal log in
         Hacl.Spec.Poly1305_64.State.invariant (Hacl.Spec.Poly1305_64.State.MkState r acc log))
    ))
    (ensures (fun h0 _ h1 -> I.live_st h0 st /\ live h0 key_s /\ live h0 input
      /\ modifies_2 mac I.(st.h) h0 h1 /\ live h1 mac
      /\ (let mac = as_seq h1 mac in
         let r   = (as_seq h0 I.(st.r)) in
         let acc = as_seq h0 I.(st.h) in
         let log = Ghost.reveal log in
         let m   = reveal_sbytes (as_seq h0 input) in
         let k   = Hacl.Spec.Endianness.hlittle_endian (as_seq h0 key_s) in
         Hacl.Spec.Poly1305_64.State.invariant (Hacl.Spec.Poly1305_64.State.MkState r acc log)
         /\ Hacl.Spec.Endianness.hlittle_endian mac
           == (Spec.Poly1305.poly (Seq.cons m log) (seval r) + k) % pow2 128)
    ))
