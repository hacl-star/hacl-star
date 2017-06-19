module Hacl.Poly1305

open FStar.Mul
open FStar.ST
open FStar.Buffer
open FStar.Ghost
open FStar.Seq
open FStar.HyperStack

open Hacl.Cast
open Hacl.Bignum.Parameters
open Hacl.Spec.Bignum.Bigint
open Hacl.Spec.Poly1305


module H8   = Hacl.UInt8
module Limb = Hacl.Bignum.Limb
module Wide = Hacl.Bignum.Wide
module U8   = FStar.UInt8
module U32  = FStar.UInt32
module U64  = FStar.UInt64

#set-options "--lax"

open Hacl.MAC.Poly1305_64

inline_for_extraction let bigint = felem
inline_for_extraction let uint8_p = buffer Hacl.UInt8.t
let elemB : Type0 = b:felem
let wordB = b:uint8_p{length b <= 16}
let wordB_16 = b:uint8_p{length b = 16}


(* Poly log *)
inline_for_extraction let log_t = erased text


val poly1305_init:
  st:poly1305_state ->
  key:uint8_p{length key = 32} ->
  Stack log_t
    (requires (fun h -> live_st h st /\ live h key
      /\ disjoint st.r key
      /\ disjoint st.h key))
    (ensures  (fun h0 log h1 -> modifies_2 st.r st.h h0 h1 /\ live h0 key
      /\ live h1 st.r /\ live h1 st.h
      /\ (let log = reveal log in
         let r = seval (as_seq h1 st.r) % prime in
         let acc = seval (as_seq h1 st.h) % prime in
         acc == poly log r
         /\ r = encode_r (as_seq h0 key))))
let poly1305_init_ st key = poly1305_init_ st key


val poly1305_update:
  current_log:log_t ->
  st:poly1305_state ->
  m:uint8_p{length m >= 16} ->
  Stack log_t
    (requires (fun h -> live_st h st /\ live h m /\ disjoint m st.h /\ disjoint m st.r
      /\ (let log = reveal current_log in
         let r = seval (as_seq h st.r) % prime in
         let acc = seval (as_seq h st.h) % prime in
         acc == poly log r)
      ))
    (ensures  (fun h0 updated_log h1 -> modifies_1 st.h h0 h1 /\ live_st h1 st /\ live_st h0 st /\ live h0 m
      /\ (let log  = reveal current_log in
         let log' = reveal updated_log in
         let r    = seval (as_seq h0 st.r) % prime in
         let acc  = seval (as_seq h0 st.h) % prime in
         let acc' = seval (as_seq h1 st.h) % prime in
         let block = Seq.slice (as_seq h0 m) 0 16 in
         log' = Seq.snoc log block
         /\ acc' == poly log' r)))
let poly1305_update log st m =
  let h = ST.get() in
  let log' = elift1 (fun x -> Seq.snoc x (Seq.slice (as_seq h m) 0 16)) log in
  poly1305_update () st m;
  log'


val poly1305_finish:
  log:log_t ->
  st:poly1305_state ->
  mac:uint8_p{length mac = 16} ->
  m:uint8_p ->
  len:U64.t{U64.v len < pow2 32 /\ U64.v len <= length m} ->
  key_s:uint8_p{length key_s = 16} ->
  Stack unit
    (requires (fun h -> live_st h st /\ live h mac /\ live h m /\ live h key_s
      /\ disjoint st.h mac /\ disjoint st.h key_s /\ disjoint st.h m
      /\ (let log = reveal log in
         let r = seval (as_seq h st.r) % prime in
         let acc = seval (as_seq h st.h) % prime in
         acc == poly log r)
      ))
    (ensures  (fun h0 updated_log h1 -> modifies_2 st.h mac h0 h1 /\ live_st h0 st /\ live h0 m
      /\ live h1 st.h /\ live h1 mac /\ live h0 key_s
      /\ (let log  = reveal log in
         let r    = seval (as_seq h0 st.r) % prime in
         let s    = as_seq h0 key_s in
         let block = Seq.slice (as_seq h0 m) 0 (U64.v len) in
         let final_log = poly (Seq.snoc log block) r in
         let tag  = as_seq h1 mac in
         tag = finish final_log s)
      ))
let poly1305_finish log st mac m len key_s = poly1305_finish_ () st mac m len key_s


val crypto_onetimeauth:
  output:uint8_p{length output = 16} ->
  input:uint8_p{disjoint input output} ->
  len:U64.t{U64.v len < pow2 32 /\ U64.v len <= length input} ->
  k:uint8_p{disjoint output k /\ length k = 32} ->
  Stack unit
    (requires (fun h -> live h output /\ live h input /\ live h k))
    (ensures  (fun h0 _ h1 -> live h1 output /\ modifies_1 output h0 h1 /\ live h0 input /\ live h0 k
      /\ (let msg = Seq.slice (as_seq h0 input) 0 (U64.v len) in
         let k   = as_seq h0 k in
         let tag = as_seq h1 output in
         tag = poly1305 msg k)
    ))
let crypto_onetimeauth output input len k = crypto_onetimeauth output input len k
