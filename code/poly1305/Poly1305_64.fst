module Poly1305_64

open FStar.Mul
open FStar.ST
open FStar.Ghost
open FStar.Seq
open FStar.HyperStack
open FStar.Endianness
open FStar.Buffer
open Hacl.Cast


module H8   = Hacl.UInt8
module Limb = Hacl.Bignum.Limb
module Wide = Hacl.Bignum.Wide
module U8   = FStar.UInt8
module U32  = FStar.UInt32
module U64  = FStar.UInt64
module I = Hacl.Impl.Poly1305_64
module S = Hacl.Spec.Poly1305_64
module Poly = Hacl.Standalone.Poly1305_64
       	      

(* Type Aliases *)
type uint8_p = Buffer.buffer Hacl.UInt8.t
type key = k:uint8_p{length k = 32}

abstract type state = I.poly1305_state
abstract type live_state (h:mem) (st:state) = I.live_st h st
abstract type stable (h:mem) (st:state) = live_state h st /\ S.red_45 (as_seq h I.(st.h)) /\ S.red_44 (as_seq h I.(st.r))

private let get_key (st:state) = I.MkState?.r st
private let get_accumulator (st:state) = I.MkState?.h st

#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 10"

val alloc:
  unit -> StackInline state
    (requires (fun h -> True))
    (ensures (fun h0 st h1 -> modifies_0 h0 h1 /\ live_state h1 st))
let alloc () =
  I.alloc()


val init:
  st:state ->
  k:uint8_p{length k >= 16} ->
  Stack unit
    (requires (fun h -> live h k /\ live_state h st))
    (ensures (fun h0 _ h1 -> modifies_2 (get_key st) (get_accumulator st) h0 h1 /\ stable h1 st))
let init st k =
  let _ = I.poly1305_init_ st (Buffer.sub k 0ul 16ul) in ()

let empty_log : I.log_t = Ghost.hide (Seq.createEmpty)

val update_block:
  st:state ->
  m:uint8_p{length m = 16} ->
  Stack unit
    (requires (fun h -> stable h st /\ live h m))
    (ensures  (fun h0 updated_log h1 -> modifies_1 (get_accumulator st) h0 h1 /\ stable h1 st))
let update_block st m =
  let _ = I.poly1305_update empty_log st m in ()


#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 100"

val update:
  st:state ->
  m:uint8_p ->
  len:FStar.UInt32.t{length m >= 16 * UInt32.v len} ->
  Stack unit
    (requires (fun h -> stable h st /\ live h m))
    (ensures  (fun h0 updated_log h1 -> modifies_1 (get_accumulator st) h0 h1 /\ stable h1 st))
let rec update st m len =
  if FStar.UInt32.(len =^ 0ul) then ()
  else 
    let block = Buffer.sub m 0ul 16ul in
    let m'    = Buffer.offset m 16ul  in
    let len   = FStar.UInt32.(len -^ 1ul) in
    let _ = update_block st block in
    update st m' len

  
#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 10"

module A = Hacl.Spec.Bignum.AddAndMultiply

abstract type before_finish h st = A.(live_state h st /\ bounds (as_seq h (get_accumulator st)) p44 p44 p42)


#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 100"

val update_last:
  st:state ->
  m:uint8_p ->
  len:UInt32.t{UInt32.v len < 16 /\ UInt32.v len <= length m} ->
  Stack unit
    (requires (fun h -> stable h st /\ live h m))
    (ensures  (fun h0 _ h1 -> modifies_1 (get_accumulator st) h0 h1 /\ before_finish h1 st))
let update_last st m len =
  I.poly1305_update_last empty_log st (Buffer.sub m 0ul len) (Hacl.Cast.sint32_to_sint64 len)


val finish:
  st:state ->
  mac:uint8_p{length mac = 16} ->
  k:uint8_p{length k = 16} ->
  Stack unit
    (requires (fun h -> before_finish h st /\ live h mac /\ live h k))
    (ensures (fun h0 _ h1 -> modifies_1 mac h0 h1))
let finish st mac k =
  I.poly1305_finish st mac k


val crypto_onetimeauth:
  output:uint8_p{length output = 16} ->
  input:uint8_p{disjoint input output} ->
  len:U64.t{U64.v len < pow2 32 /\ U64.v len = length input} ->
  k:uint8_p{disjoint output k /\ length k = 32} ->
  Stack unit
    (requires (fun h -> live h output /\ live h input /\ live h k))
    (ensures  (fun h0 _ h1 -> live h1 output /\ modifies_1 output h0 h1 /\ live h0 input /\ live h0 k
      /\ (let mac     = Hacl.Spec.Endianness.reveal_sbytes (as_seq h1 output) in
         let message = Hacl.Spec.Endianness.reveal_sbytes (as_seq h0 input) in
         let key     = Hacl.Spec.Endianness.reveal_sbytes (as_seq h0 k) in
         mac == Spec.Poly1305.poly1305 message key)))
let crypto_onetimeauth output input len k = Hacl.Standalone.Poly1305_64.crypto_onetimeauth output input len k

#set-options "--lax"

private val pad_16_bytes:
  input:uint8_p ->
  len:U32.t{length input = U32.v len /\ U32.v len < 16 /\ U32.v len > 0} ->
  StackInline (uint8_p)
    (requires (fun h -> live h input))
    (ensures (fun h0 output h1 -> live h0 input /\ live h1 output /\ frameOf output = h1.tip
      /\ modifies_0 h0 h1 /\ length output = 16
      /\ (let o = as_seq h1 output in let i = as_seq h0 input in
         o == Spec.Chacha20Poly1305.pad_16 i)))
private let pad_16_bytes input len =
  let h0 = ST.get() in
  let b = Buffer.create (uint8_to_sint8 0uy) 16ul in
  Buffer.blit input 0ul b 0ul len;
  let h = ST.get() in
  no_upd_lemma_0 h0 h input;
  Seq.lemma_eq_intro (as_seq h input) (Seq.slice (as_seq h input) 0 (U32.v len));
  Seq.lemma_eq_intro (Seq.slice (as_seq h b) (U32.v len) 16) (Seq.create (16 - U32.v len) (uint8_to_sint8 0uy));
  Seq.lemma_eq_intro (as_seq h b) (Spec.Chacha20Poly1305.pad_16 (as_seq h0 input));
  b

val poly1305_blocks_init:
  st:state ->
  input:uint8_p{disjoint (get_key st) input /\ disjoint (get_accumulator st) input} ->
  len:U32.t{U32.v len = length input} ->
  k:uint8_p{length k = 32 /\ disjoint k (get_key st) /\ disjoint k (get_accumulator st)} ->
  Stack unit
    (requires (fun h -> live_state h st /\ live h input /\ live h k))
    (ensures (fun h0 _ h1 -> live_state h1 st /\ live h0 input /\ live h0 k /\ modifies_2 (get_key st) (get_accumulator st) h0 h1))
let poly1305_blocks_init st input len k =
  let l = I.poly1305_init_ st (Buffer.sub k 0ul 16ul) in
  let len_16 = U32.(len >>^ 4ul) in
  let rem_16 = U32.(len &^ 15ul)  in
  let l = Poly.poly1305_blocks l st (Buffer.sub input 0ul U32.(16ul *^ len_16)) (Int.Cast.uint32_to_uint64 len_16) in
  if U32.(rem_16 =^ 0ul) then ()
  else (
    push_frame();
    let b = pad_16_bytes (Buffer.offset input U32.(len -^ rem_16)) rem_16 in
    let l = I.poly1305_update l st b in
    pop_frame()
  )



val poly1305_blocks_continue:
  st:state ->
  input:uint8_p{disjoint (get_accumulator st) input} ->
  len:U32.t{U32.v len = length input} ->
  Stack unit
    (requires (fun h -> live_state h st /\ live h input))
    (ensures (fun h0 _ h1 -> live_state h1 st /\ live h0 input /\ modifies_1 (get_accumulator st) h0 h1))
let poly1305_blocks_continue st input len =
  let len_16 = U32.(len >>^ 4ul) in
  let rem_16 = U32.(len &^ 15ul)  in
  let l = Poly.poly1305_blocks empty_log st (Buffer.sub input 0ul U32.(16ul *^ len_16)) (Int.Cast.uint32_to_uint64 len_16) in
  if U32.(rem_16 =^ 0ul) then ()
  else (
    push_frame();
    let b = pad_16_bytes (Buffer.offset input U32.(len -^ rem_16)) rem_16 in
    let _ = I.poly1305_update l st b in
    pop_frame()
  )

val poly1305_blocks_finish:
  st:state ->
  input:uint8_p{disjoint (get_accumulator st) input} ->
  mac:uint8_p{disjoint (get_accumulator st) mac /\ disjoint mac input} ->
  key_s:uint8_p{disjoint key_s (get_accumulator st) /\ disjoint key_s mac} ->
  Stack unit
    (requires (fun h -> live_state h st /\ live h input /\ live h mac))
    (ensures (fun h0 _ h1 -> live h0 input /\ modifies_2 mac (get_accumulator st) h0 h1 /\ live h1 mac))
let poly1305_blocks_finish st input mac key_s =
  let _ = I.poly1305_update empty_log st input in
  let _ = I.poly1305_update_last empty_log st (Buffer.offset input 16ul) 0uL in
  let _ = I.poly1305_finish st mac key_s in
  ()

