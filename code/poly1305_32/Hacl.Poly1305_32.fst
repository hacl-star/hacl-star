module Hacl.Poly1305_32

open FStar.HyperStack.All

module HS = FStar.HyperStack
module ST = FStar.HyperStack.ST

open FStar.Mul
open FStar.HyperStack.ST
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
module I = Hacl.Impl.Poly1305_32
module S = Hacl.Spec.Poly1305_32
module Poly = Hacl.Standalone.Poly1305_32
       	      

(* Type Aliases *)
type key = k:uint8_p{length k = 32}

type state = I.poly1305_state
type live_state (h:mem) (st:state) = I.live_st h st
type stable (h:mem) (st:state) = live_state h st /\ S.red_y (as_seq h I.(st.h)) /\ S.red_26 (as_seq h I.(st.r))

private let get_key (st:state) = I.(st.r)
private let get_accumulator (st:state) = I.(st.h)

#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 100"

val alloc:
  unit -> StackInline state
    (requires (fun h -> True))
    (ensures (fun h0 st h1 -> modifies_0 h0 h1 /\ I.live_st h1 st /\ frameOf I.(st.h) == HS.get_tip h0
      /\ frameOf I.(st.r) = HS.get_tip h0 /\ (I.(st.r) `unused_in` h0) /\ (I.(st.h) `unused_in` h0)))
let alloc () =
  I.alloc()

val mk_state:
  r:buffer Hacl.UInt32.t{length r = 5} -> acc:buffer Hacl.UInt32.t{length acc = 5 /\ disjoint r acc} ->
  Stack state
    (requires (fun h -> live h r /\ live h acc))
    (ensures (fun h0 st h1 -> h0 == h1 /\ I.(st.r) == r /\ I.(st.h) == acc /\ I.live_st h1 st))
let mk_state r acc = I.mk_state r acc


val init:
  st:state ->
  k:uint8_p{length k >= 16} ->
  Stack unit
    (requires (fun h -> live h k /\ live_state h st))
    (ensures (fun h0 _ h1 -> modifies_2 (get_key st) (get_accumulator st) h0 h1 /\ stable h1 st))
let init st k =
  let _ = I.poly1305_init_ st (Buffer.sub k 0ul 16ul) in ()

let empty_log : I.log_t = Ghost.hide (Seq.createEmpty #Spec.Poly1305.word)

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
    let h0    = ST.get () in
    let _ = update_block st block in
    let h1    = ST.get () in
    Buffer.lemma_reveal_modifies_1 (get_accumulator st) h0 h1;
    update st m' len

  
#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 10"

module A = Hacl.Spec.Bignum.AddAndMultiply

type before_finish h st = A.(live_state h st /\ bounds (as_seq h (get_accumulator st)) p26 p26 p26 p26 p26)


#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 100"

val update_last:
  st:state ->
  m:uint8_p ->
  len:UInt32.t{UInt32.v len < 16 /\ UInt32.v len <= length m} ->
  Stack unit
    (requires (fun h -> stable h st /\ live h m))
    (ensures  (fun h0 _ h1 -> modifies_1 (get_accumulator st) h0 h1 /\ before_finish h1 st))
let update_last st m len =
  I.poly1305_update_last empty_log st (Buffer.sub m 0ul len) (Int.Cast.uint32_to_uint64 len)


val finish:
  st:state ->
  mac:uint8_p{length mac = 16} ->
  k:uint8_p{length k = 16} ->
  Stack unit
    (requires (fun h -> before_finish h st /\ live h mac /\ live h k))
    (ensures (fun h0 _ h1 -> modifies_1 mac h0 h1))
let finish st mac k =
  I.poly1305_finish st mac k

let crypto_onetimeauth output input len k = Hacl.Standalone.Poly1305_32.crypto_onetimeauth output input len k
