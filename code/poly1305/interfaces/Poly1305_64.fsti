module Poly1305_64

open FStar.Mul
open FStar.ST
open FStar.Ghost
open FStar.Seq
open FStar.HyperStack
open FStar.Endianness
open FStar.Buffer


module U32  = FStar.UInt32
module U64  = FStar.UInt64


(* Type Aliases *)
type uint8_p = Buffer.buffer Hacl.UInt8.t
type key = k:uint8_p{length k = 32}

type state
type live_state (h:mem) (st:state)
type stable (h:mem) (st:state)

val get_key: st:state -> Tot (b:Buffer.buffer Hacl.UInt32.t{length b = 3})
val get_accumulator: st:state -> Tot (b:Buffer.buffer Hacl.UInt32.t{length b = 3})

#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 10"

val alloc:
  unit -> StackInline state
    (requires (fun h -> True))
    (ensures (fun h0 st h1 -> modifies_0 h0 h1 /\ live_state h1 st))


val init:
  st:state ->
  k:uint8_p{length k >= 16} ->
  Stack unit
    (requires (fun h -> live h k /\ live_state h st))
    (ensures (fun h0 _ h1 -> modifies_2 (get_key st) (get_accumulator st) h0 h1 /\ stable h1 st))


val update_block:
  st:state ->
  m:uint8_p{length m = 16} ->
  Stack unit
    (requires (fun h -> stable h st /\ live h m))
    (ensures  (fun h0 updated_log h1 -> modifies_1 (get_accumulator st) h0 h1 /\ stable h1 st))


#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 100"

val update:
  st:state ->
  m:uint8_p ->
  len:FStar.UInt32.t{length m >= 16 * UInt32.v len} ->
  Stack unit
    (requires (fun h -> stable h st /\ live h m))
    (ensures  (fun h0 updated_log h1 -> modifies_1 (get_accumulator st) h0 h1 /\ stable h1 st))

  
#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 10"

type before_finish (h:mem) (st:state)


#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 100"

val update_last:
  st:state ->
  m:uint8_p ->
  len:UInt32.t{UInt32.v len < 16 /\ UInt32.v len <= length m} ->
  Stack unit
    (requires (fun h -> stable h st /\ live h m))
    (ensures  (fun h0 _ h1 -> modifies_1 (get_accumulator st) h0 h1 /\ before_finish h1 st))


val finish:
  st:state ->
  mac:uint8_p{length mac = 16} ->
  k:uint8_p{length k = 16} ->
  Stack unit
    (requires (fun h -> before_finish h st /\ live h mac /\ live h k))
    (ensures (fun h0 _ h1 -> modifies_1 mac h0 h1))


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

val poly1305_blocks_init:
  st:state ->
  input:uint8_p{disjoint (get_key st) input /\ disjoint (get_accumulator st) input} ->
  len:U32.t{U32.v len = length input} ->
  k:uint8_p{length k = 32 /\ disjoint k (get_key st) /\ disjoint k (get_accumulator st)} ->
  Stack unit
    (requires (fun h -> live_state h st /\ live h input /\ live h k))
    (ensures (fun h0 _ h1 -> live_state h1 st /\ live h0 input /\ live h0 k /\ modifies_2 (get_key st) (get_accumulator st) h0 h1))

val poly1305_blocks_continue:
  st:state ->
  input:uint8_p{disjoint (get_accumulator st) input} ->
  len:U32.t{U32.v len = length input} ->
  Stack unit
    (requires (fun h -> live_state h st /\ live h input))
    (ensures (fun h0 _ h1 -> live_state h1 st /\ live h0 input /\ modifies_1 (get_accumulator st) h0 h1))

val poly1305_blocks_finish:
  st:state ->
  input:uint8_p{disjoint (get_accumulator st) input} ->
  mac:uint8_p{disjoint (get_accumulator st) mac /\ disjoint mac input} ->
  key_s:uint8_p{disjoint key_s (get_accumulator st) /\ disjoint key_s mac} ->
  Stack unit
    (requires (fun h -> live_state h st /\ live h input /\ live h mac))
    (ensures (fun h0 _ h1 -> live h0 input /\ modifies_2 mac (get_accumulator st) h0 h1 /\ live h1 mac))
