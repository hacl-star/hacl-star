module Hacl.Chacha20

module ST = FStar.HyperStack.ST

open FStar.HyperStack.All

open FStar.Buffer
open FStar.UInt32

open Hacl.Spec.Endianness

open Spec.Chacha20


#reset-options "--max_fuel 0 --z3rlimit 100"

let uint8_p = buffer Hacl.UInt8.t
let uint32_t = t
private let op_String_Access (h:HyperStack.mem) (m:uint8_p{live h m}) = reveal_sbytes (as_seq h m)

val chacha20_key_block:
  block:uint8_p{length block = 64} ->
  k:uint8_p{length k = 32 /\ disjoint block k} ->
  n:uint8_p{length n = 12 /\ disjoint block n} ->
  ctr:uint32_t ->
  Stack unit
    (requires (fun h -> live h block /\ live h k /\ live h n))
    (ensures (fun h0 _ h1 -> live h1 block /\ modifies_1 block h0 h1 /\ live h0 k /\ live h0 n /\
      h1.[block] == Spec.Chacha20.chacha20_block h0.[k] h0.[n] (v ctr)))


(** @summary This function implements Chacha20
    @type
*)
val chacha20:
  output:uint8_p ->
  plain:uint8_p{disjoint output plain} ->
  len:uint32_t{v len = length output /\ v len = length plain} ->
  key:uint8_p{length key = 32} ->
  nonce:uint8_p{length nonce = 12} ->
  ctr:uint32_t{v ctr + (length plain / 64) < pow2 32} ->
  Stack unit
    (requires (fun h -> live h output /\ live h plain /\ live h nonce /\ live h key))
    (ensures (fun h0 _ h1 -> live h1 output /\ live h0 plain /\ modifies_1 output h0 h1
      /\ live h0 nonce /\ live h0 key /\
      h1.[output] == chacha20_encrypt_bytes h0.[key] h0.[nonce] (v ctr) h0.[plain]))
