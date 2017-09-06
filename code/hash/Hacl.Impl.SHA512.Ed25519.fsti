module Hacl.Impl.SHA512.Ed25519

module ST = FStar.HyperStack.ST

open FStar.HyperStack.All

open FStar.Mul
open FStar.UInt32
open FStar.HyperStack
open FStar.Seq
open FStar.Buffer

#reset-options "--max_fuel 0 --z3rlimit 20"

let hint8_p = buffer Hacl.UInt8.t
let op_String_Access h b = Hacl.Spec.Endianness.reveal_sbytes (as_seq h b)


val sha512_pre_msg:
  hash:hint8_p{length hash = 64} ->
  prefix:hint8_p{length prefix = 32 /\ disjoint prefix hash} ->
  input:hint8_p{disjoint input hash} ->
  len:UInt32.t{UInt32.v len = length input /\ length input < pow2 32 - 32} ->
  Stack unit
    (requires (fun h -> live h hash /\ live h prefix /\ live h input))
    (ensures (fun h0 _ h1 -> live h0 hash /\ live h0 prefix /\ live h0 input /\
      live h1 hash /\ live h1 prefix /\ live h1 input /\ modifies_1 hash h0 h1 /\
      h1.[hash] == Spec.Ed25519.sha512 FStar.Seq.(h0.[prefix] @| h0.[input])))


val sha512_pre_pre2_msg:
  hash:hint8_p{length hash = 64} ->
  prefix:hint8_p{length prefix = 32 /\ disjoint prefix hash} ->
  prefix2:hint8_p{length prefix2 = 32 /\ disjoint prefix2 hash} ->
  input:hint8_p{disjoint input hash} ->
  len:UInt32.t{UInt32.v len = length input /\ length input < pow2 32 - 64} ->
  Stack unit
    (requires (fun h -> live h hash /\ live h prefix /\ live h prefix2 /\ live h input))
    (ensures (fun h0 _ h1 -> live h0 hash /\ live h0 prefix /\ live h0 input /\ live h0 prefix2 /\
      live h1 hash /\ live h1 prefix /\ live h1 input /\ modifies_1 hash h0 h1 /\
      h1.[hash] == Spec.Ed25519.sha512 (h0.[prefix] @| h0.[prefix2] @| h0.[input])))
