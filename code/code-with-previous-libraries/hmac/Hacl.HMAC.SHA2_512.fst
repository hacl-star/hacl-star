module Hacl.HMAC.SHA2_512

open FStar.Mul
open FStar.Ghost
open FStar.HyperStack
open FStar.HyperStack.All
open FStar.HyperStack.ST
open FStar.Buffer
open FStar.UInt32

module ST = FStar.HyperStack.ST
module Hash = Hacl.Impl.SHA2_512
module Spec = Spec.HMAC.SHA2_512
module HMAC = Hacl.Impl.HMAC.SHA2_512


(* Definition of base types *)
private let uint8_ht   = Hacl.UInt8.t
private let uint32_t  = FStar.UInt32.t
private let uint8_p  = Buffer.buffer uint8_ht


//
// HMAC
//

#reset-options "--max_fuel 0 --z3rlimit 25"

val hmac_core:
  mac  :uint8_p  {length mac = v Hash.size_hash} ->
  key  :uint8_p  {length key = v Hash.size_block /\ disjoint key mac} ->
  data :uint8_p  {length data + v Hash.size_block < pow2 32 /\ disjoint data mac /\ disjoint data key} ->
  len  :uint32_t {length data = v len} ->
  Stack unit
        (requires (fun h -> live h mac /\ live h key /\ live h data))
        (ensures  (fun h0 _ h1 -> live h1 mac /\ live h0 mac
                             /\ live h1 key /\ live h0 key
                             /\ live h1 data /\ live h0 data /\ modifies_1 mac h0 h1
                             /\ (as_seq h1 mac == Spec.hmac_core (as_seq h0 key) (as_seq h0 data))))

#reset-options "--max_fuel 0 --z3rlimit 10"

let hmac_core mac key data len = HMAC.hmac_core mac key data len

//
//

#reset-options "--max_fuel 0 --z3rlimit 25"

val hmac:
  mac     :uint8_p  {length mac = v Hash.size_hash} ->
  key     :uint8_p  {length key = v Hash.size_block /\ disjoint key mac} ->
  keylen  :uint32_t {v keylen = length key} ->
  data    :uint8_p  {length data + v Hash.size_block < pow2 32 /\ disjoint data mac /\ disjoint data key} ->
  datalen :uint32_t {v datalen = length data} ->
  Stack unit
        (requires (fun h -> live h mac /\ live h key /\ live h data))
        (ensures  (fun h0 _ h1 -> live h1 mac /\ live h0 mac
                             /\ live h1 key /\ live h0 key
                             /\ live h1 data /\ live h0 data /\ modifies_1 mac h0 h1
                             /\ (as_seq h1 mac == Spec.hmac (as_seq h0 key) (as_seq h0 data))))

#reset-options "--max_fuel 0 --z3rlimit 10"

let hmac mac key keylen data datalen = HMAC.hmac mac key keylen data datalen
