module Hacl.SHA2.Scalar32

open FStar.HyperStack
open FStar.HyperStack.All
open FStar.Mul

open Lib.IntTypes
open Lib.NTuple
open Lib.Buffer
open Lib.MultiBuffer

open Spec.Hash.Definitions
open Hacl.Spec.SHA2.Vec
open Hacl.Impl.SHA2.Generic

module ST = FStar.HyperStack.ST
module Spec = Spec.Agile.Hash
module SpecVec = Hacl.Spec.SHA2.Vec

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

[@CInline]
private
val sha224_update1: update_vec_t SHA2_224 M32
let sha224_update1 block hash = update #SHA2_224 #M32 block hash


val sha224: dst:lbuffer uint8 28ul -> input_len:size_t -> input:lbuffer uint8 input_len ->
  Stack unit
  (requires fun h0 -> v input_len <= max_input_length SHA2_224 /\
    live h0 input /\ live h0 dst /\ disjoint dst input)
  (ensures  fun h0 _ h1 -> modifies (loc dst) h0 h1 /\
    as_seq h1 dst == Spec.hash SHA2_224 (as_seq h0 input))

let sha224 dst input_len input =
  let ib = ntup1 input in
  let rb = ntup1 dst in
  let h0 = ST.get() in
  loc_multi1 rb;
  hash #SHA2_224 #M32 (sha224_update1 <: update_vec_t SHA2_224 M32) rb input_len ib;
  let h1 = ST.get() in
  Hacl.Spec.SHA2.Equiv.hash_agile_lemma #SHA2_224 #M32 (v input_len) (as_seq_multi h0 ib);
  assert ((as_seq_multi h1 rb).(|0|) == as_seq h1 dst)


[@CInline]
private
val sha256_update1: update_vec_t SHA2_256 M32
let sha256_update1 block hash = update #SHA2_256 #M32 block hash


val sha256: dst:lbuffer uint8 32ul -> input_len:size_t -> input:lbuffer uint8 input_len ->
  Stack unit
  (requires fun h0 -> v input_len <= max_input_length SHA2_256 /\
    live h0 input /\ live h0 dst /\ disjoint dst input)
  (ensures  fun h0 _ h1 -> modifies (loc dst) h0 h1 /\
    as_seq h1 dst == Spec.hash SHA2_256 (as_seq h0 input))

let sha256 dst input_len input =
  let ib = ntup1 input in
  let rb = ntup1 dst in
  let h0 = ST.get() in
  loc_multi1 rb;
  hash #SHA2_256 #M32 (sha256_update1 <: update_vec_t SHA2_256 M32) rb input_len ib;
  let h1 = ST.get() in
  Hacl.Spec.SHA2.Equiv.hash_agile_lemma #SHA2_256 #M32 (v input_len) (as_seq_multi h0 ib);
  assert ((as_seq_multi h1 rb).(|0|) == as_seq h1 dst)


[@CInline]
private
val sha384_update1: update_vec_t SHA2_384 M32
let sha384_update1 block hash = update #SHA2_384 #M32 block hash


val sha384: dst:lbuffer uint8 48ul -> input_len:size_t -> input:lbuffer uint8 input_len ->
  Stack unit
  (requires fun h0 -> v input_len <= max_input_length SHA2_384 /\
    live h0 input /\ live h0 dst /\ disjoint dst input)
  (ensures  fun h0 _ h1 -> modifies (loc dst) h0 h1 /\
    as_seq h1 dst == Spec.hash SHA2_384 (as_seq h0 input))

let sha384 dst input_len input =
  let ib = ntup1 input in
  let rb = ntup1 dst in
  let h0 = ST.get() in
  loc_multi1 rb;
  hash #SHA2_384 #M32 (sha384_update1 <: update_vec_t SHA2_384 M32) rb input_len ib;
  let h1 = ST.get() in
  Hacl.Spec.SHA2.Equiv.hash_agile_lemma #SHA2_384 #M32 (v input_len) (as_seq_multi h0 ib);
  assert ((as_seq_multi h1 rb).(|0|) == as_seq h1 dst)


[@CInline]
private
val sha512_update1: update_vec_t SHA2_512 M32
let sha512_update1 block hash = update #SHA2_512 #M32 block hash


val sha512: dst:lbuffer uint8 64ul -> input_len:size_t -> input:lbuffer uint8 input_len ->
  Stack unit
  (requires fun h0 -> v input_len <= max_input_length SHA2_512 /\
    live h0 input /\ live h0 dst /\ disjoint dst input)
  (ensures  fun h0 _ h1 -> modifies (loc dst) h0 h1 /\
    as_seq h1 dst == Spec.hash SHA2_512 (as_seq h0 input))

let sha512 dst input_len input =
  let ib = ntup1 input in
  let rb = ntup1 dst in
  let h0 = ST.get() in
  loc_multi1 rb;
  hash #SHA2_512 #M32 (sha512_update1 <: update_vec_t SHA2_512 M32) rb input_len ib;
  let h1 = ST.get() in
  Hacl.Spec.SHA2.Equiv.hash_agile_lemma #SHA2_512 #M32 (v input_len) (as_seq_multi h0 ib);
  assert ((as_seq_multi h1 rb).(|0|) == as_seq h1 dst)
