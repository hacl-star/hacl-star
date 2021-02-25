module Hacl.SHA2.Scalar32

open FStar.HyperStack
open FStar.HyperStack.All
open FStar.Mul

open Lib.IntTypes
open Lib.NTuple
open Lib.Buffer
open Lib.MultiBuffer

open Spec.Hash.Definitions
open Hacl.Hash.Definitions
open Hacl.Spec.SHA2.Vec
open Hacl.Impl.SHA2.Generic

module ST = FStar.HyperStack.ST
module Spec = Spec.Agile.Hash
module SpecVec = Hacl.Spec.SHA2.Vec


#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

[@CInline]
private
val sha224_update1: update_vec_t SHA2_224 M32
let sha224_update1 b hash = update #SHA2_224 #M32 b hash


val sha224: hash:lbuffer uint8 28ul -> len:size_t -> b:lbuffer uint8 len ->
  Stack unit
  (requires fun h0 -> live h0 b /\ live h0 hash /\ disjoint hash b)
  (ensures  fun h0 _ h1 -> modifies (loc hash) h0 h1 /\
    as_seq h1 hash == Spec.hash #SHA2_224 (v len) (as_seq h0 b))

let sha224 h len b =
  let h0 = ST.get() in
  let b = ntup1 b in
  let h = ntup1 h in
  hash #SHA2_224 #M32 (sha224_update1 <: update_vec_t SHA2_224 M32) h len b;
  let h1 = ST.get() in
  Hacl.Spec.SHA2.Equiv.hash_lemma #SHA2_224 #M32 (v len) (as_seq_multi h0 b);
  let hash0 = tup1 h in
  assert ((as_seq_multi h1 h).(|0|) == as_seq h1 hash0)


[@CInline]
private
val sha256_update1: update_vec_t SHA2_256 M32
let sha256_update1 b hash = update #SHA2_256 #M32 b hash


val sha256: hash:lbuffer uint8 32ul -> len:size_t -> b:lbuffer uint8 len ->
  Stack unit
  (requires fun h0 -> v len <= max_input_length SHA2_256 /\
    live h0 b /\ live h0 hash /\ disjoint hash b)
  (ensures  fun h0 _ h1 -> modifies (loc hash) h0 h1 /\
    as_seq h1 hash == Spec.hash SHA2_256 (as_seq h0 b))

let sha256 h len b =
  let h0 = ST.get() in
  let b = ntup1 b in
  let h = ntup1 h in
  hash #SHA2_256 #M32 (sha256_update1 <: update_vec_t SHA2_256 M32) h len b;
  let h1 = ST.get() in
  Hacl.Spec.SHA2.Equiv.hash_agile_lemma #SHA2_256 #M32 (v len) (as_seq_multi h0 b);
  let hash0 = tup1 h in
  assert ((as_seq_multi h1 h).(|0|) == as_seq h1 hash0)


[@CInline]
private
val sha384_update1: update_vec_t SHA2_384 M32
let sha384_update1 b hash = update #SHA2_384 #M32 b hash


val sha384: hash:lbuffer uint8 48ul -> len:size_t -> b:lbuffer uint8 len ->
  Stack unit
  (requires fun h0 -> live h0 b /\ live h0 hash /\ disjoint hash b)
  (ensures  fun h0 _ h1 -> modifies (loc hash) h0 h1 /\
    as_seq h1 hash == Spec.hash #SHA2_384 (v len) (as_seq h0 b))

let sha384 h len b =
  let h0 = ST.get() in
  let b = ntup1 b in
  let h = ntup1 h in
  hash #SHA2_384 #M32 (sha384_update1 <: update_vec_t SHA2_384 M32) h len b;
  let h1 = ST.get() in
  Hacl.Spec.SHA2.Equiv.hash_lemma #SHA2_384 #M32 (v len) (as_seq_multi h0 b);
  let hash0 = tup1 h in
  assert ((as_seq_multi h1 h).(|0|) == as_seq h1 hash0)


[@CInline]
private
val sha512_update1: update_vec_t SHA2_512 M32
let sha512_update1 b hash = update #SHA2_512 #M32 b hash


val sha512: hash:lbuffer uint8 64ul -> len:size_t -> b:lbuffer uint8 len ->
  Stack unit
  (requires fun h0 -> v len <= max_input_length SHA2_512 /\
    live h0 b /\ live h0 hash /\ disjoint hash b)
  (ensures  fun h0 _ h1 -> modifies (loc hash) h0 h1 /\
    as_seq h1 hash == Spec.hash SHA2_512 (as_seq h0 b))

let sha512 h len b =
  let h0 = ST.get() in
  let b = ntup1 b in
  let h = ntup1 h in
  hash #SHA2_512 #M32 (sha512_update1 <: update_vec_t SHA2_512 M32) h len b;
  let h1 = ST.get() in
  Hacl.Spec.SHA2.Equiv.hash_agile_lemma #SHA2_512 #M32 (v len) (as_seq_multi h0 b);
  let hash0 = tup1 h in
  assert ((as_seq_multi h1 h).(|0|) == as_seq h1 hash0)
