module Hacl.Streaming.Functor

/// Provided an instance of the type class, this creates a streaming API on top.
/// This means that every function in this module takes two extra arguments
/// compared to the previous streaming module specialized for hashes: the type
/// of the index, and a type class for that index. Then, as usual, a given value
/// for the index as a parameter.

#set-options "--max_fuel 0 --max_ifuel 0 --z3rlimit 100"

module HS = FStar.HyperStack
module B = LowStar.Buffer
module G = FStar.Ghost
module S = FStar.Seq
module U32 = FStar.UInt32
module U64 = FStar.UInt64

open Hacl.Streaming.Interface
open FStar.HyperStack.ST
open LowStar.BufferOps
open FStar.Mul

inline_for_extraction noextract
let uint8 = Lib.IntTypes.uint8

inline_for_extraction noextract
let uint32 = Lib.IntTypes.uint32

/// State machinery

noeq
type state_s #index (c: block index) (i: index) =
| State:
    block_state: c.state i ->
    buf: B.buffer Lib.IntTypes.uint8 { B.len buf = c.block_len i } ->
    total_len: UInt64.t ->
    seen: G.erased (S.seq uint8) ->
    state_s #index c i

// TODO: move to fsti
let state #index (c: block index) (i: index) = B.pointer (state_s c i)

let freeable #index (c: block index) (i: index) (h: HS.mem) (p: state c i) =
  B.freeable p /\ (
  let s = B.deref h p in
  let State hash_state buf _ _ = s in
  B.freeable buf /\ c.freeable h hash_state)

let preserves_freeable #index (c: block index) (i: index) (s: state c i) (h0 h1: HS.mem): Type0 =
  freeable c i h0 s ==> freeable c i h1 s

let footprint_s #index (c: block index) (i: index) (h: HS.mem) (s: state_s c i) =
  let State block_state buf_ _ _ = s in
  B.(loc_union (loc_addr_of_buffer buf_) (c.footprint h block_state))

// TODO: move to fsti
let footprint #index (c: block index) (i: index) (m: HS.mem) (s: state c i) =
  B.(loc_union (loc_addr_of_buffer s) (footprint_s c i m (B.deref m s)))

/// Invariants

let bytes = S.seq uint8

noextract
let split_at_last (block_length: pos) (b: bytes):
  Pure (bytes & bytes)
    (requires True)
    (ensures (fun (blocks, rest) ->
      S.length rest < block_length /\
      S.length rest = S.length b % block_length /\
      S.equal (S.append blocks rest) b /\
      S.length blocks % block_length = 0))
=
  let n = S.length b / block_length in
  let blocks, rest = S.split b (n * block_length) in
  assert (S.length blocks = n * block_length);
  FStar.Math.Lemmas.multiple_modulo_lemma n block_length;
  assert ((n * block_length) % block_length = 0);
  assert (S.length rest = S.length b - n * block_length);
  assert (S.length b - n * block_length < block_length);
  blocks, rest

let loc_includes_union_l_footprint_s
  #index
  (c: block index)
  (i: index)
  (m: HS.mem)
  (l1 l2: B.loc) (s: state_s c i)
: Lemma
  (requires (
    B.loc_includes l1 (footprint_s c i m s) \/ B.loc_includes l2 (footprint_s c i m s)
  ))
  (ensures (B.loc_includes (B.loc_union l1 l2) (footprint_s c i m s)))
  [SMTPat (B.loc_includes (B.loc_union l1 l2) (footprint_s c i m s))]
= B.loc_includes_union_l l1 l2 (footprint_s c i m s)

let invariant_s #index (c: block index) (i: index) h (s: state_s c i) =
  let State hash_state buf_ total_len seen = s in
  let seen = G.reveal seen in
  let blocks, rest = split_at_last (U32.v (c.block_len i)) seen in

  // Liveness and disjointness (administrative)
  B.live h buf_ /\ c.invariant #i h hash_state /\
  B.(loc_disjoint (loc_buffer buf_) (c.footprint h hash_state)) /\

  // Formerly, the "hashes" predicate
  S.length blocks + S.length rest = U64.v total_len /\
  S.length seen = U64.v total_len /\
  U64.v total_len < c.max_input_length i /\
  // Note the double equals here, we now no longer know that this is a sequence.
  c.v h hash_state == c.update_multi_s i (c.init_s i) blocks /\
  S.equal (S.slice (B.as_seq h buf_) 0 (U64.v total_len % U32.v (c.block_len i))) rest

let invariant #index (c: block index) (i: index) (m: HS.mem) (s: state c i) =
  B.live m s /\
  B.(loc_disjoint (loc_addr_of_buffer s) (footprint_s c i m (B.deref m s))) /\
  invariant_s c i m (B.get m s 0)

val invariant_loc_in_footprint
  (#index: Type0)
  (c: block index)
  (i: index)
  (s: state c i)
  (m: HS.mem)
: Lemma
  (requires (invariant c i m s))
  (ensures (B.loc_in (footprint c i m s) m))
  [SMTPat (invariant c i m s)]


#push-options "--max_ifuel 1"
let invariant_loc_in_footprint #index c i s m =
  let aux (h:HS.mem) (s:c.state i): Lemma
    (requires (c.invariant h s))
    (ensures (B.loc_in (c.footprint #i h s) h))
    [SMTPat (c.invariant h s)]
  =
    c.invariant_loc_in_footprint #i h s
  in
  ()
#pop-options
