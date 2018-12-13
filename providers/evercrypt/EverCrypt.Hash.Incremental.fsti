module EverCrypt.Hash.Incremental

open FStar.Mul

/// An alternative API on top of EverCrypt.Hash that holds an internal buffer.
/// No state abstraction for now, can be added later on as we wish.

module B = LowStar.Buffer
module S = FStar.Seq
module ST = FStar.HyperStack.ST
module HS = FStar.HyperStack
module G = FStar.Ghost

module Hash = EverCrypt.Hash

open FStar.HyperStack.ST
open Spec.Hash.Helpers
open FStar.Integers

noeq
type state a =
| State:
    hash_state: Hash.state a ->
    buf: B.buffer UInt8.t { B.length buf = 2 * size_block a } ->
    buf_size: UInt32.t ->
    state a

let footprint #a (s: state a) h =
  let State hash_state buf _ = s in
  B.(loc_union (loc_buffer buf) (Hash.footprint hash_state h))

let freeable #a (s: state a) h =
  let State hash_state buf _ = s in
  B.freeable buf /\ Hash.freeable h hash_state

let preserves_freeable #a (s: state a) (h0 h1: HS.mem) =
  let State hash_state buf _ = s in
  Hash.preserves_freeable hash_state h0 h1

noextract
let split_at_last (a: Hash.alg) (b: bytes):
  Pure (bytes_blocks a & bytes)
    (requires True)
    (ensures (fun (blocks, rest) ->
      S.length rest < size_block a /\
      S.length rest = S.length b % size_block a /\
      S.equal (S.append blocks rest) b))
=
  let n = S.length b / size_block a in
  let blocks, rest = S.split b (n * size_block a) in
  assert (S.length blocks = n * size_block a);
  assert ((n * size_block a) % size_block a = 0);
  assert (S.length rest = S.length b - n * size_block a);
  assert (S.length b - n * size_block a < size_block a);
  blocks, rest

unfold
let hashes (#a: Hash.alg) (h: HS.mem) (s: state a) (b: bytes) =
  let State hash_state buf sz = s in
  let blocks, rest = split_at_last a b in
  B.live h buf /\
  B.(loc_disjoint (loc_buffer buf) (Hash.footprint hash_state h)) /\
  Hash.invariant hash_state h /\
  v sz < size_block a /\
  S.equal (Hash.repr hash_state h) (Hash.compress_many (Hash.acc0 #a) blocks) /\
  S.equal (S.slice (B.as_seq h buf) 0 (v sz)) rest

let bytes = S.seq UInt8.t

val create (a: Hash.alg): ST (state a)
  (requires (fun _ -> True))
  (ensures (fun h0 s h1 ->
    hashes h1 s S.empty /\
    B.(modifies (footprint s h1) h0 h1) /\
    Hash.fresh_loc (footprint s h1) h0 h1 /\
    freeable s h1))

unfold
let update_pre
  (a: Hash.alg)
  (s: state a)
  (prev: G.erased bytes)
  (data: B.buffer UInt8.t)
  (len: UInt32.t)
  (h0: HS.mem)
=
  hashes h0 s (G.reveal prev) /\
  B.live h0 data /\
  v len = B.length data /\
  B.(loc_disjoint (loc_buffer data) (footprint s h0))

unfold
let update_post
  (a: Hash.alg)
  (s s': state a)
  (prev: G.erased bytes)
  (data: B.buffer UInt8.t)
  (len: UInt32.t)
  (h0 h1: HS.mem)
=
  B.(modifies (footprint s h0) h0 h1) /\
  footprint s h0 == footprint s' h1 /\
  hashes h1 s' (Seq.append (G.reveal prev) (B.as_seq h0 data)) /\
  preserves_freeable s h0 h1 /\
  State?.hash_state s == State?.hash_state s' /\
  State?.buf s == State?.buf s'

val update:
  a:Hash.alg ->
  s:state a ->
  prev:G.erased bytes ->
  data: B.buffer UInt8.t ->
  len: UInt32.t ->
  Stack (state a)
    (requires fun h0 -> update_pre a s prev data len h0)
    (ensures fun h0 s' h1 -> update_post a s s' prev data len h0 h1)

/// Writes out the final hash in the destination buffer, and resets the state.
/// Note: taking UInt32 here, but we could either do UInt64 (with pre-conditions
/// that the size does not overflow) or even len_t, with a layer of
/// specialization+multiplexing.
val finish:
  a:Hash.alg ->
  s:state a ->
  prev:G.erased bytes ->
  len:UInt32.t { UInt32.v len = S.length (G.reveal prev) } -> // JP: just v doesn't work (why?)
  dst: Hacl.Hash.Definitions.hash_t a ->
  Stack (state a)
    (requires fun h0 ->
      hashes h0 s (G.reveal prev) /\
      B.live h0 dst /\
      B.(loc_disjoint (loc_buffer dst) (footprint s h0)))
    (ensures fun h0 s' h1 ->
      B.(modifies (footprint s h0) h0 h1) /\
      footprint s h0 == footprint s' h1 /\
      hashes h1 s' S.empty /\
      preserves_freeable s h0 h1 /\
      State?.hash_state s == State?.hash_state s' /\
      State?.buf s == State?.buf s')
