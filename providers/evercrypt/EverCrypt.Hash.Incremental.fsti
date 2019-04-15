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
open Spec.Hash.Definitions
open FStar.Integers

noeq
type state a =
| State:
    hash_state: Hash.state a ->
    buf: B.buffer UInt8.t { B.length buf = block_length a } ->
    total_len: UInt64.t ->
    state a

let footprint #a (s: state a) h =
  let State hash_state buf_ _ = s in
  B.(loc_union (loc_buffer buf_) (Hash.footprint hash_state h))

let freeable #a (s: state a) h =
  let State hash_state buf _ = s in
  B.freeable buf /\ Hash.freeable h hash_state

let preserves_freeable #a (s: state a) (h0 h1: HS.mem) =
  let State hash_state buf _ = s in
  Hash.preserves_freeable hash_state h0 h1

/// A lemma to be used by all clients, to show that a stateful operation that
/// operates on a disjoint fragment of the heap preserves the invariants of this
/// module. Note: it might be useful to call `Hash.fresh_is_disjoint` to turn
/// the `fresh_loc` post-condition of create_in into a more useful
/// `loc_disjoint` clause.
let modifies_disjoint_preserves #a (l: B.loc) (h0 h1: HS.mem) (s: state a): Lemma
  (requires (
    let hash_state = State?.hash_state s in
    B.modifies l h0 h1 /\
    B.loc_disjoint l (footprint s h0) /\
    Hash.invariant hash_state h0))
  (ensures (
    let hash_state = State?.hash_state s in
    Hash.invariant hash_state h1 /\
    Hash.repr hash_state h1 == Hash.repr hash_state h0 /\
    footprint s h0 == footprint s h1))
=
  let hash_state = State?.hash_state s in
  Hash.frame_invariant l hash_state h0 h1;
  Hash.frame_invariant_implies_footprint_preservation l hash_state h0 h1

noextract
let split_at_last (a: Hash.alg) (b: bytes):
  Pure (bytes_blocks a & bytes)
    (requires True)
    (ensures (fun (blocks, rest) ->
      S.length rest < block_length a /\
      S.length rest = S.length b % block_length a /\
      S.equal (S.append blocks rest) b /\
      S.length blocks % block_length a = 0))
=
  let n = S.length b / block_length a in
  let blocks, rest = S.split b (n * block_length a) in
  assert (S.length blocks = n * block_length a);
  assert ((n * block_length a) % block_length a = 0);
  assert (S.length rest = S.length b - n * block_length a);
  assert (S.length b - n * block_length a < block_length a);
  blocks, rest

#set-options "--max_fuel 0 --max_ifuel 0"
unfold
let hashes (#a: Hash.alg) (h: HS.mem) (s: state a) (b: bytes) =
  let State hash_state buf_ total_len = s in
  let blocks, rest = split_at_last a b in
  S.length blocks + S.length rest = v total_len /\
  S.length b = v total_len /\
  v total_len < pow2 61 /\
  B.live h buf_ /\
  B.(loc_disjoint (loc_buffer buf_) (Hash.footprint hash_state h)) /\
  Hash.invariant hash_state h /\
  S.equal (Hash.repr hash_state h) (Hash.compress_many (Hash.acc0 #a) blocks) /\
  S.equal (S.slice (B.as_seq h buf_) 0 (v total_len % block_length a)) rest

noextract
let bytes = S.seq UInt8.t

(** @type: true
*)
val create_in (a: Hash.alg) (r: HS.rid): ST (state a)
  (requires (fun _ ->
    HyperStack.ST.is_eternal_region r))
  (ensures (fun h0 s h1 ->
    hashes h1 s S.empty /\
    B.(modifies loc_none h0 h1) /\
    Hash.fresh_loc (footprint s h1) h0 h1 /\
    B.(loc_includes (loc_region_only true r) (footprint s h1)) /\
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
  S.length (G.reveal prev) + v len < pow2 61 /\
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

(** @type: true
*)
val update:
  a:Hash.alg ->
  s:state a ->
  prev:G.erased bytes ->
  data: B.buffer UInt8.t ->
  len: UInt32.t ->
  Stack (state a)
    (requires fun h0 -> update_pre a s prev data len h0)
    (ensures fun h0 s' h1 -> update_post a s s' prev data len h0 h1)

/// Note: the state is left to be reused by the caller to feed more data into
/// the hash.
inline_for_extraction
let finish_st (a: Hash.alg) =
  s:state a ->
  prev:G.erased bytes ->
  dst: Hacl.Hash.Definitions.hash_t a ->
  Stack unit
    (requires fun h0 ->
      hashes h0 s (G.reveal prev) /\
      B.live h0 dst /\
      B.(loc_disjoint (loc_buffer dst) (footprint s h0)))
    (ensures fun h0 s' h1 ->
      assert_norm (pow2 61 < pow2 125);
      hashes h1 s (G.reveal prev) /\
      preserves_freeable s h0 h1 /\
      footprint s h0 == footprint s h1 /\
      B.(modifies (loc_union (loc_buffer dst) (footprint s h0)) h0 h1) /\
      S.equal (B.as_seq h1 dst) (Spec.Hash.hash a (G.reveal prev)))

(** @type: true
*)
val finish: a:Hash.alg -> finish_st a
