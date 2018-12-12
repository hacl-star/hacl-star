module EverCrypt.Hash.Incremental

open FStar.Mul

/// An alternative API on top of EverCrypt.Hash that holds an internal buffer.
/// No abstraction for now, can be added later on as we wish.

module B = LowStar.Buffer
module S = FStar.Seq
module ST = FStar.HyperStack.ST
module HS = FStar.HyperStack
module G = FStar.Ghost

module Hash = EverCrypt.Hash

open FStar.HyperStack.ST
open Spec.Hash.Helpers
open Hacl.Hash.Definitions
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

let bytes = S.seq UInt8.t

#set-options "--max_fuel 0 --max_ifuel 0"

let split_at_last (a: Hash.alg) (b: bytes):
  bytes_blocks a & (r: bytes {
    S.length r < size_block a
  })
=
  let n = S.length b / size_block a in
  let blocks, rest = S.split b (n * size_block a) in
  assert (S.length blocks = n * size_block a);
  assert ((n * size_block a) % size_block a = 0);
  assert (S.length rest = S.length b - n * size_block a);
  assert (S.length b - n * size_block a < size_block a);
  blocks, rest

let hashes (#a: Hash.alg) (h: HS.mem) (s: state a) (b: bytes) =
  let State hash_state buf sz = s in
  let blocks, rest = split_at_last a b in
  B.live h buf /\
  B.(loc_disjoint (loc_buffer buf) (Hash.footprint hash_state h)) /\
  Hash.invariant hash_state h /\
  v sz < size_block a /\
  S.equal (Hash.repr hash_state h) (Hash.compress_many (Hash.acc0 #a) blocks) /\
  S.equal (S.slice (B.as_seq h buf) 0 (v sz)) rest

let _: squash (inversion Hash.alg) = allow_inversion Hash.alg

val create (a: Hash.alg): ST (state a)
  (requires (fun _ -> True))
  (ensures (fun h0 s h1 ->
    hashes h1 s S.empty /\
    B.(modifies (footprint s h1) h0 h1) /\
    Hash.fresh_loc (footprint s h1) h0 h1 /\
    freeable s h1))

let split_at_last_empty (a: Hash.alg): Lemma
  (ensures (
    let blocks, rest = split_at_last a S.empty in
    S.equal blocks S.empty /\ S.equal rest S.empty))
=
  ()

let create a =
  // Allocate all the state
  let h0 = ST.get () in
  let buf = B.malloc HS.root 0uy (2ul * size_block_ul a) in
  let h1 = ST.get () in
  assert (Hash.fresh_loc (B.loc_buffer buf) h0 h1);
  let hash_state = Hash.create a in
  let h2 = ST.get () in
  assert (Hash.fresh_loc (Hash.footprint hash_state h2) h0 h2);
  assert (Hash.fresh_loc (B.loc_buffer buf) h0 h2);
  let s = State hash_state buf 0ul in
  assert (Hash.fresh_loc (footprint s h2) h0 h2);

  Hash.init #(G.hide a) hash_state;

  let h3 = ST.get () in
  // JP: I don't understand the need for this assertion. This proof fails if I
  // put the assertion further down.
  assert (ST.equal_stack_domains h0 h3);
  Spec.Hash.update_multi_zero a (Hash.repr hash_state h3);
  split_at_last_empty a;
  assert (Hash.invariant hash_state h3);
  assert (v 0ul <= B.length buf);
  assert (
    let blocks, rest = split_at_last a S.empty in
    S.equal blocks S.empty /\ S.equal rest S.empty /\
    S.equal (Hash.compress_many (Hash.acc0 #a) S.empty) (Hash.acc0 #a));
  assert (S.equal (Hash.repr hash_state h3) (Hash.acc0 #a));
  assert (hashes h3 s S.empty);
  assert (freeable s h3);
  assert (B.(modifies (footprint s h3) h0 h3));
  assert (Hash.fresh_loc (footprint s h3) h0 h3);
  s

let preserves_freeable #a (s: state a) (h0 h1: HS.mem) =
  let State hash_state buf _ = s in
  Hash.preserves_freeable hash_state h0 h1

val update:
  a:Hash.alg ->
  s:state a ->
  prev:G.erased bytes ->
  data: B.buffer UInt8.t ->
  len: UInt32.t ->
  Stack (state a)
    (requires fun h0 ->
      hashes h0 s (G.reveal prev) /\
      B.live h0 data /\
      v len = B.length data /\
      B.(loc_disjoint (loc_buffer data) (footprint s h0)))
    (ensures fun h0 s' h1 ->
      B.(modifies (footprint s h0) h0 h1) /\
      footprint s h0 == footprint s' h1 /\
      hashes h1 s' (Seq.append (G.reveal prev) (B.as_seq h0 data)) /\
      preserves_freeable s h0 h1 /\
      State?.hash_state s == State?.hash_state s' /\
      State?.buf s == State?.buf s')

let split_at_last_small (a: Hash.alg) (b: bytes) (d: bytes): Lemma
  (requires (
    let _, rest = split_at_last a b in
    S.length rest + S.length d < size_block a))
  (ensures (
    let blocks, rest = split_at_last a b in
    let blocks', rest' = split_at_last a (S.append b d) in
    S.equal blocks blocks' /\ S.equal (S.append rest d) rest'))
=
  ()

#push-options "--z3rlimit 200"
let update a s prev data len =
  let State hash_state buf sz = s in
  if len < size_block_ul a - sz then begin
    let h0 = ST.get () in
    let buf1 = B.sub buf 0ul sz in
    let buf2 = B.sub buf sz len in
    B.blit data 0ul buf2 0ul len;
    let h1 = ST.get () in
    split_at_last_small a (G.reveal prev) (B.as_seq h0 data);
    B.modifies_inert_intro (B.loc_buffer buf) h0 h1;
    Hash.frame_invariant (B.loc_buffer buf) hash_state h0 h1;
    Hash.frame_invariant_implies_footprint_preservation (B.loc_buffer buf) hash_state h0 h1;
    let s' = State hash_state buf (sz + len) in
    assert (hashes h1 s' (S.append (G.reveal prev) (B.as_seq h0 data)));
    assert (footprint s h0 == footprint s h1);
    assert (preserves_freeable s h0 h1);
    s'
  end else
    admit ()
