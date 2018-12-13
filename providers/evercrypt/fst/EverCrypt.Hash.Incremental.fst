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

/// We split update into several versions, to all be simplified into a single
/// large one at extraction-time.

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

/// Case 1: we just need to grow the buffer, no call to the hash function.
val update_small:
  a:Hash.alg ->
  s:state a ->
  prev:G.erased bytes ->
  data: B.buffer UInt8.t ->
  len: UInt32.t ->
  Stack (state a)
    (requires fun h0 ->
      update_pre a s prev data len h0 /\
      v len < size_block a - v (State?.buf_size s))
    (ensures fun h0 s' h1 ->
      update_post a s s' prev data len h0 h1)

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

// Larger rlimit required for batch mode.
#push-options "--z3rlimit 300 --z3refresh"
let update_small a s prev data len =
  let State hash_state buf sz = s in
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
#pop-options

/// Case 2: we have no buffered data *and* the input is a multiple of the block length.
val update_no_copy:
  a:Hash.alg ->
  s:state a ->
  prev:G.erased bytes ->
  data: B.buffer UInt8.t ->
  len: UInt32.t ->
  Stack (state a)
    (requires fun h0 ->
      update_pre a s prev data len h0 /\
      State?.buf_size s = 0ul /\
      B.length data % size_block a = 0)
    (ensures fun h0 s' h1 ->
      update_post a s s' prev data len h0 h1)

#push-options "--z3rlimit 100"
let update_no_copy a s prev data len =
  let State hash_state buf sz = s in
  Hash.update_multi #(G.hide a) hash_state data len;
  s
#pop-options

/// Case 3: we have no buffered data
val update_empty_buf:
  a:Hash.alg ->
  s:state a ->
  prev:G.erased bytes ->
  data: B.buffer UInt8.t ->
  len: UInt32.t ->
  Stack (state a)
    (requires fun h0 ->
      update_pre a s prev data len h0 /\
      State?.buf_size s = 0ul)
    (ensures fun h0 s' h1 ->
      update_post a s s' prev data len h0 h1)

#set-options "--z3rlimit 100"
let split_at_last_blocks (a: Hash.alg) (b: bytes) (d: bytes): Lemma
  (requires (
    let blocks, rest = split_at_last a b in
    S.equal rest S.empty))
  (ensures (
    let blocks, rest = split_at_last a b in
    let blocks', rest' = split_at_last a d in
    let blocks'', rest'' = split_at_last a (S.append b d) in
    S.equal blocks'' (S.append blocks blocks') /\
    S.equal rest' rest''))
=
  let blocks, rest = split_at_last a b in
  let blocks', rest' = split_at_last a d in
  let blocks'', rest'' = split_at_last a (S.append b d) in
  let b' = S.append blocks rest in
  let d' = S.append blocks' rest' in
  assert (S.equal (S.append b' d') (S.append blocks'' rest''));
  assert (S.equal b' blocks);
  assert (S.equal (S.append b' d') (S.append (S.append blocks blocks') rest'));
  assert (S.equal (S.append blocks'' rest'') (S.append (S.append blocks blocks') rest'));
  assert (S.length b % size_block a = 0);
  assert (S.length rest' = S.length rest'');
  Seq.Properties.append_slices (S.append blocks blocks') rest';
  Seq.Properties.append_slices blocks'' rest''

let update_empty_buf a s prev data len =
  let State hash_state buf sz = s in
  let h0 = ST.get () in
  assert (
    let blocks, rest = split_at_last a (G.reveal prev) in
    S.equal blocks (G.reveal prev) /\
    S.equal rest S.empty);
  split_at_last_blocks a (G.reveal prev) (B.as_seq h0 data);
  let n_blocks = len / size_block_ul a in
  let data1_len = n_blocks * size_block_ul a in
  let data2_len = len - data1_len in
  let data1 = B.sub data 0ul data1_len in
  let data2 = B.sub data data1_len data2_len in
  Hash.update_multi #(G.hide a) hash_state data1 data1_len;

  let dst = B.sub buf 0ul data2_len in
  let h1 = ST.get () in
  B.blit data2 0ul dst 0ul data2_len;
  let h2 = ST.get () in
  B.modifies_inert_intro (B.loc_buffer buf) h1 h2;
  Hash.frame_invariant (B.loc_buffer buf) hash_state h1 h2;
  Hash.frame_invariant_implies_footprint_preservation (B.loc_buffer buf) hash_state h1 h2;

  assert (S.equal
    (S.append (S.append (G.reveal prev) (B.as_seq h0 data1)) (B.as_seq h0 data2))
    (S.append (G.reveal prev) (S.append (B.as_seq h0 data1) (B.as_seq h0 data2))));

  State hash_state buf data2_len


/// Case 4: we are given just enough data to end up on the boundary
val update_round:
  a:Hash.alg ->
  s:state a ->
  prev:G.erased bytes ->
  data: B.buffer UInt8.t ->
  len: UInt32.t ->
  Stack (state a)
    (requires fun h0 ->
      update_pre a s prev data len h0 /\
      v len + v (State?.buf_size s) = size_block a /\
      State?.buf_size s <> 0ul)
    (ensures fun h0 s' h1 ->
      update_post a s s' prev data len h0 h1 /\
      State?.buf_size s' = 0ul)

let split_at_last_block (a: Hash.alg) (b: bytes) (d: bytes): Lemma
  (requires (
    let _, rest = split_at_last a b in
    S.length rest + S.length d = size_block a))
  (ensures (
    let blocks, rest = split_at_last a b in
    let blocks', rest' = split_at_last a (S.append b d) in
    S.equal (S.append b d) blocks' /\ S.equal S.empty rest'))
=
   ()

let _ = ()

#push-options "--z3rlimit 200"
let update_round a s prev data len =
  let State hash_state buf sz = s in
  let h0 = ST.get () in
  let diff = size_block_ul a - sz in
  let buf0 = B.sub buf 0ul (size_block_ul a) in
  let buf1 = B.sub buf0 0ul sz in
  let buf2 = B.sub buf0 sz diff in
  assert (B.(loc_pairwise_disjoint
    [ loc_buffer buf1; loc_buffer buf2; loc_buffer data; ]));
  B.blit data 0ul buf2 0ul diff;
  let h1 = ST.get () in
  assert (S.equal (B.as_seq h1 buf0) (S.append (B.as_seq h1 buf1) (B.as_seq h1 data)));
  B.modifies_inert_intro (B.loc_buffer buf) h0 h1;
  Hash.frame_invariant (B.loc_buffer buf) hash_state h0 h1;
  Hash.frame_invariant_implies_footprint_preservation (B.loc_buffer buf) hash_state h0 h1;
  Hash.update_multi #(G.hide a) hash_state buf0 (size_block_ul a);
  let h2 = ST.get () in
  // JP: no clue why I had to go through all these manual steps.
  (
    let blocks, rest = split_at_last a (G.reveal prev) in
    assert (S.equal (Hash.repr hash_state h2)
      (Hash.compress_many (Hash.repr hash_state h1) (B.as_seq h1 buf0)));
    assert (S.equal (B.as_seq h0 buf1) (B.as_seq h1 buf1));
    assert (S.equal rest (B.as_seq h1 buf1));
    assert (S.equal (B.as_seq h0 data) (B.as_seq h1 data));
    assert (S.equal (B.as_seq h1 buf0) (S.append (B.as_seq h1 buf1) (B.as_seq h1 data)));
    assert (S.equal (Hash.repr hash_state h2)
      (Hash.compress_many (Hash.acc0 #a)
        (S.append blocks (B.as_seq h1 buf0))));
    assert (S.equal (Hash.repr hash_state h2)
      (Hash.compress_many (Hash.acc0 #a)
        (S.append blocks (S.append (B.as_seq h1 buf1) (B.as_seq h1 data)))));
    S.append_assoc blocks (B.as_seq h1 buf1) (B.as_seq h1 data);
    assert (S.equal (Hash.repr hash_state h2)
      (Hash.compress_many (Hash.acc0 #a)
        (S.append (S.append blocks (B.as_seq h1 buf1)) (B.as_seq h1 data))));
    assert (S.equal (S.append blocks rest) (G.reveal prev));
    assert (S.equal (Hash.repr hash_state h2)
      (Hash.compress_many (Hash.acc0 #a)
        (S.append (G.reveal prev) (B.as_seq h1 data))));
    assert (S.equal (Hash.repr hash_state h2)
      (Hash.compress_many (Hash.acc0 #a)
        (S.append (G.reveal prev) (B.as_seq h0 data))));
    split_at_last_block a (G.reveal prev) (B.as_seq h0 data);
    let blocks', rest' = split_at_last a (S.append (G.reveal prev) (B.as_seq h0 data)) in
    assert (S.equal rest' S.empty);
    assert (B.live h2 buf /\
      B.(loc_disjoint (loc_buffer buf) (Hash.footprint hash_state h2)) /\
      Hash.invariant hash_state h2);
    ()
  );
  let s' = State hash_state buf 0ul in
  assert (hashes h2 s' (S.append (G.reveal prev) (B.as_seq h0 data)));
  s'
#pop-options

val update:
  a:Hash.alg ->
  s:state a ->
  prev:G.erased bytes ->
  data: B.buffer UInt8.t ->
  len: UInt32.t ->
  Stack (state a)
    (requires fun h0 -> update_pre a s prev data len h0)
    (ensures fun h0 s' h1 -> update_post a s s' prev data len h0 h1)

#push-options "--z3rlimit 200"
let update a s prev data len =
  let State hash_state buf sz = s in
  if len < size_block_ul a - sz then
    update_small a s prev data len
  else if sz = 0ul then
    update_empty_buf a s prev data len
  else begin
    let h0 = ST.get () in
    let diff = size_block_ul a - sz in
    let data1 = B.sub data 0ul diff in
    let data2 = B.sub data diff (len - diff) in
    let s1 = update_round a s prev data1 diff in
    let h1 = ST.get () in
    let s2 = update_empty_buf a s1
      (G.hide (S.append (G.reveal prev) (B.as_seq h0 data1))) data2 (len - diff)
    in
    let h2 = ST.get () in
    (
      let prev = G.reveal prev in
      assert (hashes h1 s1 (S.append prev (B.as_seq h0 data1)));
      assert (hashes h2 s2 (S.append (S.append prev (B.as_seq h0 data1)) (B.as_seq h0 data2)));
      S.append_assoc prev (B.as_seq h0 data1) (B.as_seq h0 data2);
      assert (S.equal (S.append (B.as_seq h0 data1) (B.as_seq h0 data2)) (B.as_seq h0 data));
      assert (S.equal
        (S.append (S.append prev (B.as_seq h0 data1)) (B.as_seq h0 data2))
        (S.append prev (B.as_seq h0 data)));
      assert (hashes h2 s2 (S.append prev (B.as_seq h0 data)));
      ()
    );
    s2
  end
#pop-options
