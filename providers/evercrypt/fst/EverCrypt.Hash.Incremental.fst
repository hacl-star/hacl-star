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

#set-options "--max_fuel 0 --max_ifuel 0"

let _: squash (inversion Hash.alg) = allow_inversion Hash.alg

let split_at_last_empty (a: Hash.alg): Lemma
  (ensures (
    let blocks, rest = split_at_last a S.empty in
    S.equal blocks S.empty /\ S.equal rest S.empty))
=
  ()

let create a =
  // Allocate all the state
  let h0 = ST.get () in
  let buf = B.malloc HS.root 0uy (2ul * Hacl.Hash.Definitions.size_block_ul a) in
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

/// We split update into several versions, to all be simplified into a single
/// large one at extraction-time.

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

/// Case 3: we have no buffered data. TODO: reuse case 2 above.
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

#push-options "--z3rlimit 100"
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
  let n_blocks = len / Hacl.Hash.Definitions.size_block_ul a in
  let data1_len = n_blocks * Hacl.Hash.Definitions.size_block_ul a in
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
#pop-options


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
  let diff = Hacl.Hash.Definitions.size_block_ul a - sz in
  let buf0 = B.sub buf 0ul (Hacl.Hash.Definitions.size_block_ul a) in
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
  Hash.update_multi #(G.hide a) hash_state buf0 (Hacl.Hash.Definitions.size_block_ul a);
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

#push-options "--z3rlimit 200"
let update a s prev data len =
  let State hash_state buf sz = s in
  if len < Hacl.Hash.Definitions.size_block_ul a - sz then
    update_small a s prev data len
  else if sz = 0ul then
    update_empty_buf a s prev data len
  else begin
    let h0 = ST.get () in
    let diff = Hacl.Hash.Definitions.size_block_ul a - sz in
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

friend Hacl.Hash.PadFinish
friend Hacl.Hash.MD

#push-options "--z3rlimit 100"
let finish a s prev len dst =
  let h0 = ST.get () in
  let State hash_state buf sz = s in

  // This reuses a bunch of stuff from Hacl.Hash.MD. The match below reduces for
  // extraction to the exact same code in the two branches. Ideally, we would have
  // a version of pad_len that works with uint32 or uint64, but that proof was
  // horrible to perform and I don't want to touch this code.
  let pad_len = match a with
    | SHA1 | MD5 | SHA2_224 | SHA2_256 ->
        [@ inline_let ] // JP: why?
        let len: len_t a = len in
        Hacl.Hash.PadFinish.pad_len a (Int.Cast.Full.uint32_to_uint64 len)
    | SHA2_384 | SHA2_512 ->
        Hacl.Hash.PadFinish.pad_len a
          (Int.Cast.Full.uint64_to_uint128 (Int.Cast.Full.uint32_to_uint64 len))
  in

  //Hacl.Hash.MD.pad_length_mod (v len - v sz) (v sz);
  assert (pad_length a (v len) <= 2 * size_block a);

  let buf0 = B.sub buf 0ul (sz + pad_len) in
  let buf1 = B.sub buf 0ul sz in
  let buf2 = B.sub buf sz pad_len in
  begin match a with
    | SHA1 | MD5 | SHA2_224 | SHA2_256 ->
        Hacl.Hash.PadFinish.pad a len buf2
    | SHA2_384 | SHA2_512 ->
        Hacl.Hash.PadFinish.pad a (Int.Cast.Full.uint64_to_uint128 len) buf2
  end;
  let h1 = ST.get () in

  B.modifies_inert_intro (B.loc_buffer buf) h0 h1;
  Hash.frame_invariant (B.loc_buffer buf) hash_state h0 h1;
  Hash.frame_invariant_implies_footprint_preservation (B.loc_buffer buf) hash_state h0 h1;
  EverCrypt.Hash.update_multi #(G.hide a) hash_state buf0 (sz + pad_len);
  EverCrypt.Hash.finish #(G.hide a) hash_state dst;
  EverCrypt.Hash.init #(G.hide a) hash_state;
  State hash_state buf 0ul
