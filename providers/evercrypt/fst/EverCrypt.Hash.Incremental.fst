module EverCrypt.Hash.Incremental

open FStar.Mul

// Watch out: keep the module declarations in sync between fsti and fst
// (otherwise interleaving issues may bite).
module B = LowStar.Buffer
module S = FStar.Seq
module ST = FStar.HyperStack.ST
module HS = FStar.HyperStack
module G = FStar.Ghost
module U32 = FStar.UInt32
module U64 = FStar.UInt64

module Hash = EverCrypt.Hash

open FStar.HyperStack.ST
open Spec.Hash.Definitions

#set-options "--max_fuel 0 --max_ifuel 0"

let _: squash (inversion Hash.alg) = allow_inversion Hash.alg

/// State

noeq
type state_s a =
| State:
    hash_state: Hash.state a ->
    buf: B.buffer UInt8.t { B.length buf = block_length a } ->
    total_len: UInt64.t ->
    state_s a

let freeable (#a: alg) (h: HS.mem) (p: state a) =
  B.freeable p /\ (
  let s = B.deref h p in
  let State hash_state buf _ = s in
  B.freeable buf /\ Hash.freeable h hash_state)

let footprint_s #a h (s: state_s a) =
  let State hash_state buf_ _ = s in
  B.(loc_union (loc_addr_of_buffer buf_) (Hash.footprint hash_state h))

let invariant_s #a h s =
  let State hash_state buf_ _ = s in
  B.live h buf_ /\ Hash.invariant hash_state h /\
  B.(loc_disjoint (loc_buffer buf_) (Hash.footprint hash_state h))

#push-options "--max_ifuel 1"
let invariant_loc_in_footprint #a s m =
  ()
#pop-options

/// Hashes

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

let hashes (#a: Hash.alg) (h: HS.mem) (s: state a) (b: bytes) =
  let State hash_state buf_ total_len = B.deref h s in
  let blocks, rest = split_at_last a b in
  S.length blocks + S.length rest = U64.v total_len /\
  S.length b = U64.v total_len /\
  U64.v total_len < pow2 61 /\
  S.equal (Hash.repr hash_state h) (Spec.Hash.update_multi a (Spec.Hash.init a) blocks) /\
  S.equal (S.slice (B.as_seq h buf_) 0 (U64.v total_len % block_length a)) rest

let hash_fits #a h s b =
  assert_norm (pow2 61 < pow2 125);
  ()

/// Framing

#push-options "--max_ifuel 1"

let frame_invariant #a l s h0 h1 =
  let hash_state = State?.hash_state (B.deref h0 s) in
  Hash.frame_invariant #a l hash_state h0 h1;
  Hash.frame_invariant_implies_footprint_preservation #a l hash_state h0 h1

let frame_hashes #a l s b h0 h1 =
  let hash_state = State?.hash_state (B.deref h0 s) in
  Hash.frame_invariant #a l hash_state h0 h1

let frame_freeable #a l s h0 h1 =
  ()

#reset-options "--max_fuel 0 --max_ifuel 0"

let split_at_last_empty (a: Hash.alg): Lemma
  (ensures (
    let blocks, rest = split_at_last a S.empty in
    S.equal blocks S.empty /\ S.equal rest S.empty))
=
  ()

let create_in a r =
  // Allocate all the state
  let h0 = ST.get () in
  let buf = B.malloc r 0uy (Hacl.Hash.Definitions.block_len a) in
  let h1 = ST.get () in
  assert (Hash.fresh_loc (B.loc_buffer buf) h0 h1);
  let hash_state = Hash.create_in a r in
  let h2 = ST.get () in
  assert (Hash.fresh_loc (Hash.footprint hash_state h2) h0 h2);
  assert (Hash.fresh_loc (B.loc_buffer buf) h0 h2);
  let s = State hash_state buf 0UL in
  assert (Hash.fresh_loc (footprint s h2) h0 h2);

  Hash.init #(G.hide a) hash_state;

  let h3 = ST.get () in
  Spec.Hash.Lemmas.update_multi_zero a (Hash.repr hash_state h3);
  split_at_last_empty a;
  assert (Hash.invariant hash_state h3);
  assert (v 0ul <= B.length buf);
  assert (
    let blocks, rest = split_at_last a S.empty in
    S.equal blocks S.empty /\ S.equal rest S.empty /\
    Spec.Hash.(S.equal (update_multi a (init a) S.empty) (init a)));
  assert (S.equal (Hash.repr hash_state h3) (Spec.Hash.init a));
  assert (hashes h3 s S.empty);
  assert (freeable s h3);
  assert (Hash.fresh_loc (footprint s h3) h0 h3);
  assert (B.modifies (footprint s h3) h0 h3);
  B.modifies_only_not_unused_in B.loc_none h0 h3;
  assert (B.modifies B.loc_none h0 h3);
  s

/// We keep the total length at run-time, on 64 bits, but require that it abides
/// by the size requirements for the smaller hashes -- we're not interested at
/// this stage in having an agile type for lengths that would be up to 2^125 for
/// SHA384/512.

inline_for_extraction noextract
let rest a (total_len: UInt64.t): (x:UInt32.t { v x = v total_len % block_length a }) =
  let open FStar.Int.Cast.Full in
  uint64_to_uint32 (total_len % uint32_to_uint64 (Hacl.Hash.Definitions.block_len a))

inline_for_extraction noextract
let add_len (total_len: UInt64.t) (len: UInt32.t):
  Pure UInt64.t
    (requires v total_len + v len < pow2 61)
    (ensures fun x -> v x = v total_len + v len /\ v x < pow2 61)
=
  assert_norm (pow2 61 < pow2 64);
  total_len + Int.Cast.uint32_to_uint64 len

#push-options "--z3rlimit 20"

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
      v len < block_length a - v (rest a (State?.total_len s)))
    (ensures fun h0 s' h1 ->
      update_post a s s' prev data len h0 h1)

let split_at_last_small (a: Hash.alg) (b: bytes) (d: bytes): Lemma
  (requires (
    let _, rest = split_at_last a b in
    S.length rest + S.length d < block_length a))
  (ensures (
    let blocks, rest = split_at_last a b in
    let blocks', rest' = split_at_last a (S.append b d) in
    S.equal blocks blocks' /\ S.equal (S.append rest d) rest'))
=
  let blocks, rest = split_at_last a b in
  let blocks', rest' = split_at_last a (S.append b d) in
  let l = block_length a in

  (* Looking at the definition of split_at_last, blocks depends only on S.length b / l. *)
  calc (==) {
    S.length b / l;
  (==) { (* definition *) }
    (S.length blocks + S.length rest) / l;
  (==) { Math.Lemmas.lemma_div_exact (S.length blocks) l }
    (l * (S.length blocks / l) + S.length rest) / l;
  (==) { }
    (S.length rest + (S.length blocks / l) * l) / l;
  (==) { Math.Lemmas.lemma_div_plus (S.length rest) (S.length blocks / l) l }
    (S.length rest) / l + (S.length blocks / l);
  (==) { Math.Lemmas.small_div (S.length rest) l }
    S.length blocks / l;
  };

  calc (==) {
    S.length (S.append b d) / l;
  (==) { (* definition *) }
    (S.length blocks + S.length rest + S.length d) / l;
  (==) { Math.Lemmas.lemma_div_exact (S.length blocks) l }
    (l * (S.length blocks / l) + (S.length rest + S.length d)) / l;
  (==) { }
    ((S.length rest + S.length d) + (S.length blocks / l) * l) / l;
  (==) { Math.Lemmas.lemma_div_plus (S.length rest + S.length d) (S.length blocks / l) l }
    (S.length rest + S.length d) / l + (S.length blocks / l);
  (==) { Math.Lemmas.small_div (S.length rest + S.length d) l }
    S.length blocks / l;
  };

  assert (S.equal blocks blocks');

  calc (S.equal) {
    rest `S.append` d;
  (S.equal) { (* definition *) }
    S.slice b ((S.length b / l) * l) (S.length b) `S.append` d;
  (S.equal) { }
    S.slice (S.append b d) ((S.length b / l) * l) (S.length b) `S.append` d;
  (S.equal) { (* above *) }
    S.slice (S.append b d) ((S.length (S.append b d) / l) * l) (S.length b) `S.append` d;
  (S.equal) { (* ? *) }
    S.slice (S.append b d) ((S.length (S.append b d) / l) * l) (S.length b)
    `S.append`
    S.slice (S.append b d) (S.length b) (S.length (S.append b d));
  (S.equal) { S.lemma_split (S.append b d) ((S.length (S.append b d) / l) * l) }
    S.slice (S.append b d) ((S.length (S.append b d) / l) * l) (S.length b + S.length d);
  (S.equal) { S.lemma_len_append b d }
    S.slice (S.append b d) ((S.length (S.append b d) / l) * l) (S.length (S.append b d));
  (S.equal) { }
    rest';
  };

  ()

#pop-options

#push-options "--z3rlimit 100"
let add_len_small a (total_len: UInt64.t) (len: UInt32.t): Lemma
  (requires
    v len < block_length a - v (rest a total_len) /\
    v total_len + v len < pow2 61)
  (ensures (rest a (add_len total_len len) = rest a total_len + len))
=
  FStar.Math.Lemmas.small_modulo_lemma_1 (v len) (block_length a);
  FStar.Math.Lemmas.modulo_distributivity (v total_len) (v len) (block_length a)
#pop-options

#push-options "--z3rlimit 100"
let update_small a s prev data len =
  let State hash_state buf total_len = s in
  let sz = rest a total_len in
  add_len_small a total_len len;
  let h0 = ST.get () in
  let buf1 = B.sub buf 0ul sz in
  let buf2 = B.sub buf sz len in
  B.blit data 0ul buf2 0ul len;
  let h1 = ST.get () in
  split_at_last_small a (G.reveal prev) (B.as_seq h0 data);
  Hash.frame_invariant (B.loc_buffer buf) hash_state h0 h1;
  Hash.frame_invariant_implies_footprint_preservation (B.loc_buffer buf) hash_state h0 h1;
  let s' = State hash_state buf (add_len total_len len) in
  assert (hashes h1 s' (S.append (G.reveal prev) (B.as_seq h0 data)));
  assert (footprint s h0 == footprint s h1);
  assert (preserves_freeable s h0 h1);
  s'
#pop-options

#set-options "--z3rlimit 60"
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
  let l = block_length a in
  calc (S.equal) {
    rest';
  (S.equal) { }
    snd (split_at_last a d);
  (S.equal) { }
    S.slice d ((S.length d / l) * l) (S.length d);
  (S.equal) { }
    S.slice (S.append b d) (S.length b + (S.length d / l) * l) (S.length b + S.length d);
  (S.equal) { }
    S.slice (S.append b d) (S.length b + (S.length d / l) * l) (S.length (S.append b d));
  (S.equal) { Math.Lemmas.div_exact_r (S.length b) l }
    // For some reason this doesn't go through with the default rlimit, even
    // though this is a direct rewriting based on the application of the lemma
    // above.
    S.slice (S.append b d) ((S.length b / l) * l + (S.length d / l) * l) (S.length (S.append b d));
  (S.equal) { Math.Lemmas.distributivity_add_left (S.length b / l) (S.length d / l) l }
    S.slice (S.append b d) ((S.length b / l + S.length d / l) * l) (S.length (S.append b d));
  (S.equal) { Math.Lemmas.lemma_div_plus (S.length d) (S.length b / l) l }
    S.slice (S.append b d) (((S.length b + S.length d) / l) * l) (S.length (S.append b d));
  (S.equal) { }
    snd (S.split (S.append b d) (((S.length (S.append b d)) / l) * l));
  (S.equal) { }
    rest'';
  };

  calc (S.equal) {
    S.append blocks blocks';
  (S.equal) { (* rest = S.empty *) }
    S.append (S.append blocks rest) blocks';
  (S.equal) { }
    S.append b blocks';
  (S.equal) { }
    S.append b (fst (split_at_last a d));
  (S.equal) { (* definition of split_at_last *) }
    S.append b (fst (S.split d ((S.length d / l) * l)));
  (S.equal) { (* definition of split *) }
    S.append b (S.slice d 0 ((S.length d / l) * l));
  (S.equal) { }
    S.slice (S.append b d) 0 (S.length b + (S.length d / l) * l);
  (S.equal) { Math.Lemmas.div_exact_r (S.length b) l }
    S.slice (S.append b d) 0 ((S.length b / l) * l + (S.length d / l) * l);
  (S.equal) { Math.Lemmas.distributivity_add_left (S.length b / l) (S.length d / l) l }
    S.slice (S.append b d) 0 ((S.length b / l + S.length d / l) * l);
  (S.equal) { Math.Lemmas.lemma_div_plus (S.length d) (S.length b / l) l }
    S.slice (S.append b d) 0 (((S.length b + S.length d) / l) * l);
  (S.equal) { }
    fst (S.split (S.append b d) (((S.length (S.append b d)) / l) * l));
  (S.equal) { }
    blocks'';
  }

/// Case 2: we have no buffered data.
val update_empty_buf:
  a:Hash.alg ->
  s:state a ->
  prev:G.erased bytes ->
  data: B.buffer UInt8.t ->
  len: UInt32.t ->
  Stack (state a)
    (requires fun h0 ->
      update_pre a s prev data len h0 /\
      rest a (State?.total_len s) = 0ul)
    (ensures fun h0 s' h1 ->
      update_post a s s' prev data len h0 h1)

#push-options "--z3rlimit 150"
let update_empty_buf a s prev data len =
  let State hash_state buf total_len = s in
  let sz = rest a total_len in
  let h0 = ST.get () in
  assert (
    let blocks, rest = split_at_last a (G.reveal prev) in
    S.equal blocks (G.reveal prev) /\
    S.equal rest S.empty);
  split_at_last_blocks a (G.reveal prev) (B.as_seq h0 data);
  let n_blocks = len / Hacl.Hash.Definitions.block_len a in
  let data1_len = n_blocks `U32.mul` Hacl.Hash.Definitions.block_len a in
  let data2_len = len `U32.sub` data1_len in
  let data1 = B.sub data 0ul data1_len in
  let data2 = B.sub data data1_len data2_len in
  Hash.update_multi #(G.hide a) hash_state data1 data1_len;

  let dst = B.sub buf 0ul data2_len in
  let h1 = ST.get () in
  B.blit data2 0ul dst 0ul data2_len;
  let h2 = ST.get () in
  Hash.frame_invariant (B.loc_buffer buf) hash_state h1 h2;
  Hash.frame_invariant_implies_footprint_preservation (B.loc_buffer buf) hash_state h1 h2;

  assert (S.equal
    (S.append (S.append (G.reveal prev) (B.as_seq h0 data1)) (B.as_seq h0 data2))
    (S.append (G.reveal prev) (S.append (B.as_seq h0 data1) (B.as_seq h0 data2))));

  State hash_state buf (add_len total_len len)
#pop-options


/// Case 3: we are given just enough data to end up on the boundary
#push-options "--z3rlimit 200"
val update_round:
  a:Hash.alg ->
  s:state a ->
  prev:G.erased bytes ->
  data: B.buffer UInt8.t ->
  len: UInt32.t ->
  Stack (state a)
    (requires fun h0 ->
      update_pre a s prev data len h0 /\ (
      let r = rest a (State?.total_len s) in
      v len + v r = block_length a /\
      r <> 0ul))
    (ensures fun h0 s' h1 ->
      update_post a s s' prev data len h0 h1 /\
      v (State?.total_len s') % block_length a = 0)

let split_at_last_block (a: Hash.alg) (b: bytes) (d: bytes): Lemma
  (requires (
    let _, rest = split_at_last a b in
    S.length rest + S.length d = block_length a))
  (ensures (
    let blocks, rest = split_at_last a b in
    let blocks', rest' = split_at_last a (S.append b d) in
    S.equal (S.append b d) blocks' /\ S.equal S.empty rest'))
=
   ()

let update_round a s prev data len =
  let State hash_state buf_ total_len = s in
  let h0 = ST.get () in
  let sz = rest a total_len in
  let diff = Hacl.Hash.Definitions.block_len a - sz in
  let buf0 = B.sub buf_ 0ul (Hacl.Hash.Definitions.block_len a) in
  let buf1 = B.sub buf0 0ul sz in
  let buf2 = B.sub buf0 sz diff in
  assert (B.(loc_pairwise_disjoint
    [ loc_buffer buf1; loc_buffer buf2; loc_buffer data; ]));
  B.blit data 0ul buf2 0ul diff;
  let h1 = ST.get () in
  assert (S.equal (B.as_seq h1 buf0) (S.append (B.as_seq h1 buf1) (B.as_seq h1 data)));
  Hash.frame_invariant (B.loc_buffer buf_) hash_state h0 h1;
  Hash.frame_invariant_implies_footprint_preservation (B.loc_buffer buf_) hash_state h0 h1;
  Hash.update_multi #(G.hide a) hash_state buf0 (Hacl.Hash.Definitions.block_len a);
  let h2 = ST.get () in
  // JP: no clue why I had to go through all these manual steps.
  (
    let open Spec.Hash in
    let blocks, rest = split_at_last a (G.reveal prev) in
    assert (S.equal (Hash.repr hash_state h2)
      (update_multi a (Hash.repr hash_state h1) (B.as_seq h1 buf0)));
    assert (S.equal (B.as_seq h0 buf1) (B.as_seq h1 buf1));
    assert (S.equal rest (B.as_seq h1 buf1));
    assert (S.equal (B.as_seq h0 data) (B.as_seq h1 data));
    assert (S.equal (B.as_seq h1 buf0) (S.append (B.as_seq h1 buf1) (B.as_seq h1 data)));
    assert (S.equal (Hash.repr hash_state h2)
      (update_multi a (Spec.Hash.init a)
        (S.append blocks (B.as_seq h1 buf0))));
    assert (S.equal (Hash.repr hash_state h2)
      (update_multi a (Spec.Hash.init a)
        (S.append blocks (S.append (B.as_seq h1 buf1) (B.as_seq h1 data)))));
    S.append_assoc blocks (B.as_seq h1 buf1) (B.as_seq h1 data);
    assert (S.equal (Hash.repr hash_state h2)
      (update_multi a (Spec.Hash.init a)
        (S.append (S.append blocks (B.as_seq h1 buf1)) (B.as_seq h1 data))));
    assert (S.equal (S.append blocks rest) (G.reveal prev));
    assert (S.equal (Hash.repr hash_state h2)
      (update_multi a (Spec.Hash.init a)
        (S.append (G.reveal prev) (B.as_seq h1 data))));
    assert (S.equal (Hash.repr hash_state h2)
      (update_multi a (Spec.Hash.init a)
        (S.append (G.reveal prev) (B.as_seq h0 data))));
    split_at_last_block a (G.reveal prev) (B.as_seq h0 data);
    let blocks', rest' = split_at_last a (S.append (G.reveal prev) (B.as_seq h0 data)) in
    assert (S.equal rest' S.empty);
    assert (B.live h2 buf_ /\
      B.(loc_disjoint (loc_buffer buf_) (Hash.footprint hash_state h2)) /\
      Hash.invariant hash_state h2);
    ()
  );
  let s' = State hash_state buf_ (add_len total_len len) in
  assert (hashes h2 s' (S.append (G.reveal prev) (B.as_seq h0 data)));
  s'
#pop-options

#push-options "--z3rlimit 200"
let update a s prev data len =
  let State hash_state buf_ total_len = s in
  let sz = rest a total_len in
  if len < Hacl.Hash.Definitions.block_len a - sz then
    update_small a s prev data len
  else if sz = 0ul then
    update_empty_buf a s prev data len
  else begin
    let h0 = ST.get () in
    let diff = Hacl.Hash.Definitions.block_len a - sz in
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

inline_for_extraction noextract
val mk_finish: a:Hash.alg -> finish_st a

#reset-options "--z3rlimit 30 --max_fuel 0 --max_ifuel 0"
inline_for_extraction noextract
let mk_finish a s prev dst =
  let h0 = ST.get () in
  let State hash_state buf_ total_len = s in

  push_frame ();
  let h1 = ST.get () in
  Hash.frame_invariant B.loc_none hash_state h0 h1;
  Hash.frame_invariant_implies_footprint_preservation B.loc_none hash_state h0 h1;
  assert (Hash.invariant hash_state h1);

  assert_norm (pow2 61 < pow2 125);
  assert (v total_len < max_input_length a);
  let buf_ = B.sub buf_ 0ul (rest a total_len) in
  assert (
    let r = rest a total_len in
    (v total_len - v r) % block_length a = 0);

  let tmp_hash_state = Hash.alloca a in

  let h2 = ST.get () in
  assert (B.(loc_disjoint (Hash.footprint tmp_hash_state h2) (Hash.footprint hash_state h1)));
  Hash.frame_invariant B.(loc_region_only false (HS.get_tip h2)) hash_state h1 h2;
  Hash.frame_invariant_implies_footprint_preservation
    B.(loc_region_only false (HS.get_tip h2)) hash_state h1 h2;
  assert (Hash.invariant hash_state h2);
  assert (Hash.invariant tmp_hash_state h2);
  assert (Hash.footprint hash_state h2 == Hash.footprint hash_state h1);

  Hash.copy #(G.hide a) hash_state tmp_hash_state;

  let h3 = ST.get () in
  assert (Hash.footprint tmp_hash_state h2 == Hash.footprint tmp_hash_state h3);
  Hash.frame_invariant (Hash.footprint tmp_hash_state h2) hash_state h2 h3;
  Hash.frame_invariant_implies_footprint_preservation
    (Hash.footprint tmp_hash_state h2) hash_state h2 h3;
  assert (Hash.invariant hash_state h3);
  EverCrypt.Hash.update_last #(G.hide a) tmp_hash_state buf_ total_len;

  let h4 = ST.get () in
  Hash.frame_invariant (Hash.footprint tmp_hash_state h3) hash_state h3 h4;
  Hash.frame_invariant_implies_footprint_preservation
    (Hash.footprint tmp_hash_state h3) hash_state h3 h4;
  assert (Hash.invariant hash_state h4);

  EverCrypt.Hash.finish #(G.hide a) tmp_hash_state dst;

  let h5 = ST.get () in
  begin
    let open Spec.Hash.PadFinish in
    let open Spec.Hash in
    let prev = G.reveal prev in
    let n = S.length prev / block_length a in
    let blocks, rest_ = S.split prev (n * block_length a) in
    calc (S.equal) {
      B.as_seq h5 dst;
    (S.equal) { }
      finish a (Hash.repr tmp_hash_state h4);
    (S.equal) { }
      finish a (
        update_multi a (Hash.repr tmp_hash_state h3)
          (S.append
            (S.slice (B.as_seq h3 buf_) 0 (v (rest a total_len)))
            (pad a (UInt64.v total_len))));
    (S.equal) { }
      finish a (
        update_multi a
          (update_multi a (init a) blocks)
          (S.append rest_ (pad a (UInt64.v total_len))));
    (S.equal) { }
      finish a (
        update_multi a (init a)
          (S.append blocks (S.append rest_ (pad a (UInt64.v total_len)))));
    (S.equal) { S.append_assoc blocks rest_ (pad a (UInt64.v total_len)) }
      finish a (
        update_multi a (init a)
          (S.append (S.append blocks rest_) (pad a (UInt64.v total_len))));
    (S.equal) { Spec.Hash.Lemmas.hash_is_hash_incremental a prev }
      Spec.Hash.hash a prev;
    }
  end;

  Hash.frame_invariant (B.loc_buffer dst) hash_state h4 h5;
  Hash.frame_invariant_implies_footprint_preservation
    (B.loc_buffer dst) hash_state h4 h5;
  assert (Hash.invariant hash_state h5);

  pop_frame ();
  let h6 = ST.get () in
  Hash.frame_invariant B.(loc_region_only false (HS.get_tip h5)) hash_state h5 h6;
  Hash.frame_invariant_implies_footprint_preservation
    B.(loc_region_only false (HS.get_tip h5)) hash_state h5 h6;
  assert (hashes h6 s (G.reveal prev));

  (*
   * AR: 02/14: This is hard. In emacs, the lemma calls are not needed
   *            Whereas on the command line, proof doesn't work without
   *            With log_queries, the differences between the two are:
   *            -- Comments
   *            -- More push calls in emacs
   *            -- The name of one non total arrow symbol (_288 vs _327)
   *            Can't do much about it, may be can investigate the gensym difference
   *)
  let mloc = B.loc_union (B.loc_buffer dst) (footprint s h0) in
  B.modifies_remove_fresh_frame h0 h1 h6 mloc;
  B.popped_modifies h5 h6;
  assert (B.(modifies mloc h0 h6))

  // So much for automated proofs.

/// The wrapper pattern, to ensure that the stack-allocated state is properly
/// monomorphized.
let finish_md5: finish_st MD5 = mk_finish MD5
let finish_sha1: finish_st SHA1 = mk_finish SHA1
let finish_sha224: finish_st SHA2_224 = mk_finish SHA2_224
let finish_sha256: finish_st SHA2_256 = mk_finish SHA2_256
let finish_sha384: finish_st SHA2_384 = mk_finish SHA2_384
let finish_sha512: finish_st SHA2_512 = mk_finish SHA2_512

let finish a s prev dst =
  match a with
  | MD5 -> finish_md5 s prev dst
  | SHA1 -> finish_sha1 s prev dst
  | SHA2_224 -> finish_sha224 s prev dst
  | SHA2_256 -> finish_sha256 s prev dst
  | SHA2_384 -> finish_sha384 s prev dst
  | SHA2_512 -> finish_sha512 s prev dst

let free a s =
  let State hash_state buf _ = s in
  Hash.free #(Ghost.hide a) hash_state;
  B.free buf
