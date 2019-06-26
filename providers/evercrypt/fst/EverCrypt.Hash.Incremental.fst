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
    seen: G.erased bytes ->
    state_s a

let freeable (#a: alg) (h: HS.mem) (p: state a) =
  B.freeable p /\ (
  let s = B.deref h p in
  let State hash_state buf _ _ = s in
  B.freeable buf /\ Hash.freeable h hash_state)

let footprint_s #a h (s: state_s a) =
  let State hash_state buf_ _ _ = s in
  B.(loc_union (loc_addr_of_buffer buf_) (Hash.footprint hash_state h))

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

let invariant_s #a h s =
  let State hash_state buf_ total_len seen = s in
  let seen = G.reveal seen in
  let blocks, rest = split_at_last a seen in

  // Liveness and disjointness (administrative)
  B.live h buf_ /\ Hash.invariant hash_state h /\
  B.(loc_disjoint (loc_buffer buf_) (Hash.footprint hash_state h)) /\

  // Formerly, the "hashes" predicate
  S.length blocks + S.length rest = U64.v total_len /\
  S.length seen = U64.v total_len /\
  U64.v total_len < pow2 61 /\
  S.equal (Hash.repr hash_state h) (Spec.Hash.update_multi a (Spec.Hash.init a) blocks) /\
  S.equal (S.slice (B.as_seq h buf_) 0 (U64.v total_len % block_length a)) rest

#push-options "--max_ifuel 1"
let invariant_loc_in_footprint #a s m =
  ()
#pop-options

/// Hashes

let hashed (#a: Hash.alg) (h: HS.mem) (s: state a) =
  G.reveal (State?.seen (B.deref h s))

let hash_fits #a h s =
  assert_norm (pow2 61 < pow2 125)

let alg_of_state a s =
  let open LowStar.BufferOps in
  let State hash_state _ _ _ = !*s in
  Hash.alg_of_state a hash_state

/// Framing

#push-options "--max_ifuel 1"

let frame_invariant #a l s h0 h1 =
  let hash_state = State?.hash_state (B.deref h0 s) in
  Hash.frame_invariant #a l hash_state h0 h1;
  Hash.frame_invariant_implies_footprint_preservation #a l hash_state h0 h1

let frame_hashed #a l s h0 h1 =
  ()

let frame_freeable #a l s h0 h1 =
  ()

#pop-options

let split_at_last_empty (a: Hash.alg): Lemma
  (ensures (
    let blocks, rest = split_at_last a S.empty in
    S.equal blocks S.empty /\ S.equal rest S.empty))
=
  ()

#push-options "--z3rlimit 20"
let create_in a r =
  (**) let h0 = ST.get () in

  let buf = B.malloc r 0uy (Hacl.Hash.Definitions.block_len a) in
  (**) let h1 = ST.get () in
  (**) assert (B.fresh_loc (B.loc_buffer buf) h0 h1);

  let hash_state = Hash.create_in a r in
  (**) let h2 = ST.get () in
  (**) assert (B.fresh_loc (Hash.footprint hash_state h2) h0 h2);

  let s = State hash_state buf 0UL (G.hide S.empty) in
  (**) assert (B.fresh_loc (footprint_s h2 s) h0 h2);

  let p = B.malloc r s 1ul in
  (**) let h3 = ST.get () in
  (**) Hash.frame_invariant B.loc_none hash_state h2 h3;
  (**) Hash.frame_invariant_implies_footprint_preservation B.loc_none hash_state h2 h3;
  (**) assert (B.fresh_loc (footprint_s h3 s) h0 h3);
  (**) assert (B.fresh_loc (B.loc_addr_of_buffer p) h0 h3);

  Hash.init #(G.hide a) hash_state;
  (**) let h4 = ST.get () in
  (**) assert (B.fresh_loc (Hash.footprint hash_state h4) h0 h4);
  (**) assert (B.fresh_loc (B.loc_buffer buf) h0 h4);
  (**) Spec.Hash.Lemmas.update_multi_zero a (Hash.repr hash_state h4);
  (**) split_at_last_empty a;
  (**) B.modifies_only_not_unused_in B.loc_none h0 h4;

  p
#pop-options

#push-options "--z3refresh"
let init a s =
  let open LowStar.BufferOps in
  let h1 = ST.get () in
  let State hash_state buf _ _ = !*s in
  // JP: figuring out the alg at run-time is useful, but entails a lot more
  // proof difficulty; note the let-binding below, as well as the fact that
  // implicit argument resolution basically no longer works after this...
  let a = Hash.alg_of_state a hash_state in
  [@inline_let]
  let hash_state: Hash.state a = hash_state in

  Hash.init #(G.hide a) hash_state;
  let h2 = ST.get () in
  Spec.Hash.Lemmas.update_multi_zero a (Hash.repr #a hash_state h2);
  split_at_last_empty a;

  B.upd s 0ul (State hash_state buf 0UL (G.hide S.empty));
  let h3 = ST.get () in
  Hash.frame_invariant B.(loc_buffer s) hash_state h2 h3;
  Hash.frame_invariant_implies_footprint_preservation B.(loc_buffer s) hash_state h2 h3;
  assert (preserves_freeable #a s h1 h3);
  assert (invariant #a h3 s);
  assert B.(modifies (footprint #a h1 s) h1 h3);
  // This seems to cause insurmountable difficulties. Puzzled.
  assert (equal_domains h2 h3)
#pop-options

/// We keep the total length at run-time, on 64 bits, but require that it abides
/// by the size requirements for the smaller hashes -- we're not interested at
/// this stage in having an agile type for lengths that would be up to 2^125 for
/// SHA384/512.

inline_for_extraction noextract
let rest a (total_len: UInt64.t): (x:UInt32.t { U32.v x = U64.v total_len % block_length a }) =
  let open FStar.Int.Cast.Full in
  uint64_to_uint32 (total_len `U64.rem` uint32_to_uint64 (Hacl.Hash.Definitions.block_len a))

inline_for_extraction noextract
let add_len (total_len: UInt64.t) (len: UInt32.t):
  Pure UInt64.t
    (requires U64.v total_len + U32.v len < pow2 61)
    (ensures fun x -> U64.v x = U64.v total_len + U32.v len /\ U64.v x < pow2 61)
=
  assert_norm (pow2 61 < pow2 64);
  total_len `U64.add` Int.Cast.uint32_to_uint64 len

#push-options "--z3rlimit 20"

/// We split update into several versions, to all be simplified into a single
/// large one at extraction-time.

let total_len_h #a h (p: state a) =
  State?.total_len (B.deref h p)

/// Case 1: we just need to grow the buffer, no call to the hash function.

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
  (==) { S.lemma_len_append blocks rest }
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
  (==) { S.lemma_len_append b d; S.lemma_len_append blocks rest }
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
    U32.v len < block_length a - U32.v (rest a total_len) /\
    U64.v total_len + U32.v len < pow2 61)
  (ensures (rest a (add_len total_len len) = rest a total_len `U32.add` len))
=
  FStar.Math.Lemmas.small_modulo_lemma_1 (U32.v len) (block_length a);
  FStar.Math.Lemmas.modulo_distributivity (U64.v total_len) (U32.v len) (block_length a)
#pop-options

val update_small:
  a:e_alg -> (
  let a = G.reveal a in
  s:state a ->
  data: B.buffer UInt8.t ->
  len: UInt32.t ->
  Stack unit
    (requires fun h0 ->
      update_pre a s data len h0 /\
      U32.v len < block_length a - U32.v (rest a (total_len_h h0 s)))
    (ensures fun h0 s' h1 ->
      update_post a s data len h0 h1))

#push-options "--z3rlimit 50"
let update_small a p data len =
  let open LowStar.BufferOps in
  let h00 = ST.get () in
  assert (invariant #(G.reveal a) h00 p);
  let s = !*p in
  let State hash_state buf total_len seen = s in
  let a = Hash.alg_of_state a hash_state in
  [@inline_let]
  let hash_state: Hash.state a = hash_state in

  let sz = rest a total_len in
  add_len_small a total_len len;
  let h0 = ST.get () in
  let buf1 = B.sub buf 0ul sz in
  let buf2 = B.sub buf sz len in

  B.blit data 0ul buf2 0ul len;
  let h1 = ST.get () in
  split_at_last_small a (G.reveal seen) (B.as_seq h0 data);
  Hash.frame_invariant (B.loc_buffer buf) hash_state h0 h1;
  Hash.frame_invariant_implies_footprint_preservation (B.loc_buffer buf) hash_state h0 h1;
  assert (B.as_seq h1 data == B.as_seq h0 data);

  let total_len = add_len total_len len in
  p *= (State hash_state buf total_len (G.hide (G.reveal seen `S.append` (B.as_seq h0 data))));
  let h2 = ST.get () in
  assert (B.as_seq h2 data == B.as_seq h1 data);
  Hash.frame_invariant (B.loc_buffer p) hash_state h1 h2;
  Hash.frame_invariant_implies_footprint_preservation (B.loc_buffer p) hash_state h1 h2;
  assert (
    let b = S.append (G.reveal seen) (B.as_seq h0 data) in
    let blocks, rest = split_at_last a b in
    S.length blocks + S.length rest = U64.v total_len /\
    S.length b = U64.v total_len /\
    U64.v total_len < pow2 61 /\
    S.equal (Hash.repr hash_state h2) (Spec.Hash.update_multi a (Spec.Hash.init a) blocks) /\
    S.equal (S.slice (B.as_seq h2 buf) 0 (U64.v total_len % block_length a)) rest
    );
  assert (hashed #a h2 p `S.equal` (S.append (G.reveal seen) (B.as_seq h0 data)));
  assert (footprint #a h0 p == footprint #a h2 p);
  assert (preserves_freeable #a p h0 h2);
  assert (equal_domains h00 h2)

#pop-options

/// Case 2: we have no buffered data.

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

#push-options "--z3rlimit 50"
val update_empty_buf:
  a:e_alg -> (
  let a = G.reveal a in
  s:state a ->
  data: B.buffer UInt8.t ->
  len: UInt32.t ->
  Stack unit
    (requires fun h0 ->
      update_pre a s data len h0 /\
      rest a (total_len_h h0 s) = 0ul)
    (ensures fun h0 s' h1 ->
      update_post a s data len h0 h1))

let update_empty_buf a p data len =
  let open LowStar.BufferOps in
  let s = !*p in
  let State hash_state buf total_len seen = s in
  let a = Hash.alg_of_state a hash_state in
  [@inline_let]
  let hash_state: Hash.state a = hash_state in
  let sz = rest a total_len in
  let h0 = ST.get () in
  assert (
    let blocks, rest = split_at_last a (G.reveal seen) in
    S.equal blocks (G.reveal seen) /\
    S.equal rest S.empty);
  split_at_last_blocks a (G.reveal seen) (B.as_seq h0 data);
  let n_blocks = len `U32.div` Hacl.Hash.Definitions.block_len a in
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

  S.append_assoc (G.reveal seen) (B.as_seq h0 data1) (B.as_seq h0 data2);
  assert (S.equal
    (S.append (S.append (G.reveal seen) (B.as_seq h0 data1)) (B.as_seq h0 data2))
    (S.append (G.reveal seen) (S.append (B.as_seq h0 data1) (B.as_seq h0 data2))));

  p *= (State hash_state buf (add_len total_len len)
    (G.hide (G.reveal seen `S.append` B.as_seq h0 data)));
  let h3 = ST.get () in
  Hash.frame_invariant (B.loc_buffer p) hash_state h2 h3;
  Hash.frame_invariant_implies_footprint_preservation (B.loc_buffer p) hash_state h2 h3;

  // After careful diagnosis, this is the difficult proof obligation that sends
  // z3 off the rails.
  (
    let seen' = G.reveal seen `S.append` B.as_seq h0 data in
    let blocks, rest = split_at_last a seen' in
    calc (==) {
      S.length blocks + S.length rest;
    (==) { }
      S.length seen';
    (==) { S.lemma_len_append (G.reveal seen) (B.as_seq h0 data) }
      S.length (G.reveal seen) + S.length (B.as_seq h0 data);
    (==) { }
      U64.v total_len + U32.v len;
    }
  );
  ()
#pop-options


/// Case 3: we are given just enough data to end up on the boundary
#push-options "--z3rlimit 200"
val update_round:
  a:e_alg -> (
  let a = G.reveal a in
  s:state a ->
  data: B.buffer UInt8.t ->
  len: UInt32.t ->
  Stack unit
    (requires fun h0 ->
      update_pre a s data len h0 /\ (
      let r = rest a (total_len_h h0 s) in
      U32.v len + U32.v r = block_length a /\
      r <> 0ul))
    (ensures fun h0 _ h1 ->
      update_post a s data len h0 h1 /\
      U64.v (total_len_h h1 s) % block_length a = 0))

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

let update_round a p data len =
  let open LowStar.BufferOps in
  let s = !*p in
  let State hash_state buf_ total_len seen = s in
  let a = Hash.alg_of_state a hash_state in
  [@inline_let]
  let hash_state: Hash.state a = hash_state in
  let h0 = ST.get () in
  let sz = rest a total_len in
  let diff = Hacl.Hash.Definitions.block_len a `U32.sub` sz in
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
    let blocks, rest = split_at_last a (G.reveal seen) in
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
    assert (S.equal (S.append blocks rest) (G.reveal seen));
    assert (S.equal (Hash.repr hash_state h2)
      (update_multi a (Spec.Hash.init a)
        (S.append (G.reveal seen) (B.as_seq h1 data))));
    assert (S.equal (Hash.repr hash_state h2)
      (update_multi a (Spec.Hash.init a)
        (S.append (G.reveal seen) (B.as_seq h0 data))));
    split_at_last_block a (G.reveal seen) (B.as_seq h0 data);
    let blocks', rest' = split_at_last a (S.append (G.reveal seen) (B.as_seq h0 data)) in
    assert (S.equal rest' S.empty);
    assert (B.live h2 buf_ /\
      B.(loc_disjoint (loc_buffer buf_) (Hash.footprint hash_state h2)) /\
      Hash.invariant hash_state h2);
    ()
  );
  p *= (State hash_state buf_ (add_len total_len len)
    (G.hide (G.reveal seen `S.append` B.as_seq h0 data)));
  let h3 = ST.get () in
  Hash.frame_invariant (B.loc_buffer p) hash_state h2 h3;
  Hash.frame_invariant_implies_footprint_preservation (B.loc_buffer p) hash_state h2 h3;
  assert (hashed #a h3 p `S.equal` (S.append (G.reveal seen) (B.as_seq h0 data)))
#pop-options

#push-options "--z3rlimit 200"
let update a p data len =
  let open LowStar.BufferOps in
  let s = !*p in
  let State hash_state buf_ total_len seen = s in
  let a = Hash.alg_of_state a hash_state in
  [@inline_let]
  let hash_state: Hash.state a = hash_state in
  let sz = rest a total_len in
  if len `U32.lt` (Hacl.Hash.Definitions.block_len a `U32.sub` sz) then
    update_small (G.hide a) p data len
  else if sz = 0ul then
    update_empty_buf (G.hide a) p data len
  else begin
    let h0 = ST.get () in
    let diff = Hacl.Hash.Definitions.block_len a `U32.sub` sz in
    let data1 = B.sub data 0ul diff in
    let data2 = B.sub data diff (len `U32.sub` diff) in
    update_round (G.hide a) p data1 diff;
    let h1 = ST.get () in
    update_empty_buf (G.hide a) p data2 (len `U32.sub` diff);
    let h2 = ST.get () in
    (
      let seen = G.reveal seen in
      assert (hashed #a h1 p `S.equal` (S.append seen (B.as_seq h0 data1)));
      assert (hashed #a h2 p `S.equal` (S.append (S.append seen (B.as_seq h0 data1)) (B.as_seq h0 data2)));
      S.append_assoc seen (B.as_seq h0 data1) (B.as_seq h0 data2);
      assert (S.equal (S.append (B.as_seq h0 data1) (B.as_seq h0 data2)) (B.as_seq h0 data));
      assert (S.equal
        (S.append (S.append seen (B.as_seq h0 data1)) (B.as_seq h0 data2))
        (S.append seen (B.as_seq h0 data)));
      assert (hashed #a h2 p `S.equal` (S.append seen (B.as_seq h0 data)));
      ()
    )
  end
#pop-options

inline_for_extraction noextract
val mk_finish: a:Hash.alg -> finish_st a

#restart-solver
#reset-options "--z3rlimit 30 --max_fuel 0 --max_ifuel 0"
inline_for_extraction noextract
let mk_finish a p dst =
  let open LowStar.BufferOps in
  let h0 = ST.get () in
  let s = !*p in
  let State hash_state buf_ total_len seen = s in
  let a = Hash.alg_of_state (G.hide a) hash_state in
  [@inline_let]
  let hash_state: Hash.state a = hash_state in

  push_frame ();
  let h1 = ST.get () in
  Hash.frame_invariant B.loc_none hash_state h0 h1;
  Hash.frame_invariant_implies_footprint_preservation B.loc_none hash_state h0 h1;
  assert (Hash.invariant hash_state h1);

  assert_norm (pow2 61 < pow2 125);
  assert (U64.v total_len < max_input_length a);
  let buf_ = B.sub buf_ 0ul (rest a total_len) in
  assert (
    let r = rest a total_len in
    (U64.v total_len - U32.v r) % block_length a = 0);

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
    let seen = G.reveal seen in
    let n = S.length seen / block_length a in
    let blocks, rest_ = S.split seen (n * block_length a) in
    calc (S.equal) {
      B.as_seq h5 dst;
    (S.equal) { }
      finish a (Hash.repr tmp_hash_state h4);
    (S.equal) { }
      finish a (
        update_multi a (Hash.repr tmp_hash_state h3)
          (S.append
            (S.slice (B.as_seq h3 buf_) 0 (U32.v (rest a total_len)))
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
    (S.equal) { Spec.Hash.Lemmas.hash_is_hash_incremental a seen }
      Spec.Hash.hash a seen;
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
  assert (hashed h6 p `S.equal` (G.reveal seen));

  (*
   * AR: 02/14: This is hard. In emacs, the lemma calls are not needed
   *            Whereas on the command line, proof doesn't work without
   *            With log_queries, the differences between the two are:
   *            -- Comments
   *            -- More push calls in emacs
   *            -- The name of one non total arrow symbol (_288 vs _327)
   *            Can't do much about it, may be can investigate the gensym difference
   *)
  let mloc = B.loc_union (B.loc_buffer dst) (footprint h0 p) in
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

let finish a s dst =
  let open LowStar.BufferOps in
  let State hash_state _ _ _ = !*s in
  let a = Hash.alg_of_state a hash_state in
  [@inline_let]
  let hash_state: Hash.state a = hash_state in
  match a with
  | MD5 -> finish_md5 s dst
  | SHA1 -> finish_sha1 s dst
  | SHA2_224 -> finish_sha224 s dst
  | SHA2_256 -> finish_sha256 s dst
  | SHA2_384 -> finish_sha384 s dst
  | SHA2_512 -> finish_sha512 s dst

let free a s =
  let open LowStar.BufferOps in
  let State hash_state buf _ _ = !*s in
  Hash.free #a hash_state;
  B.free buf
