module Hacl.Streaming.Functor

/// Provided an instance of the type class, this creates a streaming API on top.
/// This means that every function in this module takes two extra arguments
/// compared to the previous streaming module specialized for hashes: the type
/// of the index, and a type class for that index. Then, as usual, a given value
/// for the index as a parameter.

#set-options "--max_fuel 0 --max_ifuel 0"

module ST = FStar.HyperStack.ST
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

/// State machinery
/// ===============

/// Little bit of trickery here to make sure state_s is parameterized over
/// something at Type0, not Type0 -> Type0 -- otherwise it wouldn't monomorphize
/// in KreMLin.
noeq
type state_s #index (c: block index) (i: index) (t: Type0 { t == c.state.s i }) =
| State:
    block_state: t ->
    buf: B.buffer Lib.IntTypes.uint8 { B.len buf = c.block_len i } ->
    total_len: UInt64.t ->
    seen: G.erased (S.seq uint8) ->
    // Stupid name conflict on overloaded projectors leads to inscrutable
    // interleaving errors. Need a field name that does not conflict with the
    // one in Hacl.Streaming.Interface. Sigh!!
    maybe_key: optional_key i c.km c.key ->
    state_s #index c i t

let optional_freeable #index
  (#i: index)
  (#km: key_management)
  (#key: stateful index)
  (h: HS.mem)
  (k: optional_key i km key)
=
  allow_inversion key_management;
  match km with
  | Erased -> True
  | Runtime -> key.freeable #i h k

let optional_invariant #index
  (#i: index)
  (#km: key_management)
  (#key: stateful index)
  (h: HS.mem)
  (k: optional_key i km key)
=
  allow_inversion key_management;
  match km with
  | Erased -> True
  | Runtime -> key.invariant #i h k

let optional_footprint #index
  (#i: index)
  (#km: key_management)
  (#key: stateful index)
  (h: HS.mem)
  (k: optional_key i km key)
=
  allow_inversion key_management;
  match km with
  | Erased -> B.loc_none
  | Runtime -> key.footprint #i h k

let optional_reveal #index
  (#i: index)
  (#km: key_management)
  (#key: stateful index)
  (h: HS.mem)
  (k: optional_key i km key)
=
  allow_inversion key_management;
  match km with
  | Erased -> G.reveal k
  | Runtime -> key.v i h k

let freeable #index (c: block index) (i: index) (h: HS.mem) (p: state c i (c.state.s i)) =
  B.freeable p /\ (
  let s = B.deref h p in
  let State block_state buf _ _ maybe_key = s in
  B.freeable buf /\ c.state.freeable h block_state /\ optional_freeable h maybe_key)

let footprint_s #index (c: block index) (i: index) (h: HS.mem) (s: state_s c i (c.state.s i)) =
  let State block_state buf_ _ _ maybe_key = s in
  B.(loc_addr_of_buffer buf_ `loc_union` c.state.footprint h block_state `loc_union` optional_footprint h maybe_key)

/// Invariants
/// ==========

noextract
let split_at_last #index (c: block index) (i: index) (b: bytes):
  Pure (bytes & bytes)
    (requires True)
    (ensures (fun (blocks, rest) ->
      S.length rest < U32.v (c.block_len i) /\
      S.length rest = S.length b % U32.v (c.block_len i) /\
      S.equal (S.append blocks rest) b /\
      S.length blocks % U32.v (c.block_len i) = 0))
=
  let n = S.length b / U32.v (c.block_len i) in
  let blocks, rest = S.split b (n * U32.v (c.block_len i)) in
  assert (S.length blocks = n * U32.v (c.block_len i));
  FStar.Math.Lemmas.multiple_modulo_lemma n (U32.v (c.block_len i));
  assert ((n * U32.v (c.block_len i)) % U32.v (c.block_len i) = 0);
  assert (S.length rest = S.length b - n * U32.v (c.block_len i));
  assert (S.length b - n * U32.v (c.block_len i) < U32.v (c.block_len i));
  blocks, rest

let invariant_s #index (c: block index) (i: index) h (s: state_s c i (c.state.s i)) =
  let State block_state buf_ total_len seen key = s in
  let seen = G.reveal seen in
  let blocks, rest = split_at_last c i seen in

  // Liveness and disjointness (administrative)
  B.live h buf_ /\ c.state.invariant #i h block_state /\ optional_invariant h key /\
  B.(loc_disjoint (loc_buffer buf_) (c.state.footprint h block_state)) /\
  B.(loc_disjoint (loc_buffer buf_) (optional_footprint h key)) /\
  B.(loc_disjoint (optional_footprint h key) (c.state.footprint h block_state)) /\

  // Formerly, the "hashes" predicate
  S.length blocks + S.length rest = U64.v total_len /\
  S.length seen = U64.v total_len /\
  U64.v total_len <= c.max_input_length i /\
  // Note the double equals here, we now no longer know that this is a sequence.
  c.state.v i h block_state == c.update_multi_s i (c.init_s i (optional_reveal h key)) blocks /\
  S.equal (S.slice (B.as_seq h buf_) 0 (U64.v total_len % U32.v (c.block_len i))) rest

#push-options "--max_ifuel 1"
let invariant_loc_in_footprint #index c i s m =
  [@inline_let]
  let _ = c.state.invariant_loc_in_footprint #i in
  [@inline_let]
  let _ = c.key.invariant_loc_in_footprint #i in
  ()
#pop-options

let seen #index c i h s =
  G.reveal (State?.seen (B.deref h s))

let seen_bounded #index c i h s =
  ()

let key #index c i h s =
  optional_reveal h (State?.maybe_key (B.deref h s))

let frame_invariant #index c i l s h0 h1 =
  let state_t = B.deref h0 s in
  let State block_state _ _ _ _ = state_t in
  c.frame_invariant #i l block_state h0 h1

let frame_seen #_ _ _ _ _ _ _ =
  ()

let frame_freeable #index c i l s h0 h1 =
  let State block_state _ _ _ _ = B.deref h0 s in
  c.frame_freeable #i l block_state h0 h1

/// Stateful API
/// ============

let index_of_state #index c i t s =
  let open LowStar.BufferOps in
  let State block_state _ _ _ _ = !*s in
  c.index_of_state i block_state

let split_at_last_empty #index (c: block index) (i: index): Lemma
  (ensures (
    let blocks, rest = split_at_last c i S.empty in
    S.equal blocks S.empty /\ S.equal rest S.empty))
=
  ()

#push-options "--using_facts_from '*,-LowStar.Monotonic.Buffer.unused_in_not_unused_in_disjoint_2'"
let create_in #index c i t k r =
  [@inline_let]
  let _ = c.invariant_loc_in_footprint #i in

  (**) let h0 = ST.get () in

  (**) B.loc_unused_in_not_unused_in_disjoint h0;
  let buf = B.malloc r (Lib.IntTypes.u8 0) (c.block_len i) in
  (**) let h1 = ST.get () in
  (**) assert (B.fresh_loc (B.loc_buffer buf) h0 h1);
  (**) B.loc_unused_in_not_unused_in_disjoint h1;
  (**) B.(modifies_only_not_unused_in loc_none h0 h1);

  let block_state = c.create_in i r in
  (**) let h2 = ST.get () in
  (**) assert (B.fresh_loc (c.footprint #i h2 block_state) h0 h2);
  (**) B.(modifies_only_not_unused_in loc_none h1 h2);

  let s = State block_state buf 0UL (G.hide S.empty) (G.hide (c.v_key h0 k)) in
  (**) assert (B.fresh_loc (footprint_s c i h2 s) h0 h2);

  (**) B.loc_unused_in_not_unused_in_disjoint h2;
  let p = B.malloc r s 1ul in
  (**) let h3 = ST.get () in
  (**) c.frame_invariant B.loc_none block_state h2 h3;
  (**) B.(modifies_only_not_unused_in loc_none h2 h3);
  (**) assert (B.fresh_loc (B.loc_addr_of_buffer p) h0 h3);
  (**) assert (B.fresh_loc (footprint_s c i h3 s) h0 h3);
  (**) c.frame_freeable B.loc_none block_state h2 h3;
  (**) assert (freeable c i h3 p);
  (**) assert (c.v_key h2 k == c.v_key h3 k);
  admit ()

  c.init (G.hide i) k block_state;
  (**) let h4 = ST.get () in
  (**) assert (B.fresh_loc (c.footprint #i h4 block_state) h0 h4);
  (**) assert (B.fresh_loc (B.loc_buffer buf) h0 h4);
  (**) c.update_multi_zero i (c.v h4 block_state);
  (**) split_at_last_empty c i;
  (**) B.modifies_only_not_unused_in B.loc_none h0 h4;
  (**) assert (c.v h4 block_state == c.init_s i (c.v_key h3 k));

  (**) let h5 = ST.get () in
  (**) assert (
    let h = h5 in
    let s = (B.get h5 p 0) in
    let State block_state buf_ total_len seen _ = s in
    let seen = G.reveal seen in
    let blocks, rest = split_at_last c i seen in
    // JP: unclear why I need to assert this... but without it the proof doesn't
    // go through.
    U64.v total_len < c.max_input_length i /\
    True
  );
  (**) assert (invariant c i h5 p);
  (**) assert (seen c i h5 p == S.empty);
  (**) assert B.(modifies loc_none h0 h5);
  (**) assert (B.fresh_loc (footprint c i h5 p) h0 h5);
  (**) assert B.(loc_includes (loc_region_only true r) (footprint c i h5 p));
  (**) assert (freeable c i h5 p);

  (**) assert (ST.equal_stack_domains h1 h5);
  (**) assert (ST.equal_stack_domains h0 h1);

  p
#pop-options

let init #index c i t s =
  [@inline_let]
  let _ = c.invariant_loc_in_footprint #i in
  [@inline_let]
  let _ = c.frame_freeable #i in

  let open LowStar.BufferOps in
  let h1 = ST.get () in
  let State block_state buf _ _ = !*s in
  // JP: figuring out the alg at run-time is useful, but entails a lot more
  // proof difficulty; note the let-binding below, as well as the fact that
  // implicit argument resolution basically no longer works after this...
  let i = c.index_of_state i block_state in
  [@inline_let]
  let block_state: c.state i = block_state in

  c.init (G.hide i) block_state;
  let h2 = ST.get () in
  c.update_multi_zero i (c.v h2 block_state);
  split_at_last_empty c i;

  [@ inline_let ]
  let tmp: state_s c i t = State block_state buf 0UL (G.hide S.empty) in
  B.upd s 0ul tmp;
  let h3 = ST.get () in
  c.frame_invariant B.(loc_buffer s) block_state h2 h3;

  // This seems to cause insurmountable difficulties. Puzzled.
  ST.lemma_equal_domains_trans h1 h2 h3;

  // AR: 07/22: same old `Seq.equal` and `==` story
  assert (Seq.equal (seen c i h3 s) Seq.empty);

  assert (preserves_freeable c i s h1 h3);
  //assert (hashed h3 s == S.empty);
  assert (footprint c i h1 s == footprint c i h3 s);
  assert (B.(modifies (footprint c i h1 s) h1 h3));
  //assert (B.live h3 s);
  //assert (B.(loc_disjoint (loc_addr_of_buffer s) (footprint_s h3 (B.deref h3 s))));
  assert (
    let h = h3 in
    let s = B.get h3 s 0 in
    let State block_state buf_ total_len seen = s in
    let seen = G.reveal seen in
    let blocks, rest = split_at_last c i seen in

    // Liveness and disjointness (administrative)
    B.live h buf_ /\ c.invariant #i h block_state /\
    B.(loc_disjoint (loc_buffer buf_) (c.footprint #i h block_state)) /\

    // Formerly, the "hashes" predicate
    S.length blocks + S.length rest = U64.v total_len /\
    S.length seen = U64.v total_len /\
    U64.v total_len < c.max_input_length i /\
    // Note the double equals here, we now no longer know that this is a sequence.
    c.v h block_state == c.update_multi_s i (c.init_s i) blocks /\
    S.equal (S.slice (B.as_seq h buf_) 0 (U64.v total_len % U32.v (c.block_len i))) rest
  );
  assert (invariant_s c i h3 (B.get h3 s 0))

/// We keep the total length at run-time, on 64 bits, but require that it abides
/// by the size requirements for the smaller hashes -- we're not interested at
/// this stage in having an agile type for lengths that would be up to 2^125 for
/// SHA384/512.

#push-options "--z3cliopt smt.arith.nl=false"
let mod_block_len_bound #index (c: block index) (i: index)
  (total_len: U64.t): Lemma
  (requires True)
  (ensures U64.v (total_len `U64.rem` FStar.Int.Cast.uint32_to_uint64 (c.block_len i)) <= pow2 32 - 1)
=
  let open FStar.Int.Cast in
  let x = total_len `U64.rem` uint32_to_uint64 (c.block_len i) in
  calc (<=) {
    U64.v x;
  (<=) { FStar.Math.Lemmas.euclidean_division_definition (U64.v total_len) (U64.v (uint32_to_uint64 (c.block_len i))) }
    U64.v total_len % U64.v (uint32_to_uint64 (c.block_len i) );
  (<=) { FStar.Math.Lemmas.modulo_range_lemma (U64.v total_len) (U64.v (uint32_to_uint64 (c.block_len i))) }
    U64.v (uint32_to_uint64 (c.block_len i));
  (<=) { }
    pow2 32 - 1;
  }

inline_for_extraction noextract
let rest #index (c: block index) (i: index)
  (total_len: UInt64.t): (x:UInt32.t { U32.v x = U64.v total_len % U32.v (c.block_len i) })
=
  let open FStar.Int.Cast in
  let x = total_len `U64.rem` uint32_to_uint64 (c.block_len i) in
  let r = FStar.Int.Cast.uint64_to_uint32 x in
  mod_block_len_bound c i total_len;
  calc (==) {
    U32.v r;
  (==) { }
    U64.v x % pow2 32;
  (==) { FStar.Math.Lemmas.small_modulo_lemma_1 (U64.v x) (pow2 32) }
    U64.v x;
  (==) { FStar.Math.Lemmas.euclidean_division_definition (U64.v total_len) (U64.v (uint32_to_uint64 (c.block_len i))) }
    U64.v total_len % U64.v (uint32_to_uint64 (c.block_len i) );
  (==) { }
    U64.v total_len % U32.v (c.block_len i);
  };
  r
#pop-options

inline_for_extraction noextract
let add_len #index (c: block index) (i: index) (total_len: UInt64.t) (len: UInt32.t):
  Pure UInt64.t
    (requires U64.v total_len + U32.v len <= c.max_input_length i)
    (ensures fun x -> U64.v x = U64.v total_len + U32.v len /\ U64.v x <= c.max_input_length i)
=
  total_len `U64.add` Int.Cast.uint32_to_uint64 len

/// We split update into several versions, to all be simplified into a single
/// large one at extraction-time.

let total_len_h #index (c: block index) (i: index) h (p: state c i (c.state i)) =
  State?.total_len (B.deref h p)

/// Case 1: we just need to grow the buffer, no call to the hash function.

#push-options "--z3rlimit 50"
let split_at_last_small #index (c: block index) (i: index) (b: bytes) (d: bytes): Lemma
  (requires (
    let _, rest = split_at_last c i b in
    S.length rest + S.length d < U32.v (c.block_len i)))
  (ensures (
    let blocks, rest = split_at_last c i b in
    let blocks', rest' = split_at_last c i (S.append b d) in
    S.equal blocks blocks' /\ S.equal (S.append rest d) rest'))
=
  let blocks, rest = split_at_last c i b in
  let blocks', rest' = split_at_last c i (S.append b d) in
  let l = U32.v (c.block_len i) in

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

#push-options "--z3cliopt smt.arith.nl=false"
let add_len_small #index (c: block index) (i: index) (total_len: UInt64.t) (len: UInt32.t): Lemma
  (requires
    U32.v len < U32.v (c.block_len i) - U32.v (rest c i total_len) /\
    U64.v total_len + U32.v len <= c.max_input_length i)
  (ensures (rest c i (add_len c i total_len len) = rest c i total_len `U32.add` len))
=
  calc (==) {
    U32.v (rest c i (add_len c i total_len len));
  (==) { }
    U64.v (add_len c i total_len len) % U32.v (c.block_len i);
  (==) { }
    (U64.v total_len + U32.v len) % U32.v (c.block_len i);
  (==) { Math.Lemmas.modulo_distributivity (U64.v total_len) (U32.v len) (U32.v (c.block_len i)) }
    (U64.v total_len % U32.v (c.block_len i) + U32.v len % U32.v (c.block_len i)) % U32.v (c.block_len i);
  (==) { Math.Lemmas.lemma_mod_add_distr (U64.v total_len % U32.v (c.block_len i)) (U32.v len) (U32.v (c.block_len i)) }
    (U64.v total_len % U32.v (c.block_len i) + U32.v len) % U32.v (c.block_len i);
  (==) { }
    (U32.v (rest c i total_len) + U32.v len) % U32.v (c.block_len i);
  (==) { Math.Lemmas.modulo_lemma (U32.v (rest c i total_len) + U32.v len) (U32.v (c.block_len i)) }
    U32.v (rest c i total_len) + U32.v len;
  }
#pop-options

inline_for_extraction noextract
val update_small:
  #index:Type0 ->
  (c: block index) ->
  i:G.erased index -> (
  let i = G.reveal i in
  t:Type0 { t == c.state i } ->
  s:state c i t ->
  data: B.buffer uint8 ->
  len: UInt32.t ->
  Stack unit
    (requires fun h0 ->
      update_pre c i s data len h0 /\
      U32.v len < U32.v (c.block_len i) - U32.v (rest c i (total_len_h c i h0 s)))
    (ensures fun h0 s' h1 ->
      update_post c i s data len h0 h1))

#push-options "--z3rlimit 60"
let update_small #index c i t p data len =
  [@inline_let]
  let _ = c.invariant_loc_in_footprint #i in
  [@inline_let]
  let _ = c.frame_freeable #i in

  let open LowStar.BufferOps in
  let h00 = ST.get () in
  assert (invariant c i h00 p);
  let s = !*p in
  let State block_state buf total_len seen_ = s in
  let i = c.index_of_state i block_state in
  [@inline_let]
  let block_state: c.state i = block_state in

  let sz = rest c i total_len in
  add_len_small c i total_len len;
  let h0 = ST.get () in
  let buf1 = B.sub buf 0ul sz in
  let buf2 = B.sub buf sz len in

  B.blit data 0ul buf2 0ul len;
  let h1 = ST.get () in
  split_at_last_small c i (G.reveal seen_) (B.as_seq h0 data);
  c.frame_invariant (B.loc_buffer buf) block_state h0 h1;
  assert (B.as_seq h1 data == B.as_seq h0 data);

  let total_len = add_len c i total_len len in
  [@inline_let]
  let tmp: state_s c i t =
    State block_state buf total_len (G.hide (G.reveal seen_ `S.append` (B.as_seq h0 data)))
  in
  p *= tmp;
  let h2 = ST.get () in
  assert (B.as_seq h2 data == B.as_seq h1 data);
  c.frame_invariant (B.loc_buffer p) block_state h1 h2;
  assert (
    let b = S.append (G.reveal seen_) (B.as_seq h0 data) in
    let blocks, rest = split_at_last c i b in
    S.length blocks + S.length rest = U64.v total_len /\
    S.length b = U64.v total_len /\
    U64.v total_len <= c.max_input_length i /\
    (==) (c.v h2 block_state) (c.update_multi_s i (c.init_s i) blocks) /\
    S.equal (S.slice (B.as_seq h2 buf) 0 (U64.v total_len % U32.v (c.block_len i))) rest
    );
  assert (seen c i h2 p `S.equal` (S.append (G.reveal seen_) (B.as_seq h0 data)));
  assert (footprint c i h0 p == footprint c i h2 p);
  assert (preserves_freeable c i p h0 h2);
  assert (equal_domains h00 h2)

#pop-options

/// Case 2: we have no buffered data.

#push-options "--z3rlimit 60"
let split_at_last_blocks #index (c: block index) (i: index) (b: bytes) (d: bytes): Lemma
  (requires (
    let blocks, rest = split_at_last c i b in
    S.equal rest S.empty))
  (ensures (
    let blocks, rest = split_at_last c i b in
    let blocks', rest' = split_at_last c i d in
    let blocks'', rest'' = split_at_last c i (S.append b d) in
    S.equal blocks'' (S.append blocks blocks') /\
    S.equal rest' rest''))
=
  let blocks, rest = split_at_last c i b in
  let blocks', rest' = split_at_last c i d in
  let blocks'', rest'' = split_at_last c i (S.append b d) in
  let b' = S.append blocks rest in
  let d' = S.append blocks' rest' in
  let l = U32.v (c.block_len i) in
  calc (S.equal) {
    rest';
  (S.equal) { }
    snd (split_at_last c i d);
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
    S.append b (fst (split_at_last c i d));
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
#pop-options

#push-options "--z3rlimit 50"
inline_for_extraction noextract
val update_empty_buf:
  #index:Type0 ->
  c:block index ->
  i:G.erased index -> (
  let i = G.reveal i in
  t:Type0 { t == c.state i } ->
  s:state c i t ->
  data: B.buffer Lib.IntTypes.uint8 ->
  len: UInt32.t ->
  Stack unit
    (requires fun h0 ->
      update_pre c i s data len h0 /\
      rest c i (total_len_h c i h0 s) = 0ul)
    (ensures fun h0 s' h1 ->
      update_post c i s data len h0 h1))

inline_for_extraction noextract
let seen_pred = seen

let update_empty_buf #index c i t p data len =
  [@inline_let]
  let _ = c.invariant_loc_in_footprint #i in
  [@inline_let]
  let _ = c.frame_freeable #i in
  [@inline_let]
  let _ = c.update_multi_associative i in

  let open LowStar.BufferOps in
  let s = !*p in
  let State block_state buf total_len seen = s in
  let i = c.index_of_state i block_state in
  [@inline_let]
  let block_state: c.state i = block_state in
  let sz = rest c i total_len in
  let h0 = ST.get () in
  assert (
    let blocks, rest = split_at_last c i (G.reveal seen) in
    S.equal blocks (G.reveal seen) /\
    S.equal rest S.empty);
  split_at_last_blocks c i (G.reveal seen) (B.as_seq h0 data);
  let n_blocks = len `U32.div` c.block_len i in
  let data1_len = n_blocks `U32.mul` c.block_len i in
  let data2_len = len `U32.sub` data1_len in
  let data1 = B.sub data 0ul data1_len in
  let data2 = B.sub data data1_len data2_len in
  c.update_multi (G.hide i) block_state data1 data1_len;

  let dst = B.sub buf 0ul data2_len in
  let h1 = ST.get () in
  B.blit data2 0ul dst 0ul data2_len;
  let h2 = ST.get () in
  c.frame_invariant (B.loc_buffer buf) block_state h1 h2;

  S.append_assoc (G.reveal seen) (B.as_seq h0 data1) (B.as_seq h0 data2);
  assert (S.equal
    (S.append (S.append (G.reveal seen) (B.as_seq h0 data1)) (B.as_seq h0 data2))
    (S.append (G.reveal seen) (S.append (B.as_seq h0 data1) (B.as_seq h0 data2))));

  [@inline_let]
  let tmp: state_s c i t = State block_state buf (add_len c i total_len len)
    (G.hide (G.reveal seen `S.append` B.as_seq h0 data))
  in
  p *= tmp;
  let h3 = ST.get () in
  c.frame_invariant (B.loc_buffer p) block_state h2 h3;

  // After careful diagnosis, this is the difficult proof obligation that sends
  // z3 off the rails.
  (
    let seen' = G.reveal seen `S.append` B.as_seq h0 data in
    let blocks, rest = split_at_last c i seen' in
    calc (==) {
      S.length blocks + S.length rest;
    (==) { }
      S.length seen';
    (==) { S.lemma_len_append (G.reveal seen) (B.as_seq h0 data) }
      S.length (G.reveal seen) + S.length (B.as_seq h0 data);
    (==) { }
      U64.v total_len + U32.v len;
    }
  )
#pop-options


/// Case 3: we are given just enough data to end up on the boundary
#push-options "--z3rlimit 200"
inline_for_extraction noextract
val update_round:
  #index:Type0 ->
  c:block index ->
  i:G.erased index -> (
  let i = G.reveal i in
  t:Type0 { t == c.state i } ->
  s:state c i (c.state i) ->
  data: B.buffer uint8 ->
  len: UInt32.t ->
  Stack unit
    (requires fun h0 ->
      update_pre c i s data len h0 /\ (
      let r = rest c i (total_len_h c i h0 s) in
      U32.v len + U32.v r = U32.v (c.block_len i) /\
      r <> 0ul))
    (ensures fun h0 _ h1 ->
      update_post c i s data len h0 h1 /\
      U64.v (total_len_h c i h1 s) % U32.v (c.block_len i) = 0))

#push-options "--retry 3"
let split_at_last_block #index (c: block index) (i: index) (b: bytes) (d: bytes): Lemma
  (requires (
    let _, rest = split_at_last c i b in
    S.length rest + S.length d = U32.v (c.block_len i)))
  (ensures (
    let blocks, rest = split_at_last c i b in
    let blocks', rest' = split_at_last c i (S.append b d) in
    S.equal (S.append b d) blocks' /\ S.equal S.empty rest'))
=
  let blocks, rest = split_at_last c i b in

  calc (==) {
    (S.length b + S.length d) % U32.v (c.block_len i);
  (==) { S.lemma_len_append blocks rest }
    (S.length blocks + S.length rest + S.length d) % U32.v (c.block_len i);
  (==) { Math.Lemmas.modulo_distributivity (S.length blocks) (S.length rest + S.length d) (U32.v (c.block_len i)) }
    (U32.v (c.block_len i)) % (U32.v (c.block_len i));
  (==) { Math.Lemmas.multiple_modulo_lemma (U32.v (c.block_len i)) 1 }
    0;
  }
#pop-options

#push-options "--z3rlimit 100"
let update_round #index c i t p data len =
  [@inline_let]
  let _ = c.invariant_loc_in_footprint #i in
  [@inline_let]
  let _ = c.frame_freeable #i in
  [@inline_let]
  let _ = c.update_multi_associative i in

  let open LowStar.BufferOps in
  let s = !*p in
  let State block_state buf_ total_len seen = s in
  let i = c.index_of_state i block_state in
  [@inline_let]
  let block_state: c.state i = block_state in
  let h0 = ST.get () in
  let sz = rest c i total_len in
  let diff = c.block_len i `U32.sub` sz in
  let buf0 = B.sub buf_ 0ul (c.block_len i) in
  let buf1 = B.sub buf0 0ul sz in
  let buf2 = B.sub buf0 sz diff in
  assert (B.(loc_pairwise_disjoint
    [ loc_buffer buf1; loc_buffer buf2; loc_buffer data; ]));
  B.blit data 0ul buf2 0ul diff;
  let h1 = ST.get () in
  assert (S.equal (B.as_seq h1 buf0) (S.append (B.as_seq h1 buf1) (B.as_seq h1 data)));
  c.frame_invariant (B.loc_buffer buf_) block_state h0 h1;
  c.update_multi (G.hide i) block_state buf0 (c.block_len i);
  let h2 = ST.get () in
  (* Proof interlude *)
  begin
    let seen' = G.reveal seen `S.append` B.as_seq h0 data in
    let blocks', rest' = split_at_last c i seen' in
    let seen = G.reveal seen in
    let blocks, rest = split_at_last c i seen in
    assert (S.length blocks % U32.v (c.block_len i) = 0);
    assert (S.length (rest `S.append` B.as_seq h0 data) % U32.v (c.block_len i) = 0);
    calc (==) {
      c.v h2 block_state;
    (==) { }
      c.update_multi_s i (c.v h1 block_state) (B.as_seq h1 buf0);
    (==) { }
      c.update_multi_s i (c.v h1 block_state) (B.as_seq h0 buf1 `S.append` B.as_seq h0 data);
    (==) { }
      c.update_multi_s i (c.update_multi_s i (c.init_s i) blocks) (B.as_seq h0 buf1 `S.append` B.as_seq h0 data);
    (==) { }
      c.update_multi_s i (c.update_multi_s i (c.init_s i) blocks) (rest `S.append` B.as_seq h0 data);
    (==) { }
      c.update_multi_s i (c.init_s i) (blocks `S.append` (rest `S.append` B.as_seq h0 data));
    (==) { S.append_assoc blocks rest (B.as_seq h0 data) }
      c.update_multi_s i (c.init_s i) (blocks `S.append` rest `S.append` B.as_seq h0 data);
    (==) { }
      c.update_multi_s i (c.init_s i) (seen `S.append` B.as_seq h0 data);
    }
  end;
  [@inline_let]
  let tmp: state_s c i t = State block_state buf_ (add_len c i total_len len)
    (G.hide (G.reveal seen `S.append` B.as_seq h0 data))
  in
  p *= tmp;
  let h3 = ST.get () in
  c.frame_invariant (B.loc_buffer p) block_state h2 h3;
  assert (seen_pred c i h3 p `S.equal` (S.append (G.reveal seen) (B.as_seq h0 data)))
#pop-options

let update #index c i t p data len =
  let open LowStar.BufferOps in
  let s = !*p in
  let State block_state buf_ total_len seen = s in
  let i = c.index_of_state i block_state in
  let sz = rest c i total_len in
  if len `U32.lt` (c.block_len i `U32.sub` sz) then
    update_small c (G.hide i) t p data len
  else if sz = 0ul then
    update_empty_buf c (G.hide i) t p data len
  else begin
    let h0 = ST.get () in
    let diff = c.block_len i `U32.sub` sz in
    let data1 = B.sub data 0ul diff in
    let data2 = B.sub data diff (len `U32.sub` diff) in
    update_round c (G.hide i) t p data1 diff;
    let h1 = ST.get () in
    update_empty_buf c (G.hide i) t p data2 (len `U32.sub` diff);
    let h2 = ST.get () in
    (
      let seen = G.reveal seen in
      assert (seen_pred c i h1 p `S.equal` (S.append seen (B.as_seq h0 data1)));
      assert (seen_pred c i h2 p `S.equal` (S.append (S.append seen (B.as_seq h0 data1)) (B.as_seq h0 data2)));
      S.append_assoc seen (B.as_seq h0 data1) (B.as_seq h0 data2);
      assert (S.equal (S.append (B.as_seq h0 data1) (B.as_seq h0 data2)) (B.as_seq h0 data));
      assert (S.equal
        (S.append (S.append seen (B.as_seq h0 data1)) (B.as_seq h0 data2))
        (S.append seen (B.as_seq h0 data)));
      assert (seen_pred c i h2 p `S.equal` (S.append seen (B.as_seq h0 data)));
      ()
    )
  end

let mk_finish #index c i t p dst =
  [@inline_let]
  let _ = c.invariant_loc_in_footprint #i in
  [@inline_let]
  let _ = c.frame_freeable #i in
  [@inline_let]
  let _ = c.update_multi_associative i in

  let open LowStar.BufferOps in
  let h0 = ST.get () in
  let State block_state buf_ total_len seen = !*p in

  push_frame ();
  let h1 = ST.get () in
  c.frame_invariant #i B.loc_none block_state h0 h1;
  assert (c.invariant #i h1 block_state);

  let buf_ = B.sub buf_ 0ul (rest c i total_len) in
  assert (
    let r = rest c i total_len in
    (U64.v total_len - U32.v r) % U32.v (c.block_len i) = 0);

  let tmp_block_state = c.alloca i in

  let h2 = ST.get () in
  assert (B.(loc_disjoint (c.footprint #i h2 tmp_block_state) (c.footprint #i h1 block_state)));
  c.frame_invariant #i B.(loc_region_only false (HS.get_tip h2)) block_state h1 h2;
  assert (c.invariant #i h2 block_state);
  assert (c.invariant #i h2 tmp_block_state);
  assert (c.footprint #i h2 block_state == c.footprint #i h1 block_state);

  c.copy (G.hide i) block_state tmp_block_state;

  let h3 = ST.get () in
  assert (c.footprint h2 tmp_block_state == c.footprint h3 tmp_block_state);
  c.frame_invariant #i (c.footprint h2 tmp_block_state) block_state h2 h3;
  assert (c.invariant #i h3 block_state);
  c.update_last (G.hide i) tmp_block_state buf_ total_len;

  let h4 = ST.get () in
  c.frame_invariant #i (c.footprint h3 tmp_block_state) block_state h3 h4;
  assert (c.invariant #i h4 block_state);

  c.finish (G.hide i) tmp_block_state dst;

  let h5 = ST.get () in
  begin
    let seen = G.reveal seen in
    let block_length = U32.v (c.block_len i) in
    let n = S.length seen / block_length in
    let blocks, rest_ = S.split seen (n * block_length)  in
    calc (S.equal) {
      B.as_seq h5 dst;
    (S.equal) { }
      c.finish_s i (c.v h4 tmp_block_state);
    (S.equal) { }
      c.finish_s i (
        c.update_last_s i (c.v h3 tmp_block_state) (n * block_length)
          (S.slice (B.as_seq h3 buf_) 0 (U32.v (rest c i total_len))));
    (S.equal) { }
      c.finish_s i (
        c.update_last_s i (c.v h3 tmp_block_state) (n * block_length)
          (S.slice (B.as_seq h0 buf_) 0 (U32.v (rest c i total_len))));
    (S.equal) { }
      c.finish_s i (
        c.update_last_s i
          (c.update_multi_s i (c.init_s i) (S.slice seen 0 (n * block_length)))
          (n * block_length)
          (S.slice (B.as_seq h0 buf_) 0 (U32.v (rest c i total_len))));
    (S.equal) { c.spec_is_incremental i seen }
      c.spec_s i seen;
    }
  end;

  c.frame_invariant #i (B.loc_buffer dst) block_state h4 h5;
  assert (c.invariant #i h5 block_state);

  pop_frame ();
  let h6 = ST.get () in
  c.frame_invariant #i B.(loc_region_only false (HS.get_tip h5)) block_state h5 h6;
  assert (seen_pred c i h6 p `S.equal` (G.reveal seen));

  // JP: this is not the right way to prove do this proof. Need to use
  // modifies_fresh_frame_popped instead, see e.g.
  // https://github.com/project-everest/everquic-crypto/blob/d812be94e9b1a77261f001c9accb2040b80b7c39/src/QUIC.Impl.fst#L1111
  // for an example
  let mloc = B.loc_union (B.loc_buffer dst) (footprint c i h0 p) in
  B.modifies_remove_fresh_frame h0 h1 h6 mloc;
  B.popped_modifies h5 h6;
  assert (B.(modifies mloc h0 h6))

let free #index c i t s =
  let open LowStar.BufferOps in
  let State block_state buf _ _ = !*s in
  c.free i block_state;
  B.free buf;
  B.free s
