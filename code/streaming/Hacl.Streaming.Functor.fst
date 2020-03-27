module Hacl.Streaming.Functor

/// Provided an instance of the type class, this creates a streaming API on top.
/// This means that every function in this module takes two extra arguments
/// compared to the previous streaming module specialized for hashes: the type
/// of the index, and a type class for that index. Then, as usual, a given value
/// for the index as a parameter.

#set-options "--max_fuel 0 --max_ifuel 0 --z3rlimit 100"

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

noextract
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

// TODO: move to fsti
val seen: #index:Type0 -> c:block index -> i:index -> h:HS.mem -> s:state c i -> GTot bytes
let seen #index c i h s =
  G.reveal (State?.seen (B.deref h s))

val frame_invariant: #index:Type0 -> c:block index -> i:index -> l:B.loc -> s:state c i -> h0:HS.mem -> h1:HS.mem -> Lemma
  (requires (
    invariant c i h0 s /\
    B.loc_disjoint l (footprint c i h0 s) /\
    B.modifies l h0 h1))
  (ensures (
    invariant c i h1 s /\
    footprint c i h0 s == footprint c i h1 s))
  [ SMTPat (invariant c i h1 s); SMTPat (B.modifies l h0 h1) ]

let frame_invariant #index c i l s h0 h1 =
  let state_s = B.deref h0 s in
  let State block_state _ _ _ = state_s in
  c.frame_invariant #i l block_state h0 h1

val frame_seen: #index:Type0 -> c:block index -> i:index -> l:B.loc -> s:state c i -> h0:HS.mem -> h1:HS.mem -> Lemma
  (requires (
    invariant c i h0 s /\
    B.loc_disjoint l (footprint c i h0 s) /\
    B.modifies l h0 h1))
  (ensures (seen c i h0 s == seen c i h1 s))
  [ SMTPat (seen c i h1 s); SMTPat (B.modifies l h0 h1) ]

let frame_seen #_ _ _ _ _ _ _ =
  ()

val frame_freeable: #index:Type0 -> c:block index -> i:index -> l:B.loc -> s:state c i -> h0:HS.mem -> h1:HS.mem -> Lemma
  (requires (
    invariant c i h0 s /\
    freeable c i h0 s /\
    B.loc_disjoint l (footprint c i h0 s) /\
    B.modifies l h0 h1))
  (ensures (freeable c i h1 s))
  [ SMTPat (freeable c i h1 s); SMTPat (B.modifies l h0 h1) ]

let frame_freeable #index c i l s h0 h1 =
  let State block_state _ _ _ = B.deref h0 s in
  c.frame_freeable #i l block_state h0 h1

val create_in (#index: Type0) (c: block index) (i: index) (r: HS.rid): ST (state c i)
  (requires (fun _ ->
    HyperStack.ST.is_eternal_region r))
  (ensures (fun h0 s h1 ->
    invariant c i h1 s /\
    seen c i h1 s == S.empty /\
    B.(modifies loc_none h0 h1) /\
    B.fresh_loc (footprint c i h1 s) h0 h1 /\
    B.(loc_includes (loc_region_only true r) (footprint c i h1 s)) /\
    freeable c i h1 s))

let split_at_last_empty (block_length: pos): Lemma
  (ensures (
    let blocks, rest = split_at_last block_length S.empty in
    S.equal blocks S.empty /\ S.equal rest S.empty))
=
  ()

#push-options "--using_facts_from '*,-LowStar.Monotonic.Buffer.unused_in_not_unused_in_disjoint_2'"
let create_in #index c i r =
  let aux (h:HS.mem) (s:c.state i): Lemma
    (requires (c.invariant h s))
    (ensures (B.loc_in (c.footprint #i h s) h))
    [SMTPat (c.invariant h s)]
  =
    c.invariant_loc_in_footprint #i h s
  in

  (**) let h0 = ST.get () in

  (**) B.loc_unused_in_not_unused_in_disjoint h0;
  let buf = B.malloc r (Lib.IntTypes.u8 0) (c.block_len i) in
  (**) let h1 = ST.get () in
  (**) assert (B.fresh_loc (B.loc_buffer buf) h0 h1);
  (**) B.loc_unused_in_not_unused_in_disjoint h1;

  let hash_state = c.create_in i r in
  (**) let h2 = ST.get () in
  (**) assert (B.fresh_loc (c.footprint #i h2 hash_state) h0 h2);

  let s = State hash_state buf 0UL (G.hide S.empty) in
  (**) assert (B.fresh_loc (footprint_s c i h2 s) h0 h2);

  (**) B.loc_unused_in_not_unused_in_disjoint h2;
  let p = B.malloc r s 1ul in
  (**) let h3 = ST.get () in
  (**) c.frame_invariant B.loc_none hash_state h2 h3;
  (**) B.(modifies_only_not_unused_in loc_none h2 h3);
  (**) assert (B.fresh_loc (B.loc_addr_of_buffer p) h0 h3);
  (**) assert (B.fresh_loc (footprint_s c i h3 s) h0 h3);
  (**) c.frame_freeable B.loc_none hash_state h2 h3;
  (**) assert (freeable c i h3 p);

  c.init (G.hide i) hash_state;
  (**) let h4 = ST.get () in
  (**) assert (B.fresh_loc (c.footprint #i h4 hash_state) h0 h4);
  (**) assert (B.fresh_loc (B.loc_buffer buf) h0 h4);
  (**) c.update_multi_zero i (c.v h4 hash_state);
  (**) split_at_last_empty (U32.v (c.block_len i));
  (**) B.modifies_only_not_unused_in B.loc_none h0 h4;

  (**) let h5 = ST.get () in
  (**) assert (
    let h = h5 in
    let s = (B.get h5 p 0) in
    let State hash_state buf_ total_len seen = s in
    let seen = G.reveal seen in
    let blocks, rest = split_at_last (U32.v (c.block_len i)) seen in
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

val init: #index:Type0 -> c:block index -> i:G.erased index -> (
  let i = G.reveal i in
  s:state c i -> Stack unit
  (requires (fun h0 ->
    invariant c i h0 s))
  (ensures (fun h0 _ h1 ->
    preserves_freeable c i s h0 h1 /\
    invariant c i h1 s /\
    seen c i h1 s == S.empty /\
    footprint c i h0 s == footprint c i h1 s /\
    B.(modifies (footprint c i h0 s) h0 h1))))

let init #index c i s =
  let aux (h:HS.mem) (s:c.state i): Lemma
    (requires (c.invariant h s))
    (ensures (B.loc_in (c.footprint #i h s) h))
    [SMTPat (c.invariant h s)]
  =
    c.invariant_loc_in_footprint #i h s
  in
  let aux l s h0 h1: Lemma
    (requires
      c.invariant h0 s /\
      c.freeable h0 s /\
      B.loc_disjoint l (c.footprint #i h0 s) /\
      B.modifies l h0 h1)
    (ensures (
      c.freeable h1 s))
    [ SMTPat (c.freeable h1 s); SMTPat (B.modifies l h0 h1) ]
  =
    c.frame_freeable #i l s h0 h1
  in

  let open LowStar.BufferOps in
  let h1 = ST.get () in
  let State hash_state buf _ _ = !*s in
  // JP: figuring out the alg at run-time is useful, but entails a lot more
  // proof difficulty; note the let-binding below, as well as the fact that
  // implicit argument resolution basically no longer works after this...
  let i = c.index_of_state i hash_state in
  [@inline_let]
  let hash_state: c.state i = hash_state in

  c.init (G.hide i) hash_state;
  let h2 = ST.get () in
  c.update_multi_zero i (c.v h2 hash_state);
  split_at_last_empty U32.(v (c.block_len i));

  B.upd s 0ul (State hash_state buf 0UL (G.hide S.empty));
  let h3 = ST.get () in
  c.frame_invariant B.(loc_buffer s) hash_state h2 h3;

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
  );
  assert (invariant_s c i h3 (B.get h3 s 0))
