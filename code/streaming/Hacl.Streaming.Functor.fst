module Hacl.Streaming.Functor

/// Provided an instance of the type class, this creates a streaming API on top.
/// This means that every function in this module takes two extra arguments
/// compared to the previous streaming module specialized for hashes: the type
/// of the index, and a type class for that index. Then, as usual, a given value
/// for the index as a parameter.

#set-options "--max_fuel 0 --max_ifuel 0 \
  --using_facts_from '*,-LowStar.Monotonic.Buffer.unused_in_not_unused_in_disjoint_2' --z3rlimit 50"

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
open Hacl.Streaming.Spec

/// State machinery
/// ===============

/// Little bit of trickery here to make sure state_s is parameterized over
/// something at Type0, not Type0 -> Type0 -- otherwise it wouldn't monomorphize
/// in KreMLin.
noeq
type state_s #index (c: block index) (i: index)
  (t: Type0 { t == c.state.s i })
  (t': Type0 { t' == optional_key i c.km c.key })
=
| State:
    block_state: t ->
    buf: B.buffer Lib.IntTypes.uint8 { B.len buf = c.block_len i } ->
    total_len: UInt64.t ->
    seen: G.erased (S.seq uint8) ->
    // Stupid name conflict on overloaded projectors leads to inscrutable
    // interleaving errors. Need a field name that does not conflict with the
    // one in Hacl.Streaming.Interface. Sigh!!
    p_key: t' ->
    state_s #index c i t t'

/// Defining a series of helpers to deal with the indexed type of the key. This
/// makes proofs easier.

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

let optional_hide #index
  (#i: index)
  (#km: key_management)
  (#key: stateful index)
  (h: HS.mem)
  (k: key.s i):
  optional_key i km key
=
  allow_inversion key_management;
  match km with
  | Erased -> G.hide (key.v i h k)
  | Runtime -> k

let optional_frame #index
  (#i: index)
  (#km: key_management)
  (#key: stateful index)
  (l: B.loc)
  (s: optional_key i km key)
  (h0 h1: HS.mem):
  Lemma
    (requires (
      optional_invariant h0 s /\
      optional_freeable h0 s /\
      B.loc_disjoint l (optional_footprint h0 s) /\
      B.modifies l h0 h1))
    (ensures (
      optional_invariant h1 s /\
      optional_reveal h0 s == optional_reveal h1 s /\
      optional_footprint h1 s == optional_footprint h0 s /\
      optional_freeable h1 s))
=
  allow_inversion key_management;
  match km with
  | Erased -> ()
  | Runtime ->
      key.frame_invariant #i l s h0 h1;
      key.frame_freeable #i l s h0 h1

let footprint_s #index (c: block index) (i: index) (h: HS.mem) s =
  let State block_state buf_ _ _ p_key = s in
  B.(loc_addr_of_buffer buf_ `loc_union` c.state.footprint h block_state `loc_union` optional_footprint h p_key)

/// Invariants
/// ==========

(*
/// Generic state invariant. Not all the functions split the seen data at the same
/// point, to differentiate between the data which has been hashed and the data
/// which is still in the buffer, hence the [hashed_len] parameter.
unfold
val gen_invariant_s (#index: Type0) (c: block index) (i: index) (h: HS.mem)
                    (s: state_s' c i)
                    (hashed_len : nat{
                       hashed_len <= Seq.length (State?.seen s) /\
                       (hashed_len % UInt32.v (Block?.block_len c i)) = 0})
                    : Type0

let gen_invariant_s #index (c: block index) (i: index) h s hashed_len =
  let State block_state buf_ total_len seen key = s in
  let seen = G.reveal seen in
  let blocks, rest = split_at_last c i seen in

  // Liveness and disjointness (administrative)
  B.live h buf_ /\ c.state.invariant #i h block_state /\ optional_invariant h key /\
  B.(loc_disjoint (loc_buffer buf_) (c.state.footprint h block_state)) /\
  B.(loc_disjoint (loc_buffer buf_) (optional_footprint h key)) /\
  B.(loc_disjoint (optional_footprint h key) (c.state.footprint h block_state)) /\
  B.freeable buf_ /\ c.state.freeable h block_state /\ optional_freeable h key /\

  // Formerly, the "hashes" predicate
  S.length blocks + S.length rest = U64.v total_len /\
  S.length seen = U64.v total_len /\
  U64.v total_len <= c.max_input_length i /\
  // Note the double equals here, we now no longer know that this is a sequence.
  c.state.v i h block_state == c.update_multi_s i (c.init_s i (optional_reveal h key)) blocks /\
  S.equal (S.slice (B.as_seq h buf_) 0 (U64.v total_len % U32.v (c.block_len i))) rest///\

/// The real invariant
let invariant_s #index (c: block index) (i: index) h s =
  let n = split_at_last_num_blocks c i (Seq.length (State?.seen s)) in
  let l = UInt32.v (Block?.block_len c i) in
  gen_invariant_s c i h s (n * l)

/// This one is not an invariant: it is used to describe the state right after
/// the internal buffer has been hashed.
let invariant_s_post_hash #index (c: block index) (i: index) h s =
  let l = UInt32.v (Block?.block_len c i) in
  let n = Seq.length (State?.seen s) / l in
  let hashed_len = n * l in
  (**) Math.Lemmas.division_propriety (Seq.length (State?.seen s)) l;
  (**) assert(hashed_len <= Seq.length (State?.seen s));
  (**) Math.Lemmas.multiple_modulo_lemma n l;
  (**) assert(hashed_len % l = 0);
  gen_invariant_s c i h s (n * l)

let invariant_post_hash #index (c: block index) (i: index) (m: HS.mem) (s: state' c i) =
  invariant_visible c i m s /\
  invariant_s_post_hash c i m (B.get m s 0) *)

let invariant_s #index (c: block index) (i: index) h s =
  let State block_state buf_ total_len seen key = s in
  let seen = G.reveal seen in
  let blocks, rest = split_at_last c i seen in

  // Liveness and disjointness (administrative)
  B.live h buf_ /\ c.state.invariant #i h block_state /\ optional_invariant h key /\
  B.(loc_disjoint (loc_buffer buf_) (c.state.footprint h block_state)) /\
  B.(loc_disjoint (loc_buffer buf_) (optional_footprint h key)) /\
  B.(loc_disjoint (optional_footprint h key) (c.state.footprint h block_state)) /\
  B.freeable buf_ /\ c.state.freeable h block_state /\ optional_freeable h key /\

  // Formerly, the "hashes" predicate
  S.length blocks + S.length rest = U64.v total_len /\
  S.length seen = U64.v total_len /\
  U64.v total_len <= c.max_input_length i /\
  // Note the double equals here, we now no longer know that this is a sequence.
  c.state.v i h block_state == c.update_multi_s i (c.init_s i (optional_reveal h key)) blocks /\
//  S.equal (S.slice (B.as_seq h buf_) 0 (U64.v total_len % U32.v (c.block_len i))) rest///\
  S.equal (S.slice (B.as_seq h buf_) 0 (Seq.length rest)) rest///\

  // Note that we lazily flush the internal buffer, because we need to make sure
  // it is not empty upon calling update_last
//  (S.length seen > 0 ==> S.length rest > 0) *)

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
  optional_reveal h (State?.p_key (B.deref h s))

let frame_invariant #index c i l s h0 h1 =
  let state_t = B.deref h0 s in
  let State block_state _ _ _ p_key = state_t in
  c.state.frame_invariant #i l block_state h0 h1;
  c.state.frame_freeable #i l block_state h0 h1;
  allow_inversion key_management;
  match c.km with
  | Erased -> ()
  | Runtime ->
      c.key.frame_freeable #i l p_key h0 h1;
      c.key.frame_invariant #i l p_key h0 h1

let frame_seen #_ _ _ _ _ _ _ =
  ()

/// Stateful API
/// ============

let index_of_state #index c i t t' s =
  let open LowStar.BufferOps in
  let State block_state _ _ _ _ = !*s in
  c.index_of_state i block_state

let create_in #index c i t t' k r =
  [@inline_let] let _ = c.state.invariant_loc_in_footprint #i in
  [@inline_let] let _ = c.key.invariant_loc_in_footprint #i in
  allow_inversion key_management;

  (**) let h0 = ST.get () in

  (**) B.loc_unused_in_not_unused_in_disjoint h0;
  let buf = B.malloc r (Lib.IntTypes.u8 0) (c.block_len i) in
  (**) let h1 = ST.get () in
  (**) assert (B.fresh_loc (B.loc_buffer buf) h0 h1);
  (**) B.loc_unused_in_not_unused_in_disjoint h1;
  (**) B.(modifies_only_not_unused_in loc_none h0 h1);
  (**) c.key.frame_invariant B.loc_none k h0 h1;

  let block_state = c.state.create_in i r in
  (**) let h2 = ST.get () in
  (**) assert (B.fresh_loc (c.state.footprint #i h2 block_state) h0 h2);
  (**) B.loc_unused_in_not_unused_in_disjoint h2;
  (**) B.(modifies_only_not_unused_in loc_none h1 h2);
  (**) c.key.frame_invariant B.loc_none k h1 h2;

  let k': optional_key i c.km c.key =
    match c.km with
    | Runtime ->
        let k' = c.key.create_in i r in
        (**) let h3 = ST.get () in
        (**) B.loc_unused_in_not_unused_in_disjoint h3;
        (**) B.(modifies_only_not_unused_in loc_none h2 h3);
        (**) c.key.frame_invariant B.loc_none k h2 h3;
        (**) c.state.frame_invariant B.loc_none block_state h2 h3;
        (**) c.state.frame_freeable B.loc_none block_state h2 h3;
        (**) assert (B.fresh_loc (c.key.footprint #i h3 k') h0 h3);
        (**) assert (c.key.invariant #i h3 k');
        (**) assert (c.key.invariant #i h3 k);
        (**) assert B.(loc_disjoint (c.key.footprint #i h3 k) (c.key.footprint #i h3 k'));
        c.key.copy i k k';
        (**) let h4 = ST.get () in
        (**) assert (B.fresh_loc (c.key.footprint #i h4 k') h0 h4);
        (**) B.loc_unused_in_not_unused_in_disjoint h4;
        (**) B.(modifies_only_not_unused_in loc_none h2 h4);
        (**) assert (c.key.invariant #i h4 k');
        (**) c.key.frame_invariant (c.key.footprint #i h3 k') k h3 h4;
        (**) c.state.frame_invariant (c.key.footprint #i h3 k') block_state h3 h4;
        (**) c.state.frame_freeable (c.key.footprint #i h3 k') block_state h3 h4;
        k'
    | Erased ->
        G.hide (c.key.v i h0 k)
  in
  (**) let h5 = ST.get () in
  (**) assert (B.fresh_loc (optional_footprint h5 k') h0 h5);
  (**) assert (B.fresh_loc (c.state.footprint #i h5 block_state) h0 h5);

  let s = State block_state buf 0UL (G.hide S.empty) k' in
  (**) assert (B.fresh_loc (footprint_s c i h5 s) h0 h5);

  (**) B.loc_unused_in_not_unused_in_disjoint h5;
  let p = B.malloc r s 1ul in
  (**) let h6 = ST.get () in
  (**) B.(modifies_only_not_unused_in loc_none h5 h6);
  (**) B.(modifies_only_not_unused_in loc_none h0 h6);
  (**) c.key.frame_invariant B.loc_none k h5 h6;
  (**) c.state.frame_invariant B.loc_none block_state h5 h6;
  (**) optional_frame B.loc_none k' h5 h6;
  (**) assert (B.fresh_loc (B.loc_addr_of_buffer p) h0 h6);
  (**) assert (B.fresh_loc (footprint_s c i h6 s) h0 h6);
  (**) c.state.frame_freeable B.loc_none block_state h5 h6;
  (**) assert (optional_reveal h5 k' == optional_reveal h6 k');

  c.init (G.hide i) k block_state;
  (**) let h7 = ST.get () in
  (**) assert (B.fresh_loc (c.state.footprint #i h7 block_state) h0 h7);
  (**) assert (B.fresh_loc (B.loc_buffer buf) h0 h7);
  (**) optional_frame (c.state.footprint #i h7 block_state) k' h6 h7;
  (**) c.update_multi_zero i (c.state.v i h7 block_state);
  (**) split_at_last_empty c i;
  (**) B.modifies_only_not_unused_in B.loc_none h0 h7;
  (**) assert (c.state.v i h7 block_state == c.init_s i (optional_reveal h6 k'));

  (**) let h8 = ST.get () in
  (**) assert (
    let h = h8 in
    let s = (B.get h8 p 0) in
    let State block_state buf_ total_len seen _ = s in
    let seen = G.reveal seen in
    let blocks, rest = split_at_last c i seen in
    // JP: unclear why I need to assert this... but without it the proof doesn't
    // go through.
    U64.v total_len < c.max_input_length i /\
    True
  );
  (**) assert (invariant c i h8 p);
  (**) assert (seen c i h8 p == S.empty);
  (**) assert B.(modifies loc_none h0 h8);
  (**) assert (B.fresh_loc (footprint c i h8 p) h0 h8);
  (**) assert B.(loc_includes (loc_region_only true r) (footprint c i h8 p));

  (**) assert (ST.equal_stack_domains h1 h8);
  (**) assert (ST.equal_stack_domains h0 h1);

  p

let init #index c i t t' k s =
  [@inline_let] let _ = c.state.invariant_loc_in_footprint #i in
  [@inline_let] let _ = c.state.frame_freeable #i in
  [@inline_let] let _ = c.key.invariant_loc_in_footprint #i in
  [@inline_let] let _ = c.key.frame_freeable #i in
  allow_inversion key_management;

  let open LowStar.BufferOps in
  (**) let h1 = ST.get () in
  let State block_state buf _ _ k' = !*s in
  let i = c.index_of_state i block_state in
  [@inline_let]
  let block_state: c.state.s i = block_state in

  c.init (G.hide i) k block_state;
  (**) let h2 = ST.get () in
  (**) optional_frame #_ #i #c.km #c.key (c.state.footprint #i h1 block_state) k' h1 h2;
  (**) c.key.frame_invariant (c.state.footprint #i h1 block_state) k h1 h2;
  (**) c.update_multi_zero i (c.state.v i h2 block_state);
  (**) split_at_last_empty c i;

  let k': optional_key i c.km c.key =
    match c.km with
    | Runtime ->
        c.key.copy i k k';
        (**) let h4 = ST.get () in
        (**) assert (c.key.invariant #i h4 k');
        (**) c.key.frame_invariant (c.key.footprint #i h2 k') k h2 h4;
        (**) c.state.frame_invariant (c.key.footprint #i h2 k') block_state h2 h4;
        (**) c.state.frame_freeable (c.key.footprint #i h2 k') block_state h2 h4;
        k'
    | Erased ->
        G.hide (c.key.v i h1 k)
  in
  (**) let h2 = ST.get () in

  [@ inline_let ]
  let tmp: state_s c i t t' = State block_state buf 0UL (G.hide S.empty) k' in
  B.upd s 0ul tmp;
  (**) let h3 = ST.get () in
  (**) c.state.frame_invariant B.(loc_buffer s) block_state h2 h3;
  (**) optional_frame #_ #i #c.km #c.key B.(loc_buffer s) k' h2 h3;

  // This seems to cause insurmountable difficulties. Puzzled.
  ST.lemma_equal_domains_trans h1 h2 h3;

  // AR: 07/22: same old `Seq.equal` and `==` story
  assert (Seq.equal (seen c i h3 s) Seq.empty);

  //assert (hashed h3 s == S.empty);
  assert (footprint c i h1 s == footprint c i h3 s);
  assert (B.(modifies (footprint c i h1 s) h1 h3));
  //assert (B.live h3 s);
  //assert (B.(loc_disjoint (loc_addr_of_buffer s) (footprint_s h3 (B.deref h3 s))));
  assert (
    let h = h3 in
    let s = B.get h3 s 0 in
    let State block_state buf_ total_len seen _ = s in
    let seen = G.reveal seen in
    let blocks, rest = split_at_last c i seen in

    // Formerly, the "hashes" predicate
    S.length blocks + S.length rest = U64.v total_len /\
    S.length seen = U64.v total_len /\
    U64.v total_len < c.max_input_length i
  );
  assert (invariant_s c i h3 (B.get h3 s 0))

/// Some helpers to minimize modulo-reasoning
/// =========================================

/// The ``rest`` function below allows computing, based ``total_len`` stored in
/// the state, the length of useful data currently stored in ``buf``.
/// Unsurprisingly, there's a fair amount of modulo reasoning here because of
/// 64-bit-to-32-bit conversions, so we do them once and for all in a helper.
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

(*inline_for_extraction noextract
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
  r *)

inline_for_extraction noextract
let rest #index (c: block index) (i: index)
  (total_len: UInt64.t): (x:UInt32.t {
    let n = split_at_last_num_blocks c i (U64.v total_len) in
    let l = U32.v (c.block_len i) in
    U32.v x = U64.v total_len - (n * l) })
=
  admit()

(*  let open FStar.Int.Cast in
  let x = total_len `U64.rem` uint32_to_uint64 (c.block_len i) in
  if U64.(x =^ uint_to_t 0 && total_len >^ uint_to_t 0) then
    begin
//    uint32_to_uint64 (c.block_len i)
    end
  else
    begin
    x
    end

  let x = total_len `U64.rem` uint32_to_uint64 (c.block_len i) in
  let r = FStar.Int.Cast.uint64_to_uint32 x in
  mod_block_len_bound c i total_len
  r

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
  r *)
#pop-options

#pop-options

/// We always add 32-bit lengths to 64-bit lengths. Having a helper for that allows
/// doing modulo reasoning once and for all.
inline_for_extraction noextract
let add_len #index (c: block index) (i: index) (total_len: UInt64.t) (len: UInt32.t):
  Pure UInt64.t
    (requires U64.v total_len + U32.v len <= c.max_input_length i)
    (ensures fun x -> U64.v x = U64.v total_len + U32.v len /\ U64.v x <= c.max_input_length i)
=
  total_len `U64.add` Int.Cast.uint32_to_uint64 len

#push-options "--z3cliopt smt.arith.nl=false"
let add_len_small #index (c: block index) (i: index) (total_len: UInt64.t) (len: UInt32.t): Lemma
  (requires
    U32.v len <= U32.v (c.block_len i) - U32.v (rest c i total_len) /\
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

/// Beginning of the three sub-cases (see Hacl.Streaming.Spec)
/// ==========================================================

let total_len_h #index (c: block index) (i: index) h (p: state' c i) =
  State?.total_len (B.deref h p)

let seen_h #index (c: block index) (i: index) h (p: state' c i) =
  State?.seen (B.deref h p)

let split_at_last_seen_h #index (c: block index) (i: index) h (p: state' c i) =
  let seen = seen_h c i h p in
  let blocks, rest = split_at_last c i seen in
  blocks, rest

inline_for_extraction noextract
val update_small:
  #index:Type0 ->
  (c: block index) ->
  i:G.erased index -> (
  let i = G.reveal i in
  t:Type0 { t == c.state.s i } ->
  t':Type0 { t' == optional_key i c.km c.key } ->
  s:state c i t t' ->
  data: B.buffer uint8 ->
  len: UInt32.t ->
  Stack unit
    (requires fun h0 ->
      update_pre c i s data len h0 /\
      U32.v len <= U32.v (c.block_len i) - U32.v (rest c i (total_len_h c i h0 s)))
    (ensures fun h0 s' h1 ->
      update_post c i s data len h0 h1))

#push-options "--z3rlimit 200"
let update_small #index c i t t' p data len =
  [@inline_let] let _ = c.state.invariant_loc_in_footprint #i in
  [@inline_let] let _ = c.state.frame_freeable #i in
  [@inline_let] let _ = c.key.invariant_loc_in_footprint #i in
  [@inline_let] let _ = c.key.frame_freeable #i in

  let open LowStar.BufferOps in
  let h00 = ST.get () in
  assert (invariant c i h00 p);
  let s = !*p in
  let State block_state buf total_len seen_ k' = s in
  let i = c.index_of_state i block_state in
  [@inline_let]
  let block_state: c.state.s i = block_state in

  let sz = rest c i total_len in
  add_len_small c i total_len len;
  let h0 = ST.get () in
  let buf1 = B.sub buf 0ul sz in
  let buf2 = B.sub buf sz len in

  B.blit data 0ul buf2 0ul len;
  let h1 = ST.get () in
  split_at_last_small c i (G.reveal seen_) (B.as_seq h0 data);
  c.state.frame_invariant (B.loc_buffer buf) block_state h0 h1;
  optional_frame #_ #i #c.km #c.key (B.loc_buffer buf) k' h0 h1;
  assert (B.as_seq h1 data == B.as_seq h0 data);

  let total_len = add_len c i total_len len in
  [@inline_let]
  let tmp: state_s c i t t' =
    State #index #c #i block_state buf total_len (G.hide (G.reveal seen_ `S.append` (B.as_seq h0 data))) k'
  in
  p *= tmp;
  let h2 = ST.get () in
  assert (B.as_seq h2 data == B.as_seq h1 data);
  c.state.frame_invariant (B.loc_buffer p) block_state h1 h2;
  optional_frame #_ #i #c.km #c.key (B.loc_buffer p) k' h1 h2;
  assert (
    let b = S.append (G.reveal seen_) (B.as_seq h0 data) in
    let blocks, rest = split_at_last c i b in
    S.length blocks + S.length rest = U64.v total_len /\
    S.length b = U64.v total_len /\
    U64.v total_len <= c.max_input_length i /\
    S.equal (S.slice (B.as_seq h2 buf) 0 (U64.v total_len % U32.v (c.block_len i))) rest
    );
  assert (seen c i h2 p `S.equal` (S.append (G.reveal seen_) (B.as_seq h0 data)));
  assert (footprint c i h0 p == footprint c i h2 p);
  assert (equal_domains h00 h2)

#pop-options

/// Case 2: we have no buffered data (ie: the buffer was just initialized), or the
/// internal buffer is full meaning that we can just hash it to go to the case where
/// there is no buffered data. Of course, the data we append has to be non-empty,
/// otherwise we might end-up with an empty internal buffer.

#push-options "--z3rlimit 100"
inline_for_extraction noextract
val update_empty_or_full_buf:
  #index:Type0 ->
  c:block index ->
  i:G.erased index -> (
  let i = G.reveal i in
  t:Type0 { t == c.state.s i } ->
  t':Type0 { t' == optional_key i c.km c.key } ->
  s:state c i t t' ->
  data: B.buffer Lib.IntTypes.uint8 ->
  len: UInt32.t ->
  Stack unit
    (requires fun h0 ->
      update_pre c i s data len h0 /\
      (rest c i (total_len_h c i h0 s) = 0ul \/
       rest c i (total_len_h c i h0 s) = c.block_len i) /\
       U32.v len > 0)
    (ensures fun h0 s' h1 ->
      update_post c i s data len h0 h1))

inline_for_extraction noextract
let seen_pred = seen

(* TODO: move with rest *)
inline_for_extraction noextract
let nblocks #index (c: block index) (i: index)
  (len: UInt32.t): (x:UInt32.t {
    U32.v x = split_at_last_num_blocks c i (U32.v len) })
=
  admit()

let update_empty_or_full_buf #index c i t t' p data len =
  [@inline_let] let _ = c.state.invariant_loc_in_footprint #i in
  [@inline_let] let _ = c.state.frame_freeable #i in
  [@inline_let] let _ = c.key.invariant_loc_in_footprint #i in
  [@inline_let] let _ = c.key.frame_freeable #i in
  [@inline_let] let _ = c.update_multi_associative i in

  let open LowStar.BufferOps in
  let s = !*p in
  let State block_state buf total_len seen k' = s in
  let i = c.index_of_state i block_state in
  [@inline_let]
  let block_state: c.state.s i = block_state in
  let sz = rest c i total_len in
  let h0 = ST.get () in
  
  assert(
    let blocks, rest = split_at_last c i seen in
    Seq.length rest = U32.v sz /\
    c.state.v i h0 block_state ==
    c.update_multi_s i (c.init_s i (optional_reveal h0
                     (k' <: optional_key i c.km c.key))) blocks);
  
  (* Start by "flushing" the buffer: hash it so that all the data seen so far
   * has been hash and we can consider the buffer as empty *)
  if U32.(sz =^ 0ul) then
    assert(c.state.v i h0 block_state ==
      c.update_multi_s i (c.init_s i (optional_reveal h0 (k' <: optional_key i c.km c.key))) seen)
  else
    begin
    c.update_multi (G.hide i) block_state buf (c.block_len i);
      begin
      let h1 = ST.get () in
      let init_state = (c.init_s i (optional_reveal h0 (k' <: optional_key i c.km c.key))) in
      let blocks, rest = split_at_last c i seen in
      assert(c.state.v i h0 block_state == c.update_multi_s i init_state blocks);
      assert(c.state.v i h1 block_state ==
               c.update_multi_s i (c.update_multi_s i init_state blocks) rest);
      assert(seen `Seq.equal` Seq.append blocks rest);
      assert(c.state.v i h1 block_state == c.update_multi_s i init_state seen)
      end
    end;
 
  let h1 = ST.get () in

  assert(c.state.v i h1 block_state ==
    c.update_multi_s i (c.init_s i (optional_reveal h0 (k' <: optional_key i c.km c.key))) seen);

  split_at_last_blocks c i (G.reveal seen) (B.as_seq h0 data);

  let n_blocks = nblocks c i len in
  let data1_len = n_blocks `U32.mul` c.block_len i in
  let data2_len = len `U32.sub` data1_len in
  let data1 = B.sub data 0ul data1_len in
  let data2 = B.sub data data1_len data2_len in
  c.update_multi (G.hide i) block_state data1 data1_len;
  let h01 = ST.get () in
  optional_frame #_ #i #c.km #c.key (c.state.footprint h0 block_state) k' h0 h01;

  let dst = B.sub buf 0ul data2_len in
  let h1 = ST.get () in
  B.blit data2 0ul dst 0ul data2_len;
  let h2 = ST.get () in
  c.state.frame_invariant (B.loc_buffer buf) block_state h1 h2;
  optional_frame #_ #i #c.km #c.key (B.loc_buffer buf) k' h1 h2;

  S.append_assoc (G.reveal seen) (B.as_seq h0 data1) (B.as_seq h0 data2);
  assert (S.equal
    (S.append (S.append (G.reveal seen) (B.as_seq h0 data1)) (B.as_seq h0 data2))
    (S.append (G.reveal seen) (S.append (B.as_seq h0 data1) (B.as_seq h0 data2))));

  [@inline_let]
  let tmp: state_s c i t t' = State #index #c #i block_state buf (add_len c i total_len len)
    (G.hide (G.reveal seen `S.append` B.as_seq h0 data)) k'
  in
  p *= tmp;
  let h3 = ST.get () in
  c.state.frame_invariant (B.loc_buffer p) block_state h2 h3;
  optional_frame #_ #i #c.km #c.key (B.loc_buffer p) k' h2 h3;

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

/// Case 3: we are given just enough data to end up on the boundary. It is just
/// a sub-case of [update_small], but with a little bit more precise pre and post
/// conditions.

(* unfold noextract
let update_round_post
  #index
  (c: block index)
  (i: index)
  (s: state' c i)
  (data: B.buffer uint8)
  (len: UInt32.t)
  (h0 h1: HS.mem)
=
  update_post c i s data len h0 h1 /\ *)

inline_for_extraction noextract
val update_round:
  #index:Type0 ->
  c:block index ->
  i:G.erased index -> (
  let i = G.reveal i in
  t:Type0 { t == c.state.s i } ->
  t':Type0 { t' == optional_key i c.km c.key } ->
  s:state c i t t' ->
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
      begin
      let blocks, rest = split_at_last_seen_h c i h0 s in
      let blocks', rest' = split_at_last_seen_h c i h1 s in
      blocks' `S.equal` blocks /\
      rest' `S.equal` S.append rest (B.as_seq h0 data) /\
      S.length rest' = U32.v (c.block_len i)
      end))

#push-options "--z3rlimit 200"
let update_round #index c i t t' p data len =
  [@inline_let] let _ = c.state.invariant_loc_in_footprint #i in
  [@inline_let] let _ = c.state.invariant_loc_in_footprint #i in
  [@inline_let] let _ = c.key.frame_freeable #i in
  [@inline_let] let _ = c.key.frame_freeable #i in
  [@inline_let] let _ = c.update_multi_associative i in

  let open LowStar.BufferOps in
  (**) let h0 = ST.get() in
  update_small #index c i t t' p data len;
  (**) let h1 = ST.get() in
  (**) split_at_last_small c i (seen_h c i h0 p) (B.as_seq h0 data)
#pop-options  

(* inline_for_extraction noextract
val update_round:
  #index:Type0 ->
  c:block index ->
  i:G.erased index -> (
  let i = G.reveal i in
  t:Type0 { t == c.state.s i } ->
  t':Type0 { t' == optional_key i c.km c.key } ->
  s:state c i t t' ->
  data: B.buffer uint8 ->
  len: UInt32.t ->
  Stack unit
    (requires fun h0 ->
      update_pre c i s data len h0 /\ (
      let r = rest c i (total_len_h c i h0 s) in
      U32.v len + U32.v r = U32.v (c.block_len i) /\
      r <> 0ul))
    (ensures fun h0 _ h1 ->
      update_round_post c i s data len h0 h1 /\
      U64.v (total_len_h c i h1 s) % U32.v (c.block_len i) = 0)) *)

(*unfold noextract
let update_round_post
  #index
  (c: block index)
  (i: index)
  (s: state' c i)
  (data: B.buffer uint8)
  (len: UInt32.t)
  (h0 h1: HS.mem)
=
  invariant_post_hash c i h1 s /\
  B.(modifies (footprint c i h0 s) h0 h1) /\
  footprint c i h0 s == footprint c i h1 s /\
  seen c i h1 s == seen c i h0 s `S.append` B.as_seq h0 data /\
  key c i h1 s == key c i h0 s

inline_for_extraction noextract
val update_round:
  #index:Type0 ->
  c:block index ->
  i:G.erased index -> (
  let i = G.reveal i in
  t:Type0 { t == c.state.s i } ->
  t':Type0 { t' == optional_key i c.km c.key } ->
  s:state c i t t' ->
  data: B.buffer uint8 ->
  len: UInt32.t ->
  Stack unit
    (requires fun h0 ->
      update_pre c i s data len h0 /\ (
      let r = rest c i (total_len_h c i h0 s) in
      U32.v len + U32.v r = U32.v (c.block_len i) /\
      r <> 0ul))
    (ensures fun h0 _ h1 ->
      update_round_post c i s data len h0 h1 /\
      U64.v (total_len_h c i h1 s) % U32.v (c.block_len i) = 0))

#push-options "--z3rlimit 200"
let update_round #index c i t t' p data len =
  [@inline_let] let _ = c.state.invariant_loc_in_footprint #i in
  [@inline_let] let _ = c.state.invariant_loc_in_footprint #i in
  [@inline_let] let _ = c.key.frame_freeable #i in
  [@inline_let] let _ = c.key.frame_freeable #i in
  [@inline_let] let _ = c.update_multi_associative i in

  let open LowStar.BufferOps in
  let s = !*p in
  let State block_state buf_ total_len seen k' = s in
  let i = c.index_of_state i block_state in
  [@inline_let]
  let block_state: c.state.s i = block_state in
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
  c.state.frame_invariant (B.loc_buffer buf_) block_state h0 h1;
  c.state.frame_freeable (B.loc_buffer buf_) block_state h0 h1;
  optional_frame #_ #i #c.km #c.key (B.loc_buffer buf_) k' h0 h1;
  c.update_multi (G.hide i) block_state buf0 (c.block_len i);
  let h2 = ST.get () in
  optional_frame #_ #i #c.km #c.key (c.state.footprint h1 block_state) k' h1 h2;
  (* Proof interlude *)
  begin
    let seen' = G.reveal seen `S.append` B.as_seq h0 data in
    let blocks', rest' = split_at_last c i seen' in
    let seen = G.reveal seen in
    let blocks, rest = split_at_last c i seen in
    assert (S.length blocks % U32.v (c.block_len i) = 0);
    assert (S.length (rest `S.append` B.as_seq h0 data) % U32.v (c.block_len i) = 0);
    let init = c.init_s i (optional_reveal #_ #i #c.km #c.key h0 k') in
    calc (==) {
      c.state.v i h2 block_state;
    (==) { }
      c.update_multi_s i (c.state.v i h1 block_state) (B.as_seq h1 buf0);
    (==) { }
      c.update_multi_s i (c.state.v i h1 block_state) (B.as_seq h0 buf1 `S.append` B.as_seq h0 data);
    (==) { }
      c.update_multi_s i (c.update_multi_s i init blocks) (B.as_seq h0 buf1 `S.append` B.as_seq h0 data);
    (==) { }
      c.update_multi_s i (c.update_multi_s i init blocks) (rest `S.append` B.as_seq h0 data);
    (==) { }
      c.update_multi_s i init (blocks `S.append` (rest `S.append` B.as_seq h0 data));
    (==) { S.append_assoc blocks rest (B.as_seq h0 data) }
      c.update_multi_s i init (blocks `S.append` rest `S.append` B.as_seq h0 data);
    (==) { }
      c.update_multi_s i init (seen `S.append` B.as_seq h0 data);
    }
  end;
  [@inline_let]
  let tmp: state_s c i t t' = State #index #c #i block_state buf_ (add_len c i total_len len)
    (G.hide (G.reveal seen `S.append` B.as_seq h0 data)) k'
  in
  p *= tmp;
  let h3 = ST.get () in
  c.state.frame_invariant (B.loc_buffer p) block_state h2 h3;
  c.state.frame_freeable (B.loc_buffer p) block_state h2 h3;
  optional_frame #_ #i #c.km #c.key (B.loc_buffer p) k' h2 h3;
  assert (seen_pred c i h3 p `S.equal` (S.append (G.reveal seen) (B.as_seq h0 data)))
#pop-options *)

/// General update function, as a decomposition of the three sub-cases
/// ==================================================================

#push-options "--z3rlimit 200"
let update #index c i t t' p data len =
  let open LowStar.BufferOps in
  let s = !*p in
  let State block_state buf_ total_len seen k' = s in
  let i = c.index_of_state i block_state in
  let sz = rest c i total_len in  
  if len `U32.lte` (c.block_len i `U32.sub` sz) then
    update_small c (G.hide i) t t' p data len
  else if sz = 0ul then
    update_empty_or_full_buf c (G.hide i) t t' p data len
  else begin
    let h0 = ST.get () in
    let diff = c.block_len i `U32.sub` sz in
    let data1 = B.sub data 0ul diff in
    let data2 = B.sub data diff (len `U32.sub` diff) in
    update_round c (G.hide i) t t' p data1 diff;
    let h1 = ST.get () in
    update_empty_or_full_buf c (G.hide i) t t' p data2 (len `U32.sub` diff);
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
#pop-options

let mk_finish #index c i t t' p dst =
  [@inline_let] let _ = c.state.invariant_loc_in_footprint #i in
  [@inline_let] let _ = c.state.frame_freeable #i in
  [@inline_let] let _ = c.key.invariant_loc_in_footprint #i in
  [@inline_let] let _ = c.key.frame_freeable #i in
  [@inline_let] let _ = c.update_multi_associative i in
  [@inline_let] let _ = allow_inversion key_management in


  let open LowStar.BufferOps in
  let h0 = ST.get () in
  let State block_state buf_ total_len seen k' = !*p in

  push_frame ();
  let h1 = ST.get () in
  c.state.frame_invariant #i B.loc_none block_state h0 h1;
  c.state.frame_freeable #i B.loc_none block_state h0 h1;
  optional_frame #_ #i #c.km #c.key B.loc_none k' h0 h1;

  let buf_ = B.sub buf_ 0ul (rest c i total_len) in
  assert (
    let r = rest c i total_len in
    (U64.v total_len - U32.v r) % U32.v (c.block_len i) = 0);

  let tmp_block_state = c.state.alloca i in

  let h2 = ST.get () in
  assert (B.(loc_disjoint (c.state.footprint #i h2 tmp_block_state) (c.state.footprint #i h1 block_state)));
  B.modifies_only_not_unused_in B.loc_none h1 h2;
  c.state.frame_invariant #i B.loc_none block_state h1 h2;
  c.state.frame_freeable #i B.loc_none block_state h1 h2;
  optional_frame #_ #i #c.km #c.key B.loc_none k' h1 h2;

  c.state.copy (G.hide i) block_state tmp_block_state;

  let h3 = ST.get () in
  c.state.frame_invariant #i (c.state.footprint h2 tmp_block_state) block_state h2 h3;
  c.state.frame_freeable #i (c.state.footprint h2 tmp_block_state) block_state h2 h3;
  optional_frame #_ #i #c.km #c.key (c.state.footprint h2 tmp_block_state) k' h2 h3;

  c.update_last (G.hide i) tmp_block_state buf_ total_len;

  let h4 = ST.get () in
  c.state.frame_invariant #i (c.state.footprint h3 tmp_block_state) block_state h3 h4;
  c.state.frame_freeable #i (c.state.footprint h3 tmp_block_state) block_state h3 h4;
  optional_frame #_ #i #c.km #c.key (c.state.footprint h3 tmp_block_state) k' h3 h4;

  c.finish (G.hide i) k' tmp_block_state dst;

  let h5 = ST.get () in
  begin
    let seen = G.reveal seen in
    let block_length = U32.v (c.block_len i) in
    let n = S.length seen / block_length in
    let blocks, rest_ = S.split seen (n * block_length)  in
    let k = optional_reveal #_ #i #c.km #c.key h0 k' in
    calc (S.equal) {
      B.as_seq h5 dst;
    (S.equal) { }
      c.finish_s i k (c.state.v i h4 tmp_block_state);
    (S.equal) { }
      c.finish_s i k (
        c.update_last_s i (c.state.v i h3 tmp_block_state) (n * block_length)
          (S.slice (B.as_seq h3 buf_) 0 (U32.v (rest c i total_len))));
    (S.equal) { }
      c.finish_s i k (
        c.update_last_s i (c.state.v i h3 tmp_block_state) (n * block_length)
          (S.slice (B.as_seq h0 buf_) 0 (U32.v (rest c i total_len))));
    (S.equal) { }
      c.finish_s i k (
        c.update_last_s i
          (c.update_multi_s i (c.init_s i k) (S.slice seen 0 (n * block_length)))
          (n * block_length)
          (S.slice (B.as_seq h0 buf_) 0 (U32.v (rest c i total_len))));
    (S.equal) { c.spec_is_incremental i k seen }
      c.spec_s i k seen;
    }
  end;

  c.state.frame_invariant #i (B.loc_buffer dst) block_state h4 h5;
  c.state.frame_freeable #i (B.loc_buffer dst) block_state h4 h5;
  optional_frame #_ #i #c.km #c.key (B.loc_buffer dst) k' h4 h5;

  pop_frame ();
  let h6 = ST.get () in
  c.state.frame_invariant #i B.(loc_region_only false (HS.get_tip h5)) block_state h5 h6;
  c.state.frame_freeable #i B.(loc_region_only false (HS.get_tip h5)) block_state h5 h6;
  optional_frame #_ #i #c.km #c.key B.(loc_region_only false (HS.get_tip h5)) k' h5 h6;
  assert (seen_pred c i h6 p `S.equal` (G.reveal seen));

  // JP: this is not the right way to prove do this proof. Need to use
  // modifies_fresh_frame_popped instead, see e.g.
  // https://github.com/project-everest/everquic-crypto/blob/d812be94e9b1a77261f001c9accb2040b80b7c39/src/QUIC.Impl.fst#L1111
  // for an example
  let mloc = B.loc_union (B.loc_buffer dst) (footprint c i h0 p) in
  B.modifies_remove_fresh_frame h0 h1 h6 mloc;
  B.popped_modifies h5 h6;
  assert (B.(modifies mloc h0 h6))

let free #index c i t t' s =
  let _ = allow_inversion key_management in
  let open LowStar.BufferOps in
  let State block_state buf _ _ k' = !*s in
  let h0 = ST.get () in
  begin match c.km with
  | Runtime -> c.key.free i k'
  | Erased -> ()
  end;
  let h1 = ST.get () in
  c.state.frame_freeable #i (optional_footprint #index #i #c.km #c.key h0 k') block_state h0 h1;
  c.state.frame_invariant #i (optional_footprint #index #i #c.km #c.key h0 k') block_state h0 h1;
  c.state.free i block_state;
  B.free buf;
  B.free s
