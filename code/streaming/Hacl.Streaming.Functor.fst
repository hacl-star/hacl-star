module Hacl.Streaming.Functor

/// Provided an instance of the type class, this creates a streaming API on top.
/// This means that every function in this module takes two extra arguments
/// compared to the previous streaming module specialized for hashes: the type
/// of the index, and a type class for that index. Then, as usual, a given value
/// for the index as a parameter.

#set-options "--max_fuel 0 --max_ifuel 0 \
  --using_facts_from '*,-LowStar.Monotonic.Buffer.unused_in_not_unused_in_disjoint_2' \
  --z3rlimit 50 --record_options --z3rlimit_factor 4"

module ST = FStar.HyperStack.ST
module HS = FStar.HyperStack
module B = LowStar.Buffer
module G = FStar.Ghost
module S = FStar.Seq
module U32 = FStar.UInt32
module U64 = FStar.UInt64

open Hacl.Streaming.Block

open FStar.HyperStack.ST
open LowStar.BufferOps
open FStar.Mul
open Hacl.Streaming.Spec

/// State machinery
/// ===============

/// Little bit of trickery here to make sure state_s is parameterized over
/// something at Type0, not Type0 -> Type0 -- otherwise it wouldn't monomorphize
/// in KaRaMeL.
noeq
type state_s (c: index)
  (t: Type0 { t == c.state.s })
  (t': Type0 { t' == optional_key c })
=
| State:
    block_state: t ->
    buf: B.buffer Lib.IntTypes.uint8 { B.len buf = c.blocks_state_len } ->
    total_len: UInt64.t ->
    seen: G.erased (S.seq uint8) ->
    // Stupid name conflict on overloaded projectors leads to inscrutable
    // interleaving errors. Need a field name that does not conflict with the
    // one in Hacl.Streaming.Interface. Sigh!!
    p_key: t' ->
    state_s c t t'

/// Defining a series of helpers to deal with the indexed type of the key. This
/// makes proofs easier.

let optional_freeable
  (#i: index)
  (h: HS.mem)
  (k: optional_key i)
=
  allow_inversion key_management;
  match i.km with
  | Erased -> True
  | Runtime -> i.key.freeable h k

let optional_invariant
  (#i: index)
  (h: HS.mem)
  (k: optional_key i)
=
  allow_inversion key_management;
  match i.km with
  | Erased -> True
  | Runtime -> i.key.invariant h k

let optional_footprint
  (#i: index)
  (h: HS.mem)
  (k: optional_key i)
=
  allow_inversion key_management;
  match i.km with
  | Erased -> B.loc_none
  | Runtime -> i.key.footprint h k

let optional_reveal #i = Block.optional_t #i

/// This lemma is used to convert the Hacl.Streaming.Interface.stateful.frame_freeable
/// lemma, written with freeable in its precondition, into a lemma of the form:
/// [> freeable h0 s => freeable h1 s
val stateful_frame_preserves_freeable:
  #i:Stateful.index -> l:B.loc -> s:i.s -> h0:HS.mem -> h1:HS.mem ->
  Lemma
  (requires (
    i.invariant h0 s /\
    B.loc_disjoint l (i.footprint h0 s) /\
    B.modifies l h0 h1))
  (ensures (
    i.freeable h0 s ==> i.freeable h1 s))

let stateful_frame_preserves_freeable #i l s h0 h1 =
  let lem h0 h1 :
    Lemma
    (requires (
      i.invariant h0 s /\
      B.loc_disjoint l (i.footprint h0 s) /\
      B.modifies l h0 h1 /\
      i.freeable h0 s))
    (ensures (
       i.freeable h1 s))
    [SMTPat (i.freeable h0 s);
     SMTPat (i.freeable h1 s)] =
     i.frame_freeable l s h0 h1
  in
  ()

let optional_frame
  (#i: index)
  (l: B.loc)
  (s: optional_key i)
  (h0 h1: HS.mem):
  Lemma
    (requires (
      optional_invariant h0 s /\
      B.loc_disjoint l (optional_footprint h0 s) /\
      B.modifies l h0 h1))
    (ensures (
      optional_invariant h1 s /\
      optional_reveal h0 s == optional_reveal h1 s /\
      optional_footprint h1 s == optional_footprint h0 s /\
      (optional_freeable h0 s ==> optional_freeable h1 s)))
=
  allow_inversion key_management;
  match i.km with
  | Erased -> ()
  | Runtime ->
      i.key.frame_invariant l s h0 h1;
      stateful_frame_preserves_freeable #i.key l s h0 h1

let footprint_s (c: index) (h: HS.mem) s =
  let State block_state buf_ _ _ p_key = s in
  B.(loc_addr_of_buffer buf_ `loc_union` c.state.footprint h block_state `loc_union` optional_footprint h p_key)

/// Invariants
/// ==========

#push-options "--z3cliopt smt.arith.nl=false"
inline_for_extraction noextract
let invariant_s (c: index) h s =
  let State block_state buf_ total_len seen key = s in
  let seen = G.reveal seen in
  let key_v = optional_reveal h key in
  let all_seen = S.append (c.init_input_s key_v) seen in
  let blocks, rest = split_at_last c all_seen in
  (**) Math.Lemmas.modulo_lemma 0 (U32.v c.block_len);
  (**) assert(0 % U32.v c.block_len = 0);
  (**) Math.Lemmas.modulo_lemma 0 (U32.v c.blocks_state_len);
  (**) assert(0 % U32.v c.blocks_state_len = 0);

  // Liveness and disjointness (administrative)
  B.live h buf_ /\ c.state.invariant h block_state /\ optional_invariant h key /\
  B.(loc_disjoint (loc_buffer buf_) (c.state.footprint h block_state)) /\
  B.(loc_disjoint (loc_buffer buf_) (optional_footprint h key)) /\
  B.(loc_disjoint (optional_footprint h key) (c.state.footprint h block_state)) /\

  // Formerly, the "hashes" predicate
  S.length blocks + S.length rest = U64.v total_len /\
  U32.v c.init_input_len + S.length seen = U64.v total_len /\
  U64.v total_len <= U64.v c.max_input_len /\

  // Note the double equals here, we now no longer know that this is a sequence.
  c.state.v h block_state == c.update_multi_s (c.init_s key_v) 0 blocks /\
  S.equal (S.slice (B.as_seq h buf_) 0 (Seq.length rest)) rest
#pop-options

inline_for_extraction noextract
let freeable_s (c: index) (h: HS.mem) (s: state_s' c): Type0 =
  let State block_state buf_ total_len seen key = s in
  B.freeable buf_ /\ c.state.freeable h block_state /\ optional_freeable h key

let freeable (c: index) (h: HS.mem) (s: state' c) =
  freeable_s c h (B.get h s 0) /\
  B.freeable s

#push-options "--max_ifuel 1"
let invariant_loc_in_footprint c s m =
  [@inline_let]
  let _ = c.state.invariant_loc_in_footprint in
  [@inline_let]
  let _ = c.key.invariant_loc_in_footprint in
  ()
#pop-options

let seen c h s =
  G.reveal (State?.seen (B.deref h s))

let seen_bounded c h s =
  ()

let key c h s =
  optional_reveal h (State?.p_key (B.deref h s))

let init_input (c:index) (h:HS.mem) (s:state' c) : GTot bytes =
  c.init_input_s (key c h s)

let all_seen (c:index) (h:HS.mem) (s:state' c) : GTot bytes =
  S.append (init_input c h s) (seen c h s)

let frame_invariant c l s h0 h1 =
  let state_t = B.deref h0 s in
  let State block_state _ _ _ p_key = state_t in
  c.state.frame_invariant l block_state h0 h1;
  stateful_frame_preserves_freeable #c.state l block_state h0 h1;
  allow_inversion key_management;
  match c.km with
  | Erased -> ()
  | Runtime ->
      stateful_frame_preserves_freeable #c.key l p_key h0 h1;
      c.key.frame_invariant l p_key h0 h1

let frame_seen _ _ _ _ _ =
  ()

/// Stateful API
/// ============

let seen_length c t t' s =
  let open LowStar.BufferOps in
  let State _ _ total_len _ _ = !*s in
  total_len

(* TODO: create_in and alloca have big portions of proofs in common, so it may
 * be possible to factorize them, but it is not clear how *)
#restart-solver
#push-options "--z3rlimit 300"
[@ Meta.Attribute.specialize ]
let create_in #c k r =
  [@inline_let] let _ = c.state.invariant_loc_in_footprint in
  [@inline_let] let _ = c.key.invariant_loc_in_footprint in
  allow_inversion key_management;

  (**) let h0 = ST.get () in

  (**) B.loc_unused_in_not_unused_in_disjoint h0;
  let buf = B.malloc r (Lib.IntTypes.u8 0) c.blocks_state_len in
  (**) let h1 = ST.get () in
  (**) assert (B.fresh_loc (B.loc_buffer buf) h0 h1);
  (**) B.loc_unused_in_not_unused_in_disjoint h1;
  (**) B.(modifies_only_not_unused_in loc_none h0 h1);
  (**) c.key.frame_invariant B.loc_none k h0 h1;

  let block_state = state_create_in #c r in
  (**) let h2 = ST.get () in
  (**) assert (B.fresh_loc (c.state.footprint h2 block_state) h0 h2);
  (**) B.loc_unused_in_not_unused_in_disjoint h2;
  (**) B.(modifies_only_not_unused_in loc_none h1 h2);
  (**) c.key.frame_invariant B.loc_none k h1 h2;

  let k': optional_key c =
    match c.km with
    | Runtime ->
        let k' = key_create_in #c r in
        (**) let h3 = ST.get () in
        (**) B.loc_unused_in_not_unused_in_disjoint h3;
        (**) B.(modifies_only_not_unused_in loc_none h2 h3);
        (**) c.key.frame_invariant B.loc_none k h2 h3;
        (**) c.state.frame_invariant B.loc_none block_state h2 h3;
        (**) c.state.frame_freeable B.loc_none block_state h2 h3;
        (**) assert (B.fresh_loc (c.key.footprint h3 k') h0 h3);
        (**) assert (c.key.invariant h3 k');
        (**) assert (c.key.invariant h3 k);
        (**) assert B.(loc_disjoint (c.key.footprint h3 k) (c.key.footprint h3 k'));
        key_copy #c k k';
        (**) let h4 = ST.get () in
        (**) assert (B.fresh_loc (c.key.footprint h4 k') h0 h4);
        (**) B.loc_unused_in_not_unused_in_disjoint h4;
        (**) B.(modifies_only_not_unused_in loc_none h2 h4);
        (**) assert (c.key.invariant h4 k');
        (**) c.key.frame_invariant (c.key.footprint h3 k') k h3 h4;
        (**) c.state.frame_invariant (c.key.footprint h3 k') block_state h3 h4;
        (**) c.state.frame_freeable (c.key.footprint h3 k') block_state h3 h4;
        k'
    | Erased ->
        Block.coerce #_ #(optional_key c) (G.hide (c.key.v h0 k)) _
  in
  (**) let h5 = ST.get () in
  (**) assert (B.fresh_loc (optional_footprint h5 k') h0 h5);
  (**) assert (B.fresh_loc (c.state.footprint h5 block_state) h0 h5);

  [@inline_let] let total_len = Int.Cast.uint32_to_uint64 c.init_input_len in
  let s = State block_state buf total_len (G.hide S.empty) k' in
  (**) assert (B.fresh_loc (footprint_s c h5 s) h0 h5);

  (**) B.loc_unused_in_not_unused_in_disjoint h5;
  let p = B.malloc r s 1ul in
  (**) let h6 = ST.get () in
  (**) B.(modifies_only_not_unused_in loc_none h5 h6);
  (**) B.(modifies_only_not_unused_in loc_none h0 h6);
  (**) c.key.frame_invariant B.loc_none k h5 h6;
  (**) c.state.frame_invariant B.loc_none block_state h5 h6;
  (**) optional_frame B.loc_none k' h5 h6;
  (**) assert (B.fresh_loc (B.loc_addr_of_buffer p) h0 h6);
  (**) assert (B.fresh_loc (footprint_s c h6 s) h0 h6);
  (**) c.state.frame_freeable B.loc_none block_state h5 h6;
  (**) assert (optional_reveal h5 k' == optional_reveal h6 k');

  Block.init #c k buf block_state;
  (**) let h7 = ST.get () in
  (**) assert (B.fresh_loc (c.state.footprint h7 block_state) h0 h7);
  (**) assert (B.fresh_loc (B.loc_buffer buf) h0 h7);
  (**) optional_frame (B.loc_union (c.state.footprint h7 block_state) (B.loc_buffer buf)) k' h6 h7;
  (**) c.update_multi_zero (c.state.v h7 block_state) 0;
  (**) B.modifies_only_not_unused_in B.loc_none h0 h7;
  (**) assert (c.state.v h7 block_state == c.init_s (optional_reveal h6 k'));

  (**) let h8 = ST.get () in
  (**) assert (U64.v total_len <= U64.v c.max_input_len);

  (**) begin
  (**) let s = B.get h8 p 0 in
  (**) let key_v = key c h8 p in
  (**) let init_input = c.init_input_s key_v in
  (**) split_at_last_init c init_input;
  (**) assert(invariant_s c h8 s)
  (**) end;
  (**) assert (invariant c h8 p);

  (**) assert (seen c h8 p == S.empty);
  (**) assert B.(modifies loc_none h0 h8);
  (**) assert (B.fresh_loc (footprint c h8 p) h0 h8);
  (**) assert B.(loc_includes (loc_region_only true r) (footprint c h8 p));

  (**) assert (ST.equal_stack_domains h1 h8);
  (**) assert (ST.equal_stack_domains h0 h1);

  p
#pop-options

#push-options "--z3rlimit 100"
[@ Meta.Attribute.specialize ]
let copy #c s0 r =
  [@inline_let] let _ = c.state.invariant_loc_in_footprint in
  [@inline_let] let _ = c.key.invariant_loc_in_footprint in
  allow_inversion key_management;

  // All source state is suffixed by 0.
  let State block_state0 buf0 total_len0 seen0 k0 = !*s0 in

  (**) let h0 = ST.get () in

  (**) B.loc_unused_in_not_unused_in_disjoint h0;
  let buf = B.malloc r (Lib.IntTypes.u8 0) c.blocks_state_len in
  B.blit buf0 0ul buf 0ul c.blocks_state_len;
  (**) let h1 = ST.get () in
  (**) assert (B.fresh_loc (B.loc_buffer buf) h0 h1);
  (**) B.loc_unused_in_not_unused_in_disjoint h1;
  (**) B.(modifies_only_not_unused_in loc_none h0 h1);
  (**) if c.km = Runtime then
  (**)   c.key.frame_invariant B.loc_none k0 h0 h1;
  (**) c.state.frame_invariant B.loc_none block_state0 h0 h1;
  (**) assert (invariant c h1 s0);

  let block_state = state_create_in r in
  (**) let h2 = ST.get () in
  (**) assert (B.fresh_loc (c.state.footprint h2 block_state) h0 h2);
  (**) B.loc_unused_in_not_unused_in_disjoint h2;
  (**) B.(modifies_only_not_unused_in loc_none h1 h2);
  (**) if c.km = Runtime then
  (**)   c.key.frame_invariant B.loc_none k0 h1 h2;
  (**) c.state.frame_invariant B.loc_none block_state0 h0 h1;
  (**) assert (invariant c h2 s0);

  state_copy #c block_state0 block_state;
  (**) let h2 = ST.get () in
  (**) B.loc_unused_in_not_unused_in_disjoint h2;
  (**) B.(modifies_only_not_unused_in loc_none h1 h2);
  (**) if c.km = Runtime then
  (**)   c.key.frame_invariant (c.state.footprint h2 block_state) k0 h1 h2;

  let k': optional_key c =
    match c.km with
    | Runtime ->
        let k' = key_create_in #c r in
        (**) let h3 = ST.get () in
        (**) B.loc_unused_in_not_unused_in_disjoint h3;
        (**) B.(modifies_only_not_unused_in loc_none h2 h3);
        (**) c.key.frame_invariant B.loc_none k0 h2 h3;
        (**) c.state.frame_invariant B.loc_none block_state h2 h3;
        (**) c.state.frame_freeable B.loc_none block_state h2 h3;
        (**) assert (B.fresh_loc (c.key.footprint h3 k') h0 h3);
        (**) assert (c.key.invariant h3 k');
        (**) assert (c.key.invariant h3 k0);
        (**) assert B.(loc_disjoint (c.key.footprint h3 k0) (c.key.footprint h3 k'));
        key_copy #c k0 k';
        (**) let h4 = ST.get () in
        (**) assert (B.fresh_loc (c.key.footprint h4 k') h0 h4);
        (**) B.loc_unused_in_not_unused_in_disjoint h4;
        (**) B.(modifies_only_not_unused_in loc_none h2 h4);
        (**) assert (c.key.invariant h4 k');
        (**) c.key.frame_invariant (c.key.footprint h3 k') k0 h3 h4;
        (**) c.state.frame_invariant (c.key.footprint h3 k') block_state h3 h4;
        (**) c.state.frame_freeable (c.key.footprint h3 k') block_state h3 h4;
        k'
    | Erased -> k0
  in
  (**) let h5 = ST.get () in
  (**) assert (B.fresh_loc (optional_footprint h5 k') h0 h5);
  (**) assert (B.fresh_loc (c.state.footprint h5 block_state) h0 h5);

  let s = State block_state buf total_len0 seen0 k' in
  (**) assert (B.fresh_loc (footprint_s c h5 s) h0 h5);

  (**) B.loc_unused_in_not_unused_in_disjoint h5;
  let p = B.malloc r s 1ul in
  (**) let h6 = ST.get () in
  (**) B.(modifies_only_not_unused_in loc_none h5 h6);
  (**) B.(modifies_only_not_unused_in loc_none h0 h6);
  (**) if c.km = Runtime then
  (**)   c.key.frame_invariant B.loc_none k0 h5 h6;
  (**) c.state.frame_invariant B.loc_none block_state h5 h6;
  (**) optional_frame B.loc_none k' h5 h6;
  (**) assert (B.fresh_loc (B.loc_addr_of_buffer p) h0 h6);
  (**) assert (B.fresh_loc (footprint_s c h6 s) h0 h6);
  (**) c.state.frame_freeable B.loc_none block_state h5 h6;
  (**) assert (optional_reveal h5 k' == optional_reveal h6 k');

  p
#pop-options

#push-options "--z3rlimit 400"
[@ Meta.Attribute.specialize ]
let alloca #c k =
  [@inline_let] let _ = c.state.invariant_loc_in_footprint in
  [@inline_let] let _ = c.key.invariant_loc_in_footprint in
  allow_inversion key_management;

  (**) let h0 = ST.get () in

  (**) B.loc_unused_in_not_unused_in_disjoint h0;
  let buf = B.alloca (Lib.IntTypes.u8 0) c.blocks_state_len in
  (**) let h1 = ST.get () in
  (**) assert (B.fresh_loc (B.loc_buffer buf) h0 h1);
  (**) B.loc_unused_in_not_unused_in_disjoint h1;
  (**) B.(modifies_only_not_unused_in loc_none h0 h1);
  (**) c.key.frame_invariant B.loc_none k h0 h1;

  let block_state = state_alloca () in
  (**) let h2 = ST.get () in
  (**) assert (B.fresh_loc (c.state.footprint h2 block_state) h0 h2);
  (**) B.loc_unused_in_not_unused_in_disjoint h2;
  (**) B.(modifies_only_not_unused_in loc_none h1 h2);
  (**) c.key.frame_invariant B.loc_none k h1 h2;

  let k': optional_key c =
    match c.km with
    | Runtime ->
        let k' = key_alloca () in
        (**) let h3 = ST.get () in
        (**) B.loc_unused_in_not_unused_in_disjoint h3;
        (**) B.(modifies_only_not_unused_in loc_none h2 h3);
        (**) c.key.frame_invariant B.loc_none k h2 h3;
        (**) c.state.frame_invariant B.loc_none block_state h2 h3;
        (**) assert (B.fresh_loc (c.key.footprint h3 k') h0 h3);
        (**) assert (c.key.invariant h3 k');
        (**) assert (c.key.invariant h3 k);
        (**) assert B.(loc_disjoint (c.key.footprint h3 k) (c.key.footprint h3 k'));
        key_copy k k';
        (**) let h4 = ST.get () in
        (**) assert (B.fresh_loc (c.key.footprint h4 k') h0 h4);
        (**) B.loc_unused_in_not_unused_in_disjoint h4;
        (**) B.(modifies_only_not_unused_in loc_none h2 h4);
        (**) assert (c.key.invariant h4 k');
        (**) c.key.frame_invariant (c.key.footprint h3 k') k h3 h4;
        (**) c.state.frame_invariant (c.key.footprint h3 k') block_state h3 h4;
        k'
    | Erased ->
        Block.coerce #_ #(optional_key c) (G.hide (c.key.v h0 k)) _
  in
  (**) let h5 = ST.get () in
  (**) assert (B.fresh_loc (optional_footprint h5 k') h0 h5);
  (**) assert (B.fresh_loc (c.state.footprint h5 block_state) h0 h5);

  [@inline_let] let total_len = Int.Cast.uint32_to_uint64 c.init_input_len in
  let s = State block_state buf total_len (G.hide S.empty) k' in
  (**) assert (B.fresh_loc (footprint_s c h5 s) h0 h5);

  (**) B.loc_unused_in_not_unused_in_disjoint h5;
  let p = B.alloca s 1ul in
  (**) let h6 = ST.get () in
  (**) B.(modifies_only_not_unused_in loc_none h5 h6);
  (**) B.(modifies_only_not_unused_in loc_none h0 h6);
  (**) c.key.frame_invariant B.loc_none k h5 h6;
  (**) c.state.frame_invariant B.loc_none block_state h5 h6;
  (**) optional_frame B.loc_none k' h5 h6;
  (**) assert (B.fresh_loc (B.loc_addr_of_buffer p) h0 h6);
  (**) assert (B.fresh_loc (footprint_s c h6 s) h0 h6);
  (**) assert (optional_reveal h5 k' == optional_reveal h6 k');

  init #c k buf block_state;
  (**) let h7 = ST.get () in
  (**) assert (B.fresh_loc (c.state.footprint h7 block_state) h0 h7);
  (**) assert (B.fresh_loc (B.loc_buffer buf) h0 h7);
  (**) optional_frame (B.loc_union (c.state.footprint h7 block_state) (B.loc_buffer buf)) k' h6 h7;
  (**) c.update_multi_zero (c.state.v h7 block_state) 0;
  (**) B.modifies_only_not_unused_in B.loc_none h0 h7;
  (**) assert (c.state.v h7 block_state == c.init_s (optional_reveal h6 k'));

  (**) let h8 = ST.get () in
  (**) assert (U64.v total_len <= U64.v c.max_input_len);
  (**) begin
  (**) let key_v = key c h8 p in
  (**) let init_input = c.init_input_s key_v in
  (**) split_at_last_init c init_input;
  (**) assert(invariant_s c h8 s)
  (**) end;
  (**) assert (invariant c h8 p);
  (**) assert (seen c h8 p == S.empty);
  (**) assert B.(modifies loc_none h0 h8);
  (**) assert (B.fresh_loc (footprint c h8 p) h0 h8);
  (**) assert B.(loc_includes (loc_region_only true (HS.get_tip h8)) (footprint c h8 p));
  (**) assert(ST.same_refs_in_non_tip_regions h0 h8);

  p
#pop-options

#push-options "--z3cliopt smt.arith.nl=false"
[@ Meta.Attribute.specialize ]
let init #c k s =
  [@inline_let] let _ = c.state.invariant_loc_in_footprint in
  [@inline_let] let _ = c.key.invariant_loc_in_footprint in
  allow_inversion key_management;

  let open LowStar.BufferOps in
  (**) let h1 = ST.get () in
  let State block_state buf _ _ k' = !*s in
  [@inline_let]
  let block_state: c.state.s = block_state in

  init #c k buf block_state;

  (**) let h2 = ST.get () in
  (**) optional_frame #c (B.loc_union (c.state.footprint h1 block_state) (B.loc_buffer buf)) k' h1 h2;
  (**) c.key.frame_invariant (B.loc_union (c.state.footprint h1 block_state) (B.loc_buffer buf)) k h1 h2;
  (**) Math.Lemmas.modulo_lemma 0 (U32.v c.block_len);
  (**) assert(0 % UInt32.v c.block_len = 0);
  (**) assert (key c h1 s == key c h2 s);
  (**) c.update_multi_zero (c.state.v h2 block_state) 0;

  let k': optional_key c =
    match c.km with
    | Runtime ->
        key_copy k k';
        (**) let h4 = ST.get () in
        (**) assert (c.key.invariant h4 k');
        (**) c.key.frame_invariant (c.key.footprint h2 k') k h2 h4;
        (**) c.state.frame_invariant (c.key.footprint h2 k') block_state h2 h4;
        (**) stateful_frame_preserves_freeable (c.key.footprint h2 k') block_state h2 h4;
        k'
    | Erased ->
        Block.coerce #_ #(optional_key c) (G.hide (c.key.v h1 k)) _
  in
  (**) let h2 = ST.get () in
  (**) assert(preserves_freeable c s h1 h2);

  [@inline_let] let total_len = Int.Cast.uint32_to_uint64 c.init_input_len in
  let tmp: state_s' c = State block_state buf total_len (G.hide S.empty) k' in
  B.upd s 0ul tmp;
  (**) let h3 = ST.get () in
  (**) c.state.frame_invariant B.(loc_buffer s) block_state h2 h3;
  (**) c.key.frame_invariant B.(loc_buffer s) k h2 h3;
  (**) optional_frame #c B.(loc_buffer s) k' h2 h3;
  (**) stateful_frame_preserves_freeable B.(loc_buffer s) block_state h2 h3;
  (**) assert(preserves_freeable c s h2 h3);

  // This seems to cause insurmountable difficulties. Puzzled.
  ST.lemma_equal_domains_trans h1 h2 h3;

  // AR: 07/22: same old `Seq.equal` and `==` story
  (**) assert (Seq.equal (seen c h3 s) Seq.empty);

  (**) assert (footprint c h1 s == footprint c h3 s);
  (**) assert (B.(modifies (footprint c h1 s) h1 h3));
  (**) assert (U64.v total_len <= U64.v c.max_input_len);
  (**) begin
  (**) let key_v = key c h3 s in
  (**) let all_seen_ = all_seen c h3 s in
  // SH (11/22): the proof fails if we don't introduce the call to [split_at_last]
  (**) let blocks, rest = split_at_last c all_seen_ in
  (**) let init_input = c.init_input_s key_v in
  (**) split_at_last_init c init_input;
  (**) assert (invariant_s c h3 (B.get h3 s 0))
  (**) end;

  (**) assert(preserves_freeable c s h1 h3)
#pop-options

/// Some helpers to minimize modulo-reasoning
/// =========================================

val split_at_last_num_blocks_lem (c: index) (b: nat):
  Lemma (
    let n_blocks = split_at_last_num_blocks c b in
    let blocks = n_blocks * U32.v c.blocks_state_len in
    0 <= blocks /\ blocks <= b)

let split_at_last_num_blocks_lem c b = ()

/// The ``rest`` function below allows computing, based ``total_len`` stored in
/// the state, the length of useful data currently stored in ``buf``.
/// Unsurprisingly, there's a fair amount of modulo reasoning here because of
/// 64-bit-to-32-bit conversions, so we do them once and for all in a helper.
#push-options "--z3cliopt smt.arith.nl=false"
inline_for_extraction noextract
let rest (c: index)
  (total_len: UInt64.t): (x:UInt32.t {
    let n = split_at_last_num_blocks c (U64.v total_len) in
    let l = U32.v c.blocks_state_len in
    0 <= n * l /\ n * l <= U64.v total_len /\
    U32.v x = U64.v total_len - (n * l)})
=
  let open FStar.Int.Cast in
  [@inline_let] let l = uint32_to_uint64 c.blocks_state_len in
  [@inline_let] let r = total_len `U64.rem` l in
  (**) let total_len_v : Ghost.erased nat = U64.v total_len in
  (**) let l_v : Ghost.erased nat = U64.v l in
  (**) let r_v : Ghost.erased nat = U64.v r in
  (**) assert(Ghost.reveal r_v = total_len_v - ((total_len_v / l_v) * l_v));
  (**) Math.Lemmas.euclidean_division_definition total_len_v l_v;
  (**) assert(Ghost.reveal r_v = total_len_v % l_v);
  (**) assert(r_v < l_v);

  if U64.(r =^ uint_to_t 0) && U64.(total_len >^ uint_to_t 0) then
    begin
    (**) split_at_last_num_blocks_lem c (U64.v total_len);
    c.blocks_state_len
    end
  else
    begin
    [@inline_let] let r' = FStar.Int.Cast.uint64_to_uint32 r in
    (**) FStar.Math.Lemmas.small_modulo_lemma_1 (U64.v r) (pow2 32);
    (**) calc (==) {
    (**)   U32.v r';
    (**) (==) { }
    (**)   U64.v r % pow2 32;
    (**) (==) { FStar.Math.Lemmas.small_modulo_lemma_1 (U64.v r) (pow2 32) }
    (**)   U64.v r;
    (**) (==) { FStar.Math.Lemmas.euclidean_division_definition (U64.v total_len) (U64.v (uint32_to_uint64 c.blocks_state_len)) }
    (**)   U64.v total_len % U64.v (uint32_to_uint64 c.blocks_state_len );
    (**) (==) { }
    (**)   U64.v total_len % U32.v c.blocks_state_len;
    (**) };
    (**) assert(
    (**)   let n = split_at_last_num_blocks c (U64.v total_len) in
    (**)   let l = U32.v c.blocks_state_len in
    (**)    U32.v r' = U64.v total_len - (n * l));
    r'
    end
#pop-options


/// The ``nblocks`` function below allows computing, given ``total_len`` stored in
/// the state, the number of blocks of data which have been processed (the remaining
/// unprocessed data being left in ``buf``).
#push-options "--z3cliopt smt.arith.nl=false"
inline_for_extraction noextract
let nblocks (c: index)
  (len: UInt32.t): (x:UInt32.t {
    let l = U32.v (c.blocks_state_len) in
    U32.v x * l <= U32.v len /\
    U32.v x = split_at_last_num_blocks c (U32.v len) })
=
  let open FStar.Int.Cast in
  [@inline_let] let l = c.blocks_state_len in
  [@inline_let] let r = rest c (uint32_to_uint64 len) in
  (**) let len_v : Ghost.erased nat = U32.v len in
  (**) let l_v : Ghost.erased nat = U32.v l in
  (**) let r_v : Ghost.erased nat = U32.v r in
  (**) let n_s : Ghost.erased nat = split_at_last_num_blocks c len_v in
  (**) assert(Ghost.reveal len_v = n_s * l_v + r_v);
  (**) Math.Lemmas.nat_times_nat_is_nat n_s l_v;
  (**) assert(U32.v r <= U32.v len);
  [@inline_let] let blocks = len `U32.sub` r in
  (**) let blocks_v : Ghost.erased nat = U32.v blocks in
  (**) assert(blocks_v % l_v = 0);
  [@inline_let] let n = blocks `U32.div` l in
  (**) let n_v : Ghost.erased nat = U32.v n in
  (**) assert(n_v * l_v = Ghost.reveal blocks_v);
  (**) split_at_last_num_blocks_spec c len_v n_v r_v;
  n
#pop-options

/// The ``rest`` function to call on the unprocessed data length in the ``finish``
/// function.
#push-options "--z3cliopt smt.arith.nl=false"
inline_for_extraction noextract
let rest_finish (c: index)
  (len: UInt32.t): (x:UInt32.t {
    let l = U32.v (c.block_len) in
    let n = fst (Lib.UpdateMulti.split_at_last_lazy_nb_rem l (U32.v len)) in
    0 <= n * l /\ n * l <= U32.v len /\
    U32.v x = U32.v len - (n * l)})
=
  [@inline_let] let l = c.block_len in
  [@inline_let] let r = len `U32.rem` l in
  (**) split_at_last_num_blocks_lem c (U32.v len);
  if U32.(r =^ uint_to_t 0) && U32.(len >^ uint_to_t 0) then
    begin
    (**) begin
    (**) let l = U32.v (c.block_len) in
    (**) let n = fst (Lib.UpdateMulti.split_at_last_lazy_nb_rem l (U32.v len)) in
    (**) Math.Lemmas.nat_times_nat_is_nat n l
    (**) end;
    c.block_len
    end
  else
    r
#pop-options

/// We always add 32-bit lengths to 64-bit lengths. Having a helper for that allows
/// doing modulo reasoning once and for all.
inline_for_extraction noextract
let add_len (c: index) (total_len: UInt64.t) (len: UInt32.t):
  Pure UInt64.t
    (requires U64.v total_len + U32.v len <= U64.v (c.max_input_len))
    (ensures fun x -> U64.v x = U64.v total_len + U32.v len /\ U64.v x <= U64.v (c.max_input_len))
=
  total_len `U64.add` Int.Cast.uint32_to_uint64 len

#push-options "--z3cliopt smt.arith.nl=false"
inline_for_extraction noextract
let add_len_small (c: index) (total_len: UInt64.t) (len: UInt32.t): Lemma
  (requires
    U32.v len <= U32.v (c.blocks_state_len) - U32.v (rest c total_len) /\
    U64.v total_len + U32.v len <= U64.v (c.max_input_len))
  (ensures (rest c (add_len c total_len len) = rest c total_len `U32.add` len))
=
  let total_len_v = U64.v total_len in
  let l = U32.v (c.blocks_state_len) in
  let b = total_len_v + U32.v len in
  let n = split_at_last_num_blocks c total_len_v in
  let r = U32.v (rest c total_len) in
  assert(total_len_v = n * l + r);
  let r' = U32.v (rest c total_len) + U32.v len in
  assert(r' <= l);
  assert(r' = 0 ==> b = 0);
  Math.Lemmas.euclidean_division_definition b l;
  assert(b = n * l + r');
  split_at_last_num_blocks_spec c b n r'
#pop-options


/// Beginning of the three sub-cases (see Hacl.Streaming.Spec)
/// ==========================================================

noextract
let total_len_h (c: index) h (p: state' c) =
  State?.total_len (B.deref h p)

noextract
let split_at_last_all_seen (c: index) h (p: state' c) =
  let all_seen = all_seen c h p in
  let blocks, rest = split_at_last c all_seen in
  blocks, rest

inline_for_extraction noextract
[@ Meta.Attribute.inline_ ]
val update_small:
  #c:index -> (
  s:state' c ->
  data: B.buffer uint8 ->
  len: UInt32.t ->
  Stack unit
    (requires fun h0 ->
      update_pre c s data len h0 /\
      U32.v (c.init_input_len) + S.length (seen c h0 s) + U32.v len <= U64.v (c.max_input_len) /\
      U32.v len <= U32.v (c.blocks_state_len) - U32.v (rest c (total_len_h c h0 s)))
    (ensures fun h0 s' h1 ->
      update_post c s data len h0 h1))

/// SH: The proof obligations for update_small have problem succeeding in command
/// line mode: hence the restart-solver instruction, the crazy rlimit and the
/// intermediate lemma. Interestingly (and frustratingly), the proof succeeds
/// quite quickly locally on command-line with this rlimit, but fails with a lower
/// one. Besides, the lemma is needed only for the CI regression.
let split_at_last_rest_eq (c: index)
                          (s: state' c) (h0: HS.mem) :
  Lemma
  (requires (
    invariant c h0 s))
  (ensures (
    let s = B.get h0 s 0 in
    let State block_state buf total_len seen_ k' = s in
    let key_v = optional_reveal #c h0 k' in
    let all_seen = S.append (c.init_input_s key_v) seen_ in
    let _, r = split_at_last c all_seen in
    let sz = rest c total_len in
    Seq.length r == U32.v sz)) =
  let s = B.get h0 s 0 in
  let State block_state buf total_len seen_ k' = s in
  let key_v = optional_reveal #c h0 k' in
  let all_seen = S.append (c.init_input_s key_v) seen_ in
  let _, r = split_at_last c all_seen in
  let sz = rest c total_len in
  ()

/// Particularly difficult proof. Z3 profiling indicates that a pattern goes off
/// the rails. So I disabled all of the known "bad" patterns, then did the proof
/// by hand. Fortunately, there were only two stateful operations. The idea was
/// to do all ofthe modifies-reasoning in the two lemmas above, then disable the
/// bad pattern for the main function.
///
/// This style is a little tedious, because it requires a little bit of digging
/// to understand what needs to hold in order to be able to prove that e.g. the
/// sequence remains unmodified from h0 to h2, but this seems more robust?
val modifies_footprint:
  (c: index) ->
  s:state' c ->
  data: B.buffer uint8 ->
  len: UInt32.t ->
  h0: HS.mem ->
  h1: HS.mem ->
  Lemma
    (requires (
      let State _ buf_ _ _ _ = B.deref h0 s in (
      update_pre c s data len h0 /\
      B.(modifies (loc_buffer buf_) h0 h1))))
    (ensures (
      let State bs0 buf0 _ _ k0 = B.deref h0 s in
      let State bs1 buf1 _ _ k1 = B.deref h1 s in (
      footprint c h0 s == footprint c h1 s /\
      preserves_freeable c s h0 h1 /\
      bs0 == bs1 /\ buf0 == buf1 /\ k0 == k1 /\
      c.state.invariant h1 bs1 /\
      c.state.v h1 bs1 == c.state.v h0 bs0 /\
      c.state.footprint h1 bs1 == c.state.footprint h0 bs0 /\
      B.(loc_disjoint (loc_addr_of_buffer s) (loc_buffer buf1)) /\
      B.(loc_disjoint (loc_addr_of_buffer s) (loc_buffer data)) /\
      B.(loc_disjoint (loc_addr_of_buffer s) (loc_addr_of_buffer buf1)) /\
      B.(loc_disjoint (loc_addr_of_buffer s) (c.state.footprint h1 bs1)) /\
      B.(loc_disjoint (loc_buffer s) (loc_buffer buf1)) /\
      B.(loc_disjoint (loc_buffer s) (loc_buffer data)) /\
      B.(loc_disjoint (loc_buffer s) (c.state.footprint h1 bs1)) /\
      (if c.km = Runtime then
        c.key.invariant h1 k1 /\
        c.key.v h1 k1 == c.key.v h0 k0 /\
        c.key.footprint h1 k1 == c.key.footprint h0 k0 /\
        B.(loc_disjoint (loc_addr_of_buffer s) (c.key.footprint h1 k1)) /\
        B.(loc_disjoint (loc_buffer s) (c.key.footprint h1 k1))
      else
        B.(loc_disjoint (loc_addr_of_buffer s) loc_none) /\
        True))))

let modifies_footprint c p data len h0 h1 =
  let _ = c.state.frame_freeable in
  let _ = c.key.frame_freeable in
  let s0 = B.deref h0 p in
  let s1 = B.deref h0 p in
  let State bs0 buf0 _ _ k0 = s0 in
  let State bs1 buf0 _ _ k1 = s1 in
  c.state.frame_invariant (B.loc_buffer buf0) bs0 h0 h1;
  if c.km = Runtime then
    c.key.frame_invariant (B.loc_buffer buf0) k0 h0 h1

val modifies_footprint':
  c: index ->
  p:state' c ->
  data: B.buffer uint8 ->
  len: UInt32.t ->
  h0: HS.mem ->
  h1: HS.mem ->
  Lemma
    (requires (
      let State bs0 buf0 _ _ k0 = B.deref h0 p in
      let State bs1 buf1 _ _ k1 = B.deref h1 p in (
      B.live h0 p /\
      B.(loc_disjoint (loc_addr_of_buffer p) (c.state.footprint h0 bs0)) /\
      B.(loc_disjoint (loc_addr_of_buffer p) (loc_addr_of_buffer buf0)) /\
      c.state.invariant h0 bs0 /\
      (if c.km = Runtime then
        B.(loc_disjoint (loc_addr_of_buffer p) (c.key.footprint h0 k0)) /\
        c.key.invariant h0 k0
      else
        B.(loc_disjoint (loc_addr_of_buffer p) loc_none)) /\
      B.(modifies (loc_buffer p) h0 h1)) /\
      bs0 == bs1 /\ buf0 == buf1 /\ k0 == k1))
    (ensures (
      let State bs0 buf0 _ _ k0 = B.deref h0 p in
      let State bs1 buf1 _ _ k1 = B.deref h1 p in (
      B.live h1 p /\
      footprint c h0 p == footprint c h1 p /\
      preserves_freeable c p h0 h1 /\
      B.(loc_disjoint (loc_addr_of_buffer p) (footprint_s c h1 (B.deref h1 p))) /\
      B.(loc_disjoint (loc_addr_of_buffer p) (c.state.footprint h1 bs1)) /\
      B.(loc_disjoint (loc_buffer p) (c.state.footprint h1 bs1)) /\
      c.state.invariant h1 bs1 /\
      c.state.v h1 bs1 == c.state.v h0 bs0 /\
      c.state.footprint h1 bs1 == c.state.footprint h0 bs0 /\
      (if c.km = Runtime then
        c.key.invariant h1 k1 /\
        c.key.v h1 k1 == c.key.v h0 k0 /\
        c.key.footprint h1 k1 == c.key.footprint h0 k0 /\
        B.(loc_disjoint (loc_addr_of_buffer p) (c.key.footprint h1 k1)) /\
        B.(loc_disjoint (loc_buffer p) (c.key.footprint h1 k1))
      else
        B.(loc_disjoint (loc_addr_of_buffer p) loc_none)))))

let modifies_footprint' c p data len h0 h1 =
  let _ = c.state.frame_freeable in
  let _ = c.key.frame_freeable in
  let _ = c.state.frame_invariant in
  let _ = c.key.frame_invariant in
  let _ = allow_inversion key_management in
  let s0 = B.deref h0 p in
  let s1 = B.deref h0 p in
  let State bs0 buf0 _ _ k0 = s0 in
  let State bs1 buf1 _ _ k1 = s1 in
  c.state.frame_invariant (B.loc_addr_of_buffer p) bs0 h0 h1;
  if c.km = Runtime then
    c.key.frame_invariant (B.loc_addr_of_buffer p) k0 h0 h1

/// Small helper which we use to factor out functional correctness proof obligations.
/// It states that a state was correctly updated to process some data between two
/// memory snapshots (the key is the same, the seen data was updated, etc.).
///
/// Note that we don't specify anything about the buffer and the block_state: they
/// might have been updated differently depending on the case.
unfold val state_is_updated :
  (c: index) ->
  s:state' c ->
  data: B.buffer uint8 ->
  len: UInt32.t ->
  h0: HS.mem ->
  h1: HS.mem ->
  Type0

#push-options "--z3cliopt smt.arith.nl=false"
let state_is_updated c p data len h0 h1 =
  // Functional conditions about the memory updates
  let s0 = B.get h0 p 0 in
  let s1 = B.get h1 p 0 in
  let State block_state0 buf0 total_len0 seen0 key0 = s0 in
  let State block_state1 buf1 total_len1 seen1 key1 = s1 in

  block_state1 == block_state0 /\
  buf1 == buf0 /\
  U64.v total_len1 == U64.v total_len0 + U32.v len /\
  key1 == key0 /\

  seen1 `S.equal` (seen0 `S.append` (B.as_seq h0 data)) /\

  optional_reveal #c h1 key1 == optional_reveal #c h0 key0
#pop-options

/// The functional part of the invariant
unfold val invariant_s_funct :
  (c: index) ->
  s:state' c ->
  data: B.buffer uint8 ->
  len: UInt32.t ->
  h0: HS.mem ->
  h1: HS.mem ->
  Pure Type0 (requires
    update_pre c s data len h0 /\
    U32.v (c.init_input_len) + S.length (seen c h0 s) + U32.v len <= U64.v (c.max_input_len) /\
    state_is_updated c s data len h0 h1)
  (ensures (fun _ -> True))

let invariant_s_funct c p data len h0 h1 =
  let blocks, rest = split_at_last_all_seen c h1 p in
  let s = B.get h1 p 0 in
  let State block_state buf_ total_len seen key = s in
  let key_v = optional_reveal #c h0 key in
  let init_s = c.init_s key_v in
  (**) Math.Lemmas.modulo_lemma 0 (U32.v (c.block_len));
  c.state.v h1 block_state == c.update_multi_s init_s 0 blocks /\
  S.equal (S.slice (B.as_seq h1 buf_) 0 (Seq.length rest)) rest


/// We isolate the functional correctness proof obligations for [update_small]
val update_small_functional_correctness :
  (c: index) ->
  s:state' c ->
  data: B.buffer uint8 ->
  len: UInt32.t ->
  h0: HS.mem ->
  h1: HS.mem ->
  Lemma
  (requires (
      // The precondition of [small_update]
      update_pre c s data len h0 /\
      U32.v (c.init_input_len) + S.length (seen c h0 s) + U32.v len <= U64.v (c.max_input_len) /\
      U32.v len <= U32.v (c.blocks_state_len) - U32.v (rest c (total_len_h c h0 s)) /\

      // Generic conditions
      state_is_updated c s data len h0 h1 /\

      // Functional conditions about the memory updates
      begin
      let s0 = B.get h0 s 0 in
      let s1 = B.get h1 s 0 in
      let State block_state0 buf0 total_len0 seen0 key0 = s0 in
      let State block_state1 buf1 total_len1 seen1 key1 = s1 in

      let sz = rest c total_len0 in
      let buf = buf0 in
      let data_v0 = B.as_seq h0 data in
      let buf_beg_v0 = S.slice (B.as_seq h0 buf) 0 (U32.v sz) in
      let buf_part_v1 = S.slice (B.as_seq h1 buf) 0 (U32.v sz + U32.v len) in

      buf_part_v1 == S.append buf_beg_v0 data_v0 /\
      c.state.v h1 block_state1 == c.state.v h0 block_state0
      end
  ))
  (ensures (invariant_s_funct c s data len h0 h1))

#push-options "--z3cliopt smt.arith.nl=false"
let update_small_functional_correctness c p data len h0 h1 =
  let s0 = B.get h0 p 0 in
  let s1 = B.get h1 p 0 in

  let State block_state buf total_len0 seen0 key = s0 in
  let seen0 = G.reveal seen0 in
  let key_v0 = optional_reveal #c h0 key in
  let init_v0 = c.init_input_s key_v0 in
  let all_seen0 = S.append init_v0 seen0 in
  let blocks0, rest0 = split_at_last c all_seen0 in

  let State block_state buf total_len1 seen1 key = s1 in
  let seen1 = G.reveal seen1 in
  let key_v1 = optional_reveal #c h1 key in
  assert(key_v1 == key_v0);
  let init_v1 = c.init_input_s key_v1 in
  assert(init_v1 == init_v0);
  let all_seen1 = S.append init_v1 seen1 in
  let blocks1, rest1 = split_at_last c all_seen1 in

  (**) Math.Lemmas.modulo_lemma 0 (U32.v c.block_len);
  (**) assert(0 % U32.v c.block_len = 0);
  (**) Math.Lemmas.modulo_lemma 0 (U32.v c.blocks_state_len);
  (**) assert(0 % U32.v c.blocks_state_len = 0);

  let data_v0 = B.as_seq h0 data in

  split_at_last_small c all_seen0 data_v0;

  // The first problematic condition
  assert(blocks1 `S.equal` blocks0);
  assert(c.state.v h1 block_state == c.update_multi_s (c.init_s key_v1) 0 blocks1);

  // The second problematic condition
  assert(S.equal (S.slice (B.as_seq h1 buf) 0 (Seq.length rest1)) rest1)
#pop-options

// The absence of loc_disjoint_includes makes reasoning a little more difficult.
// Notably, we lose all of the important disjointness properties between the
// outer point p and the buffer within B.deref h p. These need to be
// re-established by hand. Another thing that we lose without this pattern is
// knowing that loc_buffer b is included within loc_addr_of_buffer b. This is
// important for reasoning about the preservation of e.g. the contents of data.
#restart-solver
#push-options "--z3rlimit 300 --z3cliopt smt.arith.nl=false --z3refresh \
  --using_facts_from '*,-LowStar.Monotonic.Buffer.unused_in_not_unused_in_disjoint_2,-FStar.Seq.Properties.slice_slice,-LowStar.Monotonic.Buffer.loc_disjoint_includes_r'"
let update_small #c p data len =
  let open LowStar.BufferOps in
  let s = !*p in
  let State block_state buf total_len seen_ k' = s in
  [@inline_let]
  let block_state: c.state.s = block_state in

  // Functional reasoning.
  let sz = rest c total_len in
  add_len_small c total_len len;

  let h0 = ST.get () in
  let buf1 = B.sub buf 0ul sz in
  let buf2 = B.sub buf sz len in

  // Memory reasoning.
  c.state.invariant_loc_in_footprint h0 block_state;
  if c.km = Runtime then
    c.key.invariant_loc_in_footprint h0 k';
//  key_invariant_loc_in_footprint #index c h0 p;
  B.(loc_disjoint_includes_r (loc_buffer data) (footprint c h0 p) (loc_buffer buf2));

  // FIRST STATEFUL OPERATION
  B.blit data 0ul buf2 0ul len;

  // Memory reasoning.
  let h1 = ST.get () in
  modifies_footprint c p data len h0 h1;
  c.state.invariant_loc_in_footprint h1 block_state;
  if c.km = Runtime then
    c.key.invariant_loc_in_footprint h1 k';

  // Functional reasoning on data
  begin
  let buf1_v0 = B.as_seq h0 buf1 in
  let buf1_v1 = B.as_seq h1 buf1 in
  let buf2_v1 = B.as_seq h1 buf2 in
  let buf_beg_v0 = S.slice (B.as_seq h0 buf) 0 (U32.v sz) in
  let buf_part_v1 = S.slice (B.as_seq h1 buf) 0 (U32.v sz + U32.v len) in
  let data_v0 = B.as_seq h0 data in
  assert(buf1_v1 == buf1_v0);
  assert(buf1_v0 == buf_beg_v0);
  assert(buf2_v1 `S.equal` data_v0);
  assert(buf_part_v1 `S.equal` S.append buf_beg_v0 data_v0)
  end;

  // SECOND STATEFUL OPERATION
  let total_len = add_len c total_len len in
  [@inline_let]
  let tmp: state_s' c =
    State #c block_state buf total_len
          (G.hide (G.reveal seen_ `S.append` (B.as_seq h0 data))) k'
  in
  p *= tmp;

  // Memory reasoning.
  let h2 = ST.get () in
  modifies_footprint' c p data len h1 h2;
  c.state.invariant_loc_in_footprint h2 block_state;
  if c.km = Runtime then
    c.key.invariant_loc_in_footprint h2 k';
  ST.lemma_equal_domains_trans h0 h1 h2;

  // Prove the invariant
  update_small_functional_correctness c p data len h0 h2

#pop-options

// Stupid name collisions
noextract let seen_h = seen
noextract let all_seen_h = all_seen

/// Case 2: we have no buffered data (ie: the buffer was just initialized), or the
/// internal buffer is full meaning that we can just hash it to go to the case where
/// there is no buffered data. Of course, the data we append has to be non-empty,
/// otherwise we might end-up with an empty internal buffer.

/// Auxiliary lemma which groups the functional correctness proof obligations
/// for [update_empty_or_full].
#push-options "--z3cliopt smt.arith.nl=false"
val update_empty_or_full_functional_correctness :
  c:index ->
  s:state' c ->
  data: B.buffer Lib.IntTypes.uint8 ->
  len: UInt32.t ->
  h0: HS.mem ->
  h1: HS.mem ->
  Lemma
  (requires (

    // Same precondition as [update_empty_or_full_buf]
    update_pre c s data len h0 /\
    U32.v (c.init_input_len) + S.length (seen c h0 s) + U32.v len <= U64.v (c.max_input_len) /\
    (rest c (total_len_h c h0 s) = 0ul \/
     rest c (total_len_h c h0 s) = c.blocks_state_len) /\
    U32.v len > 0 /\

    // Generic additional preconditions
    state_is_updated c s data len h0 h1 /\

    // Additional preconditions
    begin
    let s0 = B.get h0 s 0 in
    let s1 = B.get h1 s 0 in
    let State block_state0 buf0 total_len0 seen0 key0 = s0 in
    let State block_state1 buf1 total_len1 seen1 key1 = s1 in
    let seen0 = G.reveal seen0 in
    let seen1 = G.reveal seen1 in

    let block_state = block_state0 in
    let buf = buf0 in

    let n_blocks = nblocks c len in
    (**) split_at_last_num_blocks_lem c (U32.v len);
    (**) assert(U32.v n_blocks * U32.v (c.blocks_state_len) <= U32.v len);
    (**) assert(U32.(FStar.UInt.size (v n_blocks * v (c.blocks_state_len)) n));
    let data1_len = n_blocks `U32.mul` c.blocks_state_len in
    let data2_len = len `U32.sub` data1_len in
    let data1 = B.gsub data 0ul data1_len in
    let data2 = B.gsub data data1_len data2_len in

    let all_seen0 = all_seen c h0 s in
    let all_seen1 = all_seen c h1 s in
    let blocks0, res0 = split_at_last c all_seen0 in
    let blocks1, res1 = split_at_last c all_seen1 in

    let data1_v = B.as_seq h0 data1 in
    let data2_v = B.as_seq h0 data2 in
    let key = optional_reveal #c h0 key0 in
    let init_s = c.init_s key in
    let all_seen_data1 = S.append all_seen0 data1_v in

    (**) Math.Lemmas.modulo_lemma 0 (U32.v (c.block_len));

    S.length all_seen0 % U32.v (c.block_len) = 0 /\ // TODO: should be proved automatically
    S.length all_seen_data1 % U32.v (c.block_len) = 0 /\ // TODO: should be proved automatically

    c.state.v h1 block_state == c.update_multi_s init_s 0 all_seen_data1 /\
    S.slice (B.as_seq h1 buf) 0 (Seq.length data2_v) `S.equal` data2_v /\
    True
    end /\
    True
      ))
  (ensures (invariant_s_funct c s data len h0 h1))
#pop-options

#push-options "--z3cliopt smt.arith.nl=false"
let update_empty_or_full_functional_correctness c p data len h0 h1 =
  let s = B.get h0 p 0 in
  let State block_state buf_ total_len seen0 key = s in
  let init_s = c.init_s (optional_reveal #c h0 key) in
  Math.Lemmas.modulo_lemma 0 (U32.v (c.block_len));

  let n_blocks = nblocks c len in
  (**) split_at_last_num_blocks_lem c (U32.v len);
  (**) assert(U32.(FStar.UInt.size (v n_blocks * v (c.blocks_state_len)) n));
  let data1_len = n_blocks `U32.mul` c.blocks_state_len in
  let data2_len = len `U32.sub` data1_len in
  let data1 = B.gsub data 0ul data1_len in
  let data2 = B.gsub data data1_len data2_len in

  let data_v = B.as_seq h0 data in

  let init_input = init_input c h0 p in
  let seen1 = seen c h1 p in
  let all_seen0 = all_seen c h0 p in
  let all_seen1 = all_seen c h1 p in
  let blocks0, rest0 = split_at_last_all_seen c h0 p in
  let blocks1, rest1 = split_at_last_all_seen c h1 p in
  let data_blocks, data_rest = split_at_last c data_v in

  split_at_last_blocks c all_seen0 data_v;
  assert(Seq.equal all_seen1 (S.append all_seen0 data_v));

  assert(S.equal blocks1 (S.append all_seen0 data_blocks));
  assert(S.equal data_rest rest1)
#pop-options

inline_for_extraction noextract
[@ Meta.Attribute.inline_ ]
val update_empty_or_full_buf:
  #c:index ->
  s:state' c ->
  data: B.buffer Lib.IntTypes.uint8 ->
  len: UInt32.t ->
  Stack unit
    (requires fun h0 ->
      update_pre c s data len h0 /\
      U32.v (c.init_input_len) + S.length (seen c h0 s) + U32.v len <= U64.v (c.max_input_len) /\
      (rest c (total_len_h c h0 s) = 0ul \/
       rest c (total_len_h c h0 s) = c.blocks_state_len) /\
       U32.v len > 0)
    (ensures fun h0 s' h1 ->
      update_post c s data len h0 h1)

#push-options "--z3cliopt smt.arith.nl=false --z3rlimit 200"
let update_empty_or_full_buf #c p data len =
  [@inline_let] let _ = c.state.invariant_loc_in_footprint in
  [@inline_let] let _ = c.key.invariant_loc_in_footprint in
  [@inline_let] let _ = c.update_multi_associative in

  let open LowStar.BufferOps in
  let s = !*p in
  let State block_state buf total_len seen k' = s in
  [@inline_let]
  let block_state: c.state.s = block_state in
  let sz = rest c total_len in
  let h0 = ST.get () in

  Math.Lemmas.modulo_lemma 0 (U32.v (c.block_len));
  assert(0 % U32.v (c.block_len) = 0);

  let init_key : Ghost.erased _ = optional_reveal h0 (k' <: optional_key c) in
  let init_state : Ghost.erased _ = c.init_s init_key in

  assert(
    let all_seen = all_seen c h0 p in
    let blocks, rest = split_at_last c all_seen in
    Seq.length rest = U32.v sz /\
    c.state.v h0 block_state ==
    c.update_multi_s init_state 0 blocks);

  (* Start by "flushing" the buffer: hash it so that all the data seen so far
   * has been processed and we can consider the buffer as empty *)
  if U32.(sz =^ 0ul) then
    begin
    assert(
      let all_seen = all_seen c h0 p in
      c.state.v h0 block_state == c.update_multi_s init_state 0 all_seen)
    end
  else begin
    let prevlen = U64.(total_len `sub` FStar.Int.Cast.uint32_to_uint64 sz) in
    update_multi #c block_state prevlen buf (c.blocks_state_len);
    begin
      let h1 = ST.get () in
      let all_seen = all_seen c h0 p in
      let blocks, rest = split_at_last c all_seen in
      assert(Seq.length blocks = U64.v prevlen);
      assert(c.state.v h0 block_state == c.update_multi_s init_state 0 blocks);
      assert(c.state.v h1 block_state ==
               c.update_multi_s (c.update_multi_s init_state 0 blocks) (U64.v prevlen) rest);
      assert(all_seen `Seq.equal` Seq.append blocks rest);
      (* TODO: the pattern of ``update_multi_associative`` is not triggered *)
      c.update_multi_associative init_state 0 (U64.v prevlen) blocks rest;
      assert(c.state.v h1 block_state == c.update_multi_s init_state 0 all_seen)
      end
  end;

  let h1 = ST.get () in

  assert(
    let all_seen = all_seen c h0 p in
    c.state.v h1 block_state ==
    c.update_multi_s init_state 0 all_seen);

  split_at_last_blocks c (all_seen c h0 p) (B.as_seq h0 data); // TODO: remove?

  let n_blocks = nblocks c len in
  (**) split_at_last_num_blocks_lem c (U32.v len);
  (**) assert(U32.(FStar.UInt.size (v n_blocks * v (c.blocks_state_len)) n));
  let data1_len = n_blocks `U32.mul` c.blocks_state_len in
  let data2_len = len `U32.sub` data1_len in
  let data1 = B.sub data 0ul data1_len in
  let data2 = B.sub data data1_len data2_len in
  update_multi #c block_state total_len data1 data1_len;
  let h01 = ST.get () in
  optional_frame #c (c.state.footprint h0 block_state) k' h0 h01;
  assert(preserves_freeable c p h0 h01);

  begin
    let all_seen = all_seen c h0 p in
    let data1_v = B.as_seq h01 data1 in
    c.update_multi_associative init_state 0 (Seq.length all_seen) all_seen data1_v;
    assert(c.state.v h01 block_state == c.update_multi_s init_state 0 (Seq.append all_seen data1_v))
  end;

  let dst = B.sub buf 0ul data2_len in
  let h1 = ST.get () in
  B.blit data2 0ul dst 0ul data2_len;
  let h2 = ST.get () in
  c.state.frame_invariant (B.loc_buffer buf) block_state h1 h2;
  optional_frame #c (B.loc_buffer buf) k' h1 h2;
  stateful_frame_preserves_freeable #c.state
                                    (B.loc_buffer dst)
                                    (State?.block_state s) h1 h2;
  assert(preserves_freeable c p h01 h2);

  [@inline_let]
  let total_len' = add_len c total_len len in
  [@inline_let]
  let tmp: state_s' c = State #c block_state buf total_len'
    (seen `S.append` B.as_seq h0 data) k'
  in
  p *= tmp;
  let h3 = ST.get () in
  c.state.frame_invariant (B.loc_buffer p) block_state h2 h3;
  optional_frame #c (B.loc_buffer p) k' h2 h3;
  stateful_frame_preserves_freeable #c.state
                                    (B.loc_buffer p)
                                    (State?.block_state s) h2 h3;
  assert(preserves_freeable c p h2 h3);
  assert(preserves_freeable c p h0 h3);

  update_empty_or_full_functional_correctness c p data len h0 h3;
  (* The following proof obligation is the difficult one - keep it here for
   * easy debugging when updating the definitions/proofs *)
  assert(invariant_s c h3 (B.get h3 p 0))
#pop-options

/// Case 3: we are given just enough data to end up on the boundary. It is just
/// a sub-case of [update_small], but with a little bit more precise pre and post
/// conditions.

inline_for_extraction noextract
[@ Meta.Attribute.inline_ ]
val update_round:
  #c:index -> (
  s:state' c ->
  data: B.buffer uint8 ->
  len: UInt32.t ->
  Stack unit
    (requires fun h0 ->
      update_pre c s data len h0 /\
      U32.v (c.init_input_len) + S.length (seen c h0 s) + U32.v len <= U64.v (c.max_input_len) /\ (
      let r = rest c (total_len_h c h0 s) in
      U32.v len + U32.v r = U32.v (c.blocks_state_len) /\
      r <> 0ul))
    (ensures fun h0 _ h1 ->
      update_post c s data len h0 h1 /\
      begin
      let blocks, rest = split_at_last_all_seen c h0 s in
      let blocks', rest' = split_at_last_all_seen c h1 s in
      blocks' `S.equal` blocks /\
      rest' `S.equal` S.append rest (B.as_seq h0 data) /\
      S.length rest' = U32.v (c.blocks_state_len)
      end))

#push-options "--z3rlimit 200 --z3cliopt smt.arith.nl=false"
let update_round #c p data len =
  [@inline_let] let _ = c.state.invariant_loc_in_footprint in
  [@inline_let] let _ = c.state.invariant_loc_in_footprint in
  [@inline_let] let _ = c.update_multi_associative in

  let open LowStar.BufferOps in
  (**) let h0 = ST.get() in
  update_small #c p data len;
  (**) let h1 = ST.get() in
  (**) split_at_last_small c (all_seen c h0 p) (B.as_seq h0 data);
  (**) begin // For some reason, the proof fails if we don't call those
  (**) let blocks, rest = split_at_last_all_seen c h0 p in
  (**) let blocks', rest' = split_at_last_all_seen c h1 p in
  (**) ()
  (**) end
#pop-options


/// General update function, as a decomposition of the three sub-cases
/// ==================================================================

#push-options "--z3rlimit 200"
[@ Meta.Attribute.specialize ]
let update #c p data len =
  let open LowStar.BufferOps in
  let s = !*p in
  let State block_state buf_ total_len seen k' = s in

  if FStar.UInt64.(FStar.Int.Cast.uint32_to_uint64 len >^ c.max_input_len -^ total_len) then
    Hacl.Streaming.Types.MaximumLengthExceeded
  else
    let sz = rest c total_len in
    if len `U32.lte` (c.blocks_state_len `U32.sub` sz) then
      update_small #c p data len
    else if sz = 0ul then
      update_empty_or_full_buf #c p data len
    else begin
      let h0 = ST.get () in
      let diff = c.blocks_state_len `U32.sub` sz in
      let data1 = B.sub data 0ul diff in
      let data2 = B.sub data diff (len `U32.sub` diff) in
      update_round #c p data1 diff;
      let h1 = ST.get () in
      update_empty_or_full_buf #c p data2 (len `U32.sub` diff);
      let h2 = ST.get () in
      (
        let seen = G.reveal seen in
        assert (seen_h c h1 p `S.equal` (S.append seen (B.as_seq h0 data1)));
        assert (seen_h c h2 p `S.equal` (S.append (S.append seen (B.as_seq h0 data1)) (B.as_seq h0 data2)));
        S.append_assoc seen (B.as_seq h0 data1) (B.as_seq h0 data2);
        assert (S.equal (S.append (B.as_seq h0 data1) (B.as_seq h0 data2)) (B.as_seq h0 data));
        assert (S.equal
          (S.append (S.append seen (B.as_seq h0 data1)) (B.as_seq h0 data2))
          (S.append seen (B.as_seq h0 data)));
        assert (seen_h c h2 p `S.equal` (S.append seen (B.as_seq h0 data)));
        ()
      )
    end;
    Hacl.Streaming.Types.Success
#pop-options

#push-options "--z3cliopt smt.arith.nl=false"
val finish_process_begin_functional_correctness :
  c:index ->
  s:state' c ->
  dst:B.buffer uint8 ->
  l: c.output_length_t { B.length dst == c.output_length l } ->
  h0: HS.mem ->
  h1: HS.mem ->
  tmp_block_state: c.state.s ->
  Lemma
  (requires (
    // The precondition of [finish]
    invariant c h0 s /\
    c.state.invariant h1 tmp_block_state /\

    begin
    let s = B.get h0 s 0 in
    let State block_state buf_ total_len seen key = s in

    let r = rest c total_len in
    (**) assert(U32.v r <= U64.v total_len);
    let prev_len = U64.(total_len `sub` FStar.Int.Cast.uint32_to_uint64 r) in
    let r_last = rest_finish c r in
    (**) assert(U32.v r_last <= U32.v r);
    let r_multi = U32.(r -^ r_last) in
    let buf_multi = B.gsub buf_ 0ul r_multi in
    let prev_length = U64.v prev_len in
    let k = optional_reveal #c h0 key in

    c.state.v h1 tmp_block_state == c.update_multi_s (c.state.v h0 block_state) prev_length (B.as_seq h0 buf_multi)
    end))
  (ensures (
    let all_seen = all_seen c h0 s in
    let s = B.get h0 s 0 in
    let State block_state buf_ total_len seen key = s in

    let block_length = U32.v (c.block_len) in
    let n = fst (Lib.UpdateMulti.split_at_last_lazy_nb_rem block_length (S.length all_seen)) in
    let k = optional_reveal #c h0 key in
    let init_state = c.init_s k in

    (**) Math.Lemmas.modulo_lemma 0 block_length;
    (**) Math.Lemmas.cancel_mul_mod n block_length;
    (**) Math.Lemmas.nat_times_nat_is_nat n block_length;
    (**) split_at_last_num_blocks_lem c (S.length all_seen);

    0 % block_length = 0 /\
    0 <= n * block_length /\ (n * block_length) % block_length = 0 /\
    c.state.v h1 tmp_block_state ==
      c.update_multi_s init_state 0 (S.slice all_seen 0 (n * block_length)))
  )
#pop-options

#push-options "--z3cliopt smt.arith.nl=false"
let finish_process_begin_functional_correctness c p dst l h0 h1 tmp_block_state =
  let h3 = h0 in
  let h4 = h1 in
  let s = B.get h0 p 0 in
  let State block_state buf_ total_len seen k' = s in

  let r = rest c total_len in
  let buf_ = B.gsub buf_ 0ul r in

  let prev_len = U64.(total_len `sub` FStar.Int.Cast.uint32_to_uint64 r) in
  let r_last = rest_finish c r in
  let r_multi = U32.(r -^ r_last) in

  let all_seen = all_seen c h0 p in
  let block_length = U32.v (c.block_len) in
  let blocks_state_length = U32.v (c.blocks_state_len) in
  let k = optional_reveal #c h0 k' in
  let prev_length = U64.v prev_len in
  let n = fst (Lib.UpdateMulti.split_at_last_lazy_nb_rem block_length (S.length all_seen)) in
  let init_state = c.init_s k in
  Math.Lemmas.modulo_lemma 0 block_length;
  Math.Lemmas.cancel_mul_mod n block_length;
  assert(prev_length + U32.v r = U64.v total_len);
  assert(U32.v r_multi <= U32.v r);
  assert(prev_length + U32.v r_multi <= U64.v total_len);
  assert(n * block_length <= U64.v total_len);
  let buf_multi = B.gsub buf_ 0ul r_multi in
  assert(
    c.state.v h4 tmp_block_state ==
      c.update_multi_s (c.state.v h0 block_state) prev_length (B.as_seq h3 buf_multi));
  assert(
    B.as_seq h3 buf_multi ==
    S.slice all_seen prev_length (prev_length + U32.v r_multi));
  assert(
    c.state.v h4 tmp_block_state ==
      c.update_multi_s
        (c.update_multi_s init_state 0 (S.slice all_seen 0 prev_length))
        prev_length (S.slice all_seen prev_length (prev_length + U32.v r_multi)));
  assert(0 % block_length = 0);
  assert(S.length (S.slice all_seen 0 prev_length) % block_length = 0);
  assert(prev_length + U32.v r_multi <= S.length all_seen);
  c.update_multi_associative init_state 0 prev_length
                             (S.slice all_seen 0 prev_length)
                             (S.slice all_seen prev_length (prev_length + U32.v r_multi));
  assert(
    S.equal (S.append (S.slice all_seen 0 prev_length)
                      (S.slice all_seen prev_length (prev_length + U32.v r_multi)))
            (S.slice all_seen 0 (prev_length + U32.v r_multi)));
  assert(
    c.state.v h4 tmp_block_state ==
    c.update_multi_s init_state 0 (S.slice all_seen 0 (prev_length + U32.v r_multi)));
  split_at_last_finish c all_seen;
  Math.Lemmas.nat_times_nat_is_nat n block_length;
  assert(0 <= n * block_length);
  assert(n * block_length <= S.length all_seen);
  assert(
    c.state.v h4 tmp_block_state ==
    c.update_multi_s init_state 0 (S.slice all_seen 0 (n * block_length)))
#pop-options

#restart-solver
#push-options "--z3cliopt smt.arith.nl=false --z3rlimit 200"
[@ Meta.Attribute.specialize ]
let finish #c p dst l =
  [@inline_let] let _ = c.state.invariant_loc_in_footprint in
  [@inline_let] let _ = c.key.invariant_loc_in_footprint in
  [@inline_let] let _ = c.update_multi_associative in
  [@inline_let] let _ = allow_inversion key_management in

  let open LowStar.BufferOps in
  let h0 = ST.get () in
  let State block_state buf_ total_len seen k' = !*p in

  push_frame ();
  let h1 = ST.get () in
  c.state.frame_invariant B.loc_none block_state h0 h1;
  stateful_frame_preserves_freeable #c.state B.loc_none block_state h0 h1;
  optional_frame #c B.loc_none k' h0 h1;

  let r = rest c total_len in

  let buf_ = B.sub buf_ 0ul r in

  let tmp_block_state = state_alloca () in

  let h2 = ST.get () in
  assert (B.(loc_disjoint (c.state.footprint h2 tmp_block_state) (c.state.footprint h1 block_state)));
  B.modifies_only_not_unused_in B.loc_none h1 h2;
  c.state.frame_invariant B.loc_none block_state h1 h2;
  stateful_frame_preserves_freeable #c.state B.loc_none block_state h1 h2;
  optional_frame #c B.loc_none k' h1 h2;

  state_copy block_state tmp_block_state;

  let h3 = ST.get () in
  c.state.frame_invariant (c.state.footprint h2 tmp_block_state) block_state h2 h3;
  stateful_frame_preserves_freeable #c.state (c.state.footprint h2 tmp_block_state) block_state h2 h3;
  optional_frame #c (c.state.footprint h2 tmp_block_state) k' h2 h3;

  // Process as many blocks as possible (but leave at least one block for update_last)
  let prev_len = U64.(total_len `sub` FStar.Int.Cast.uint32_to_uint64 r) in
  // The data length to give to update_last
  [@inline_let]
  let r_last = rest_finish c r in
  // The data length to process with update_multi before calling update_last
  [@inline_let]
  let r_multi = U32.(r -^ r_last) in
  // Split the buffer according to the computed lengths
  let buf_last = B.sub buf_ r_multi (Ghost.hide r_last) in
  let buf_multi = B.sub buf_ 0ul r_multi in

  [@inline_let]
  let state_is_block = c.block_len = c.blocks_state_len in
  assert(state_is_block ==> U32.v r_multi = 0);
  assert(state_is_block ==> r_last = r);

  // This will get simplified and will allow some simplifications in the generated code.
  // In particular, it should allow to simplify a bit update_multi
  [@inline_let] let r_multi = if state_is_block then 0ul else r_multi in
  [@inline_let] let r_last = if state_is_block then r else r_last in

  update_multi #c tmp_block_state prev_len buf_multi r_multi;

  let h4 = get () in
  optional_frame #c (c.state.footprint h3 tmp_block_state) k' h3 h4;

  // Functional correctness
  finish_process_begin_functional_correctness c p dst l h0 h4 tmp_block_state;
  split_at_last_finish c (all_seen c h0 p);

  // Process the remaining data
  assert(UInt32.v r_last <= UInt32.v c.block_len);
  let prev_len_last = U64.(total_len `sub` FStar.Int.Cast.uint32_to_uint64 r_last) in
  begin
  // Proving: prev_len_last % block_len = 0
  assert(U64.v prev_len_last = U64.v prev_len + U32.v r_multi);
  Math.Lemmas.modulo_distributivity (U64.v prev_len) (U32.v r_multi) (U32.v (c.block_len));
  Math.Lemmas.modulo_lemma 0 (U32.v (c.block_len));
  assert(U64.v prev_len_last % U32.v (c.block_len) = 0)
  end;
  update_last #c tmp_block_state prev_len_last buf_last r_last;

  let h5 = ST.get () in
  c.state.frame_invariant (c.state.footprint h3 tmp_block_state) block_state h3 h5;
  stateful_frame_preserves_freeable #c.state (c.state.footprint h3 tmp_block_state) block_state h3 h5;
  optional_frame #c (c.state.footprint h3 tmp_block_state) k' h3 h5;

  finish #c k' tmp_block_state dst l;

  let h6 = ST.get () in
  begin
    let r = r_last in
    let all_seen = all_seen c h0 p in
    let blocks_state_length = U32.v (c.blocks_state_len) in
    let block_length = U32.v (c.block_len) in

    let n = fst (Lib.UpdateMulti.split_at_last_lazy_nb_rem block_length (S.length all_seen)) in
    let blocks, rest_ = Lib.UpdateMulti.split_at_last_lazy block_length all_seen in
    let k = optional_reveal #c h0 k' in

    Math.Lemmas.modulo_lemma 0 (U32.v (c.block_len));
    assert(0 % U32.v (c.block_len) = 0);

    assert(B.as_seq h3 buf_last == rest_);

    calc (S.equal) {
      B.as_seq h6 dst;
    (S.equal) { }
      c.finish_s k (c.state.v h5 tmp_block_state) l;
    (S.equal) { }
      c.finish_s k (
        c.update_last_s (c.state.v h4 tmp_block_state) (n * block_length)
          (B.as_seq h4 buf_last)) l;
    (S.equal) { }
      c.finish_s k (
        c.update_last_s (c.state.v h4 tmp_block_state) (n * block_length)
          rest_) l;
    (S.equal) { }
      c.finish_s k (
        c.update_last_s
          (c.update_multi_s (c.init_s k) 0 (S.slice all_seen 0 (n * block_length)))
          (n * block_length)
          rest_) l;
    (S.equal) { c.spec_is_incremental k seen l }
      c.spec_s k seen l;
    }
  end;

  c.state.frame_invariant B.(loc_buffer dst `loc_union` c.state.footprint h5 tmp_block_state) block_state h5 h6;
  stateful_frame_preserves_freeable #c.state B.(loc_buffer dst `loc_union` c.state.footprint h5 tmp_block_state) block_state h5 h6;
  optional_frame #c B.(loc_buffer dst `loc_union` c.state.footprint h5 tmp_block_state) k' h5 h6;

  pop_frame ();
  let h7 = ST.get () in
  c.state.frame_invariant B.(loc_region_only false (HS.get_tip h6)) block_state h6 h7;
  stateful_frame_preserves_freeable #c.state B.(loc_region_only false (HS.get_tip h6)) block_state h6 h7;
  optional_frame #c B.(loc_region_only false (HS.get_tip h6)) k' h6 h7;
  assert (seen_h c h7 p `S.equal` (G.reveal seen));

  // JP: this is not the right way to prove do this proof. Need to use
  // modifies_fresh_frame_popped instead, see e.g.
  // https://github.com/project-everest/everquic-crypto/blob/d812be94e9b1a77261f001c9accb2040b80b7c39/src/QUIC.Impl.fst#L1111
  // for an example
  let mloc = B.loc_union (B.loc_buffer dst) (footprint c h0 p) in
  B.modifies_remove_fresh_frame h0 h1 h7 mloc;
  B.popped_modifies h6 h7;
  assert (B.(modifies mloc h0 h7))
#pop-options

[@ Meta.Attribute.specialize ]
let free #c s =
  let _ = allow_inversion key_management in
  let open LowStar.BufferOps in
  let State block_state buf _ _ k' = !*s in
  let h0 = ST.get () in
  begin match c.km with
  | Runtime -> key_free #c k'
  | Erased -> ()
  end;
  let h1 = ST.get () in
  c.state.frame_freeable (optional_footprint #c h0 k') block_state h0 h1;
  c.state.frame_invariant (optional_footprint #c h0 k') block_state h0 h1;
  state_free #c block_state;
  B.free buf;
  B.free s

let _ = allow_inversion key_management

#push-options "--print_implicits --print_effect_args --print_universes --z3rlimit_factor 4"
%splice[
  functor_create_in_higher;
  functor_copy_higher;
  functor_alloca_higher;
  functor_init_higher;
  functor_update_higher;
  functor_finish_higher;
  functor_free_higher
] (Meta.InterfaceLight.specialize (`index) [
  `create_in;
  `copy;
  `alloca;
  `init;
  `update;
  `finish;
  `free
])

(* We have to define those functions in two steps because otherwise:
   - we can't choose the names
   - F* actually fails when typechecking the .fsti, because it can't find
     definitions for the functions like [mk_create_in] (it ignores the
     output of splice)
 *)
let mk_create_in #c = functor_create_in_higher #c
let mk_copy #c = functor_copy_higher #c
let mk_alloca #c = functor_alloca_higher #c
let mk_init #c = functor_init_higher #c
let mk_update #c = functor_update_higher #c
let mk_finish #c = functor_finish_higher #c
let mk_free #c = functor_free_higher #c
