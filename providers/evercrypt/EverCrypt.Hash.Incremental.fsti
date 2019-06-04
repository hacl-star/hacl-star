module EverCrypt.Hash.Incremental

open FStar.Mul

/// An alternative API on top of EverCrypt.Hash that holds an internal buffer.
/// This module is the main entry point for hashes in EverCrypt; as such, it
/// offers abstraction, framing principles, and re-export definitions along with
/// a series of helpers.

module B = LowStar.Buffer
module S = FStar.Seq
module ST = FStar.HyperStack.ST
module HS = FStar.HyperStack
module G = FStar.Ghost
module U32 = FStar.UInt32

module Hash = EverCrypt.Hash

open FStar.HyperStack.ST
open Spec.Hash.Definitions

#set-options "--max_fuel 0 --max_ifuel 0"

/// Convenience helpers, so that clients only ever need to refer to this module
/// ---------------------------------------------------------------------------

unfold noextract
let alg = Hash.alg

// TODO: replace with include {Spec,Hacl}.Hash.Definitions here

/// Abstract footprints, with the same machinery as EverCrypt.Hash
/// --------------------------------------------------------------
///
/// Differences from EverCrypt.Hash include: combined framing lemma, and order
/// of arguments in line with ``B.as_seq``, etc. which take the memory
/// first.

[@CAbstractStruct]
val state_s: alg -> Type0

let state alg = B.pointer (state_s alg)

val freeable (#a: alg) (h: HS.mem) (p: state a): Type0

let preserves_freeable #a (s: state a) (h0 h1: HS.mem): Type0 =
  freeable h0 s ==> freeable h1 s

val footprint_s: #a:alg -> HS.mem -> state_s a -> GTot B.loc
let footprint (#a:alg) (m: HS.mem) (s: state a) =
  B.(loc_union (loc_addr_of_buffer s) (footprint_s m (B.deref m s)))

unfold let loc_includes_union_l_footprint_s = EverCrypt.Hash.loc_includes_union_l_footprint_s
unfold let loc_in = EverCrypt.Hash.loc_in
unfold let loc_unused_in = EverCrypt.Hash.loc_unused_in
unfold let fresh_loc = EverCrypt.Hash.fresh_loc
unfold let fresh_is_disjoint = EverCrypt.Hash.fresh_is_disjoint

val invariant_s: (#a:alg) -> HS.mem -> state_s a -> Type0
let invariant (#a:alg) (m: HS.mem) (s: state a) =
  B.live m s /\
  B.(loc_disjoint (loc_addr_of_buffer s) (footprint_s m (B.deref m s))) /\
  invariant_s m (B.get m s 0)

val invariant_loc_in_footprint
  (#a: alg)
  (s: state a)
  (m: HS.mem)
: Lemma
  (requires (invariant m s))
  (ensures (loc_in (footprint m s) m))
  [SMTPat (invariant m s)]

/// Keeping track of the bytes hashed so far
/// ----------------------------------------
///
/// We offer a stateful predicate that allows the client to tie a particular
/// state to a sequence of bytes hashed so far.

noextract
let bytes = S.seq UInt8.t

val hashes: #a:Hash.alg -> h:HS.mem -> s:state a -> b:bytes -> Type0

val hash_fits: #a:Hash.alg -> h:HS.mem -> s:state a -> b:bytes -> Lemma
  (requires hashes h s b)
  (ensures (
    S.length b < Spec.Hash.Definitions.max_input_length a))
  [ SMTPat (hashes h s b) ]

/// Central frame invariants
/// ------------------------
///
/// Everything a client needs to know when they modify something **disjoint**
/// from a hash state.
///
/// Note that the distinction between invariant and hashes is kind of unclear --
/// what should go in the invariant, what should be captured by the hashes
/// predicate, since the two are so close to each other?
///
/// Perhaps it would've been easier to have an erased field in the internal
/// state to keep track of the bytes hashed so far, which would've allowed a
/// function ``val hashed: HS.mem -> state -> bytes`` instead of adding an extra
/// framing lemma.
///
/// Note that the three framing lemmas are most general. We could bundle
/// invariant and freeable (hence committing to always heap-allocating); we
/// could also bundle invariant and hashes (hence preventing clients from
/// performing any operations in-between their call to ``create_in`` and
/// ``init`` since only one of the two pre-conditions would be established).
///
/// Note: it might be useful to call `Hash.fresh_is_disjoint` to turn the
/// `fresh_loc` post-condition of create_in into a more useful `loc_disjoint`
/// clause.


val frame_invariant: #a:alg -> l:B.loc -> s:state a -> h0:HS.mem -> h1:HS.mem -> Lemma
  (requires (
    invariant h0 s /\
    B.loc_disjoint l (footprint h0 s) /\
    B.modifies l h0 h1))
  (ensures (
    invariant h1 s /\
    footprint h0 s == footprint h1 s))

val frame_hashes: #a:alg -> l:B.loc -> s:state a -> b:bytes -> h0:HS.mem -> h1:HS.mem -> Lemma
  (requires (
    invariant h0 s /\
    hashes h0 s b /\
    B.loc_disjoint l (footprint h0 s) /\
    B.modifies l h0 h1))
  (ensures (hashes h1 s b))

val frame_freeable: #a:alg -> l:B.loc -> s:state a -> h0:HS.mem -> h1:HS.mem -> Lemma
  (requires (
    invariant h0 s /\
    freeable h0 s /\
    B.loc_disjoint l (footprint h0 s) /\
    B.modifies l h0 h1))
  (ensures (freeable h1 s))

/// Stateful API
/// ------------

(** @type: true
*)
val create_in (a: Hash.alg) (r: HS.rid): ST (state a)
  (requires (fun _ ->
    HyperStack.ST.is_eternal_region r))
  (ensures (fun h0 s h1 ->
    invariant h1 s /\
    B.(modifies loc_none h0 h1) /\
    fresh_loc (footprint h1 s) h0 h1 /\
    B.(loc_includes (loc_region_only true r) (footprint h1 s)) /\
    freeable h1 s))

(** @type: true
*)
val init (a: Hash.alg) (s: state a): Stack unit
  (requires (fun h0 ->
    invariant h0 s))
  (ensures (fun h0 _ h1 ->
    preserves_freeable s h0 h1 /\
    invariant h1 s /\
    hashes h1 s S.empty /\
    B.(modifies (footprint h0 s) h0 h1)))

unfold
let update_pre
  (a: Hash.alg)
  (s: state a)
  (prev: G.erased bytes)
  (data: B.buffer UInt8.t)
  (len: UInt32.t)
  (h0: HS.mem)
=
  invariant h0 s /\
  hashes h0 s (G.reveal prev) /\
  B.live h0 data /\
  U32.v len = B.length data /\
  S.length (G.reveal prev) + U32.v len < pow2 61 /\
  B.(loc_disjoint (loc_buffer data) (footprint h0 s))

unfold
let update_post
  (a: Hash.alg)
  (s s': state a)
  (prev: G.erased bytes)
  (data: B.buffer UInt8.t)
  (len: UInt32.t)
  (h0 h1: HS.mem)
=
  preserves_freeable s h0 h1 /\
  invariant h1 s /\
  B.(modifies (footprint h0 s) h0 h1) /\
  footprint h0 s == footprint h1 s /\
  hashes h1 s' (Seq.append (G.reveal prev) (B.as_seq h0 data))

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
      invariant h0 s /\
      hashes h0 s (G.reveal prev) /\
      B.live h0 dst /\
      B.(loc_disjoint (loc_buffer dst) (footprint h0 s)))
    (ensures fun h0 s' h1 ->
      preserves_freeable s h0 h1 /\
      invariant h1 s /\
      hashes h1 s (G.reveal prev) /\
      footprint h0 s == footprint h1 s /\
      B.(modifies (loc_union (loc_buffer dst) (footprint h0 s)) h0 h1) /\
      S.equal (B.as_seq h1 dst) (Spec.Hash.hash a (G.reveal prev)))

(** @type: true
*)
val finish: a:Hash.alg -> finish_st a

(** @type: true
*)
val free:
  a:Hash.alg ->
  s:state a ->
  ST unit
  (requires fun h0 ->
    freeable h0 s /\
    invariant h0 s)
  (ensures fun h0 _ h1 ->
    B.modifies (footprint h0 s) h0 h1)
