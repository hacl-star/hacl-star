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

include Hacl.Hash.Definitions
include Spec.Hash.Definitions

// Please refer to this module via a suitable module abbrevation!
unfold noextract
let alg = hash_alg

unfold noextract
let e_alg = Hash.e_alg

// Similar to: Spec.Hash.Definitions.bytes_hash
let bytes_any_hash = s:S.seq UInt8.t { S.length s = 64 }
// Similar to: Hacl.Hash.Definitions.hash_t
let any_hash_t = b:B.buffer UInt8.t { B.length b = 64 }

#push-options "--max_ifuel 1"
let bytes_any_hash_fits (a: alg) (b: bytes_any_hash): Lemma
  (requires True)
  (ensures hash_length a <= S.length b)
=
  ()

let any_hash_t_fits (a: alg) (b: any_hash_t): Lemma
  (requires True)
  (ensures hash_length a <= B.length b)
=
  ()
#pop-options


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

// TR: the following pattern is necessary because, if we generically
// add such a pattern directly on `loc_includes_union_l`, then
// verification will blowup whenever both sides of `loc_includes` are
// `loc_union`s. We would like to break all unions on the
// right-hand-side of `loc_includes` first, using
// `loc_includes_union_r`.  Here the pattern is on `footprint_s`,
// because we already expose the fact that `footprint` is a
// `loc_union`. (In other words, the pattern should be on every
// smallest location that is not exposed to be a `loc_union`.)

let loc_includes_union_l_footprint_s
  (m: HS.mem)
  (l1 l2: B.loc) (#a: alg) (s: state_s a)
: Lemma
  (requires (
    B.loc_includes l1 (footprint_s m s) \/ B.loc_includes l2 (footprint_s m s)
  ))
  (ensures (B.loc_includes (B.loc_union l1 l2) (footprint_s m s)))
  [SMTPat (B.loc_includes (B.loc_union l1 l2) (footprint_s m s))]
= B.loc_includes_union_l l1 l2 (footprint_s m s)

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
  (ensures (B.loc_in (footprint m s) m))
  [SMTPat (invariant m s)]


/// Keeping track of the bytes hashed so far
/// ----------------------------------------
///
/// We offer a stateful predicate that allows the client to tie a particular
/// state to a sequence of bytes hashed so far. There are a variety of styles
/// possible, here's a recap and a discussion of the respective merits of each
/// style, so that we document and avoid going back and forth for future APIs.
///
/// 1. val update (b: erased bytes): unit
///      requires (fun h0 -> hashes h0 s b)
///      ensures (fun h1 -> hashes h1 s (b `append` data))
///
///    The problem with this one is that it requires the client to not only
///    explicitly pass an erased argument, but also requires the client, when
///    chaining calls to construct the "next" value by manually concatenating
///    (ghostly) bytes.
///
/// 2. val update (b: erased bytes): erased bytes
///      requires (fun h0 -> hashes h0 s b)
///      ensures (fun h1 b' -> hashes h1 s b' /\ b' == b `append` data)
///
///    This one is a slight improvement over 1. because the client can "get
///    their hands" on the returned bytes and doesn't need to manually create
///    the concatenation ``b `append` data`` when they chain another call to
///    update.
///
/// 3. val update (): unit
///      requires _
///      ensures (fun h0 _ h1 -> hashed h1 s == hashed h0 s `append` data)
///
///    While 1. and 2. were based on a predicate, this one relies on a function
///    that returns the bytes (ghostly) for any given state and heap. It does
///    not require the client to materialize the erased bytes, and it does not
///    require the client to manually construct intermediary ghost byte values
///    when chaining.
///
/// 4. There's another style based on a state machine and an erased value that
///    materializes all the ghost state in a single record, thus requiring only a
///    single framing lemma (as opposed to three or more for the styles 1. 2. and
///    3.). It appears that this may be overkill for this module and may be better
///    suited to TLS.
///
///                                            JP (20190607)

noextract
let bytes = S.seq UInt8.t

val hashed: #a:Hash.alg -> h:HS.mem -> s:state a -> GTot bytes

// This should alleviate the need for painful proofs about things fitting.
val hash_fits: #a:Hash.alg -> h:HS.mem -> s:state a -> Lemma
  (requires (
    invariant h s))
  (ensures (
    S.length (hashed h s) < Spec.Hash.Definitions.max_input_length a))
  [ SMTPat (hashed h s) ]

val alg_of_state: a:e_alg -> (
  let a = G.reveal a in
  s: state a -> Stack alg
  (fun h0 -> invariant h0 s)
  (fun h0 a' h1 -> h0 == h1 /\ a' == a))


/// Central frame invariants
/// ------------------------
///
/// Everything a client needs to know when they modify something **disjoint**
/// from a hash state.
///
/// Note that the invariant now bundles a variety of conditions related to the
/// hashing predicate, meaning that the only way to establish the invariant is
/// actually to initialize the underlying state. This means that the framing
/// lemmas for invariant and hashed could be bundled together. If we committed
/// to always heap allocating, then we could conceivably have a single framing
/// lemma.

val frame_invariant: #a:alg -> l:B.loc -> s:state a -> h0:HS.mem -> h1:HS.mem -> Lemma
  (requires (
    invariant h0 s /\
    B.loc_disjoint l (footprint h0 s) /\
    B.modifies l h0 h1))
  (ensures (
    invariant h1 s /\
    footprint h0 s == footprint h1 s))
  [ SMTPat (invariant h1 s); SMTPat (B.modifies l h0 h1) ]

val frame_hashed: #a:alg -> l:B.loc -> s:state a -> h0:HS.mem -> h1:HS.mem -> Lemma
  (requires (
    invariant h0 s /\
    B.loc_disjoint l (footprint h0 s) /\
    B.modifies l h0 h1))
  (ensures (hashed h0 s == hashed h1 s))
  [ SMTPat (hashed h1 s); SMTPat (B.modifies l h0 h1) ]

val frame_freeable: #a:alg -> l:B.loc -> s:state a -> h0:HS.mem -> h1:HS.mem -> Lemma
  (requires (
    invariant h0 s /\
    freeable h0 s /\
    B.loc_disjoint l (footprint h0 s) /\
    B.modifies l h0 h1))
  (ensures (freeable h1 s))
  [ SMTPat (freeable h1 s); SMTPat (B.modifies l h0 h1) ]

/// Stateful API
/// ------------

(** @type: true
*)
val create_in (a: Hash.alg) (r: HS.rid): ST (state a)
  (requires (fun _ ->
    HyperStack.ST.is_eternal_region r))
  (ensures (fun h0 s h1 ->
    invariant h1 s /\
    hashed h1 s == S.empty /\
    B.(modifies loc_none h0 h1) /\
    B.fresh_loc (footprint h1 s) h0 h1 /\
    B.(loc_includes (loc_region_only true r) (footprint h1 s)) /\
    freeable h1 s))

(** @type: true
*)
val init: a:e_alg -> (
  let a = G.reveal a in
  s:state a -> Stack unit
  (requires (fun h0 ->
    invariant h0 s))
  (ensures (fun h0 _ h1 ->
    preserves_freeable #a s h0 h1 /\
    invariant #a h1 s /\
    hashed h1 s == S.empty /\
    footprint h0 s == footprint #a h1 s /\
    B.(modifies (footprint #a h0 s) h0 h1))))

unfold
let update_pre
  (a: Hash.alg)
  (s: state a)
  (data: B.buffer UInt8.t)
  (len: UInt32.t)
  (h0: HS.mem)
=
  invariant h0 s /\
  B.live h0 data /\
  U32.v len = B.length data /\
  S.length (hashed h0 s) + U32.v len < pow2 61 /\
  B.(loc_disjoint (loc_buffer data) (footprint h0 s))

unfold
let update_post
  (a: Hash.alg)
  (s: state a)
  (data: B.buffer UInt8.t)
  (len: UInt32.t)
  (h0 h1: HS.mem)
=
  preserves_freeable s h0 h1 /\
  invariant h1 s /\
  B.(modifies (footprint h0 s) h0 h1) /\
  footprint h0 s == footprint h1 s /\
  hashed h1 s == hashed h0 s `S.append` B.as_seq h0 data

(** @type: true
*)
val update:
  a:e_alg -> (
  let a = G.reveal a in
  s:state a ->
  data: B.buffer UInt8.t ->
  len: UInt32.t ->
  Stack unit
    (requires fun h0 -> update_pre a s data len h0)
    (ensures fun h0 s' h1 -> update_post a s data len h0 h1))

/// Note: the state is left to be reused by the caller to feed more data into
/// the hash.
inline_for_extraction
let finish_st (a: Hash.alg) =
  s:state a ->
  dst: Hacl.Hash.Definitions.hash_t a ->
  Stack unit
    (requires fun h0 ->
      invariant h0 s /\
      B.live h0 dst /\
      B.(loc_disjoint (loc_buffer dst) (footprint h0 s)))
    (ensures fun h0 s' h1 ->
      preserves_freeable s h0 h1 /\
      invariant h1 s /\
      hashed h0 s == hashed h1 s /\
      footprint h0 s == footprint h1 s /\
      B.(modifies (loc_union (loc_buffer dst) (footprint h0 s)) h0 h1) /\
      S.equal (B.as_seq h1 dst) (Spec.Hash.hash a (hashed h0 s)))

(** @type: true
*)
val finish: a:e_alg -> finish_st (G.reveal a)

(** @type: true
*)
val free:
  a:e_alg -> (
  let a = G.reveal a in
  s:state a ->
  ST unit
  (requires fun h0 ->
    freeable h0 s /\
    invariant h0 s)
  (ensures fun h0 _ h1 ->
    B.modifies (footprint h0 s) h0 h1))
