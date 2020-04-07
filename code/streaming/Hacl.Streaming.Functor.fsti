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
module I = Hacl.Streaming.Interface

open Hacl.Streaming.Interface
open FStar.HyperStack.ST
open LowStar.BufferOps
open FStar.Mul

inline_for_extraction noextract
let uint8 = Lib.IntTypes.uint8

inline_for_extraction noextract
let uint32 = Lib.IntTypes.uint32

/// State machinery
/// ===============

[@CAbstractStruct]
val state_s (#index: Type0) (c: block index) (i: index) (t: Type0 { t == c.state.s i }): Type0

/// State is equipped with a superfluous type-level parameter to ensure ML-like
/// prenex polymorphism and hence low-level monomorphization via KreMLin.
///
/// Run-time functions MUST take t as a parameter. Proof-level functions are
/// welcome to instantiate it directly with ``c.state i``.
let state #index (c: block index) (i: index) (t: Type0 { t == c.state.s i }) = B.pointer (state_s c i t)

val freeable (#index: Type0) (c: block index) (i: index) (h: HS.mem) (p: state c i (c.state.s i)): Type0

let preserves_freeable #index (c: block index) (i: index) (s: state c i (c.state.s i)) (h0 h1: HS.mem): Type0 =
  freeable c i h0 s ==> freeable c i h1 s

val footprint_s (#index: Type0) (c: block index) (i: index) (h: HS.mem) (s: state_s c i (c.state.s i)): GTot B.loc

let footprint (#index: Type0) (c: block index) (i: index) (m: HS.mem) (s: state c i (c.state.s i)) =
  B.(loc_union (loc_addr_of_buffer s) (footprint_s c i m (B.deref m s)))

/// Invariants
/// ==========

noextract
let bytes = S.seq uint8

let loc_includes_union_l_footprint_s
  #index
  (c: block index)
  (i: index)
  (m: HS.mem)
  (l1 l2: B.loc) (s: state_s c i (c.state.s i))
: Lemma
  (requires (
    B.loc_includes l1 (footprint_s c i m s) \/ B.loc_includes l2 (footprint_s c i m s)
  ))
  (ensures (B.loc_includes (B.loc_union l1 l2) (footprint_s c i m s)))
  [SMTPat (B.loc_includes (B.loc_union l1 l2) (footprint_s c i m s))]
= B.loc_includes_union_l l1 l2 (footprint_s c i m s)

val invariant_s (#index: Type0) (c: block index) (i: index) (h: HS.mem) (s: state_s c i (c.state.s i)): Type0

let invariant #index (c: block index) (i: index) (m: HS.mem) (s: state c i (c.state.s i)) =
  B.live m s /\
  B.(loc_disjoint (loc_addr_of_buffer s) (footprint_s c i m (B.deref m s))) /\
  invariant_s c i m (B.get m s 0)

val invariant_loc_in_footprint
  (#index: Type0)
  (c: block index)
  (i: index)
  (s: state c i (c.state.s i))
  (m: HS.mem)
: Lemma
  (requires (invariant c i m s))
  (ensures (B.loc_in (footprint c i m s) m))
  [SMTPat (invariant c i m s)]

/// Keeping track of the bytes fed into the algorithm so far
/// ========================================================
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

val seen: #index:Type0 -> c:block index -> i:index -> h:HS.mem -> s:state c i (c.state.s i) -> GTot bytes

val seen_bounded: #index:Type0 -> c:block index -> i:index -> h:HS.mem -> s:state c i (c.state.s i) -> Lemma
  (requires (
    invariant c i h s))
  (ensures (
    S.length (seen c i h s) <= c.max_input_length i))

/// A fine design point here... There are two styles that have been used in
/// EverCrypt and throughout for key management.
///
/// The first one keeps an erased key in the state_s and therefore clients
/// "know" that the value of the key depends only on the state_s (*not* on a
/// memory) and hence can conclude that the key remains the same *as long as
/// the modified footprints are footprint_s*. This essentially means that you
/// cannot "reallocate" the abstract struct. This works for simple cases like
/// EverCrypt.AEAD.
///
/// Here, we definitely reallocate the abstract struct to functionally update
/// the size of the buffer, so we don't bother and reveal everywhere that the
/// key remains the same (i.e. we specify it fully just like ``seen``).
///
/// Note: annotating the projector because of an interleaving bug.
val key: #index:Type0 -> c:block index -> i:index -> h:HS.mem -> s:state c i (c.state.s i) -> GTot (c.key.t i)

/// Framing
/// =======
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

val frame_invariant: #index:Type0 -> c:block index -> i:index -> l:B.loc -> s:state c i (c.state.s i) -> h0:HS.mem -> h1:HS.mem -> Lemma
  (requires (
    invariant c i h0 s /\
    B.loc_disjoint l (footprint c i h0 s) /\
    B.modifies l h0 h1))
  (ensures (
    invariant c i h1 s /\
    footprint c i h0 s == footprint c i h1 s))
  [ SMTPat (invariant c i h1 s); SMTPat (B.modifies l h0 h1) ]

val frame_seen: #index:Type0 -> c:block index -> i:index -> l:B.loc -> s:state c i (c.state.s i) -> h0:HS.mem -> h1:HS.mem -> Lemma
  (requires (
    invariant c i h0 s /\
    B.loc_disjoint l (footprint c i h0 s) /\
    B.modifies l h0 h1))
  (ensures (seen c i h0 s == seen c i h1 s))
  [ SMTPat (seen c i h1 s); SMTPat (B.modifies l h0 h1) ]

val frame_freeable: #index:Type0 -> c:block index -> i:index -> l:B.loc -> s:state c i (c.state.s i) -> h0:HS.mem -> h1:HS.mem -> Lemma
  (requires (
    invariant c i h0 s /\
    freeable c i h0 s /\
    B.loc_disjoint l (footprint c i h0 s) /\
    B.modifies l h0 h1))
  (ensures (freeable c i h1 s))
  [ SMTPat (freeable c i h1 s); SMTPat (B.modifies l h0 h1) ]


/// Stateful API
/// ============

inline_for_extraction noextract
val index_of_state:
  #index:Type0 ->
  c:block index ->
  i:G.erased index -> (
  let i = G.reveal i in
  t:Type0 { t == c.state.s i } ->
  s:state c i t ->
  Stack index
  (fun h0 -> invariant c i h0 s)
  (fun h0 i' h1 -> h0 == h1 /\ i' == i))

inline_for_extraction noextract
val create_in:
  #index: Type0 ->
  c:block index ->
  i:index ->
  t:Type0 { t == c.state.s i } ->
  k:c.key.s i ->
  r: HS.rid ->
  ST (state c i t)
  (requires (fun h0 ->
    c.key.invariant #i h0 k /\
    HyperStack.ST.is_eternal_region r))
  (ensures (fun h0 s h1 ->
    invariant c i h1 s /\
    seen c i h1 s == S.empty /\
    key c i h1 s == c.key.v i h0 k /\
    B.(modifies loc_none h0 h1) /\
    B.fresh_loc (footprint c i h1 s) h0 h1 /\
    B.(loc_includes (loc_region_only true r) (footprint c i h1 s)) /\
    freeable c i h1 s))

/// Note: this is more like a "reinit" function so that clients can reuse the state.
inline_for_extraction noextract
val init:
  #index:Type0 ->
  c:block index ->
  i:G.erased index -> (
  let i = G.reveal i in
  t:Type0 { t == c.state.s i } ->
  k:c.key.s i ->
  s:state c i t ->
  Stack unit
  (requires (fun h0 ->
    c.key.invariant #i h0 k /\
    B.loc_disjoint (c.key.footprint #i h0 k) (footprint c i h0 s) /\
    invariant c i h0 s))
  (ensures (fun h0 _ h1 ->
    preserves_freeable c i s h0 h1 /\
    invariant c i h1 s /\
    seen c i h1 s == S.empty /\
    key c i h1 s == c.key.v i h0 k /\
    footprint c i h0 s == footprint c i h1 s /\
    B.(modifies (footprint c i h0 s) h0 h1))))

unfold noextract
let update_pre
  #index
  (c: block index)
  (i: index)
  (s: state c i (c.state.s i))
  (data: B.buffer uint8)
  (len: UInt32.t)
  (h0: HS.mem)
=
  invariant c i h0 s /\
  B.live h0 data /\
  U32.v len = B.length data /\
  S.length (seen c i h0 s) + U32.v len <= c.max_input_length i /\
  B.(loc_disjoint (loc_buffer data) (footprint c i h0 s))

unfold noextract
let update_post
  #index
  (c: block index)
  (i: index)
  (s: state c i (c.state.s i))
  (data: B.buffer uint8)
  (len: UInt32.t)
  (h0 h1: HS.mem)
=
  preserves_freeable c i s h0 h1 /\
  invariant c i h1 s /\
  B.(modifies (footprint c i h0 s) h0 h1) /\
  footprint c i h0 s == footprint c i h1 s /\
  seen c i h1 s == seen c i h0 s `S.append` B.as_seq h0 data /\
  key c i h1 s == key c i h0 s

inline_for_extraction noextract
val update:
  #index:Type0 ->
  c:block index ->
  i:G.erased index -> (
  let i = G.reveal i in
  t:Type0 { t == c.state.s i } ->
  s:state c i t ->
  data: B.buffer uint8 ->
  len: UInt32.t ->
  Stack unit
    (requires fun h0 -> update_pre c i s data len h0)
    (ensures fun h0 s' h1 -> update_post c i s data len h0 h1))

/// A word of caution. Once partially applied to a type class, this function
/// will generate a stack allocation at type ``state i`` via ``c.alloca``. If
/// ``state`` is indexed over ``i``, then this function will not compile to C.
/// (In other words: there's a reason why mk_finish does *NOT* take i ghostly.)
///
/// To work around this, it suffices to apply ``mk_finish`` to each possible
/// value for the index, then to abstract over ``i`` again if agility is
/// desired. See EverCrypt.Hash.Incremental for an example. Alternatively, we
/// could provide a finish that relies on a heap allocation of abstract state
/// and does not need to be specialized.
inline_for_extraction noextract
val mk_finish:
  #index:Type0 ->
  c:block index ->
  i:index ->
  t:Type0 { t == c.state.s i } ->
  s:state c i t ->
  dst:B.buffer uint8 { B.len dst == c.output_len i } ->
  Stack unit
    (requires fun h0 ->
      invariant c i h0 s /\
      B.live h0 dst /\
      B.(loc_disjoint (loc_buffer dst) (footprint c i h0 s)))
    (ensures fun h0 s' h1 ->
      preserves_freeable c i s h0 h1 /\
      invariant c i h1 s /\
      seen c i h0 s == seen c i h1 s /\
      key c i h1 s == key c i h0 s /\
      footprint c i h0 s == footprint c i h1 s /\
      B.(modifies (loc_union (loc_buffer dst) (footprint c i h0 s)) h0 h1) /\ (
      seen_bounded c i h0 s;
      S.equal (B.as_seq h1 dst) (c.spec_s i (key c i h0 s) (seen c i h0 s))))

inline_for_extraction noextract
val free:
  #index:Type0 ->
  c:block index ->
  i:G.erased index -> (
  let i = G.reveal i in
  t:Type0 { t == c.state.s i } ->
  s:state c i t ->
  ST unit
  (requires fun h0 ->
    freeable c i h0 s /\
    invariant c i h0 s)
  (ensures fun h0 _ h1 ->
    B.modifies (footprint c i h0 s) h0 h1))
