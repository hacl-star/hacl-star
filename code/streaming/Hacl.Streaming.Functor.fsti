module Hacl.Streaming.Functor

/// Provided an instance of the type class, this creates a streaming API on top.
/// This means that every function in this module takes two extra arguments
/// compared to the previous streaming module specialized for hashes: the type
/// of the index, and a type class for that index. Then, as usual, a given value
/// for the index as a parameter.
///
/// This streaming API only allocates its internal state on the heap, no support
/// for allocation on the stack via StackInline.

#set-options "--fuel 0 --ifuel 0"

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

inline_for_extraction noextract
let uint8 = Lib.IntTypes.uint8

inline_for_extraction noextract
let uint32 = Lib.IntTypes.uint32

/// State machinery
/// ===============

// TODO: when state_s is declared as CAbstractStruct, it prevents Hacl_Streaming_MD5.c
// and Hacl_Streaming_SHA1.c from compiling, because KaRaMeL tries to share the state_s
// type definition with Hacl_Streaming_SHA2.c, which is hidden.
//[@CAbstractStruct]
val state_s (c: index)
  (t: Type0 { t == c.state.s })
  (t': Type0 { t' == optional_key c }):
  Type0

inline_for_extraction noextract
let state_s' c = state_s c c.state.s (optional_key c)

/// State is equipped with a superfluous type-level parameter to ensure ML-like
/// prenex polymorphism and hence low-level monomorphization via KaRaMeL.
///
/// Run-time functions MUST take t as a parameter. Proof-level functions are
/// welcome to instantiate it directly with ``c.state i``.
let state (c: index)
  (t: Type0 { t == c.state.s })
  (t': Type0 { t' == optional_key c})
=
  B.pointer (state_s c t t')

inline_for_extraction noextract
let state' c = state c c.state.s (optional_key c)

val footprint_s (c: index) (h: HS.mem) (s: state_s' c): GTot B.loc

let footprint (c: index) (m: HS.mem) (s: state' c) =
  B.(loc_union (loc_addr_of_buffer s) (footprint_s c m (B.deref m s)))

/// Invariants
/// ==========

noextract
let bytes = S.seq uint8

let loc_includes_union_l_footprint_s
  (c: index)
  (m: HS.mem)
  (l1 l2: B.loc) (s: state_s' c)
: Lemma
  (requires (
    B.loc_includes l1 (footprint_s c m s) \/ B.loc_includes l2 (footprint_s c m s)
  ))
  (ensures (B.loc_includes (B.loc_union l1 l2) (footprint_s c m s)))
  [SMTPat (B.loc_includes (B.loc_union l1 l2) (footprint_s c m s))]
= B.loc_includes_union_l l1 l2 (footprint_s c m s)

inline_for_extraction noextract
val invariant_s (c: index) (h: HS.mem) (s: state_s' c): Type0

inline_for_extraction noextract
val freeable (c: index) (h: HS.mem) (s: state' c) : Type0

inline_for_extraction noextract
let preserves_freeable (c: index) (s: state' c) (h0 h1 : HS.mem): Type0 =
  freeable c h0 s ==> freeable c h1 s

inline_for_extraction noextract
let invariant (c: index) (m: HS.mem) (s: state' c) =
  invariant_s c m (B.get m s 0) /\
  B.live m s /\
  B.(loc_disjoint (loc_addr_of_buffer s) (footprint_s c m (B.deref m s)))

val invariant_loc_in_footprint
  (c: index)
  (s: state' c)
  (m: HS.mem)
: Lemma
  (requires (invariant c m s))
  (ensures (B.loc_in (footprint c m s) m))
  [SMTPat (invariant c m s)]

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

val seen: c:index -> h:HS.mem -> s:state' c -> GTot bytes

/// We maintain the invariant that the length of the data hashed so far is smaller
/// than the maximum length accepted by the hash algorithm.
///
/// Note that for hashes like blake2, the key is turned into a block which is then
/// concatenated with the bytes fed into the algorithm (we copy this iniial
/// block into the temporary buffer upon initilization). We count the length of
/// this initial block in the total length of the hashed data.
val seen_bounded: c:index -> h:HS.mem -> s:state' c -> Lemma
  (requires (
    invariant c h s))
  (ensures (
    U32.v c.init_input_len + S.length (seen c h s) <= U64.v c.max_input_len))

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
val key: c:index -> h:HS.mem -> s:state' c -> GTot c.key.t

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
///
/// TODO: frame_key!

val frame_invariant: c:index -> l:B.loc -> s:state' c -> h0:HS.mem -> h1:HS.mem -> Lemma
  (requires (
    invariant c h0 s /\
    B.loc_disjoint l (footprint c h0 s) /\
    B.modifies l h0 h1))
  (ensures (
    invariant c h1 s /\
    footprint c h0 s == footprint c h1 s /\
    preserves_freeable c s h0 h1))
  [ SMTPat (invariant c h1 s); SMTPat (B.modifies l h0 h1) ]

val frame_seen: c:index -> l:B.loc -> s:state' c -> h0:HS.mem -> h1:HS.mem -> Lemma
  (requires (
    invariant c h0 s /\
    B.loc_disjoint l (footprint c h0 s) /\
    B.modifies l h0 h1))
  (ensures (seen c h0 s == seen c h1 s))
  [ SMTPat (seen c h1 s); SMTPat (B.modifies l h0 h1) ]


/// Stateful API
/// ============

// The number of bytes fed so far into the hash, so that the client doesn't have
// to track it themselves, since this module does it anyhow.
inline_for_extraction noextract
val seen_length:
  c:index ->
  t:Type0 { t == c.state.s } ->
  t':Type0 { t' == optional_key c } ->
  s:state c t t' ->
  Stack U64.t
  (fun h0 -> invariant c h0 s)
  (fun h0 l h1 -> h0 == h1 /\ U64.v l == U32.v c.init_input_len +  S.length (seen c h0 s))

inline_for_extraction noextract
let create_in_st (c:index) =
  k:c.key.s ->
  r: HS.rid ->
  ST (state' c)
  (requires (fun h0 ->
    c.key.invariant h0 k /\
    HyperStack.ST.is_eternal_region r))
  (ensures (fun h0 s h1 ->
    invariant c h1 s /\
    freeable c h1 s /\
    seen c h1 s == S.empty /\
    key c h1 s == c.key.v h0 k /\
    B.(modifies loc_none h0 h1) /\
    B.fresh_loc (footprint c h1 s) h0 h1 /\
    B.(loc_includes (loc_region_only true r) (footprint c h1 s))))

inline_for_extraction noextract
val create_in: #c:index -> create_in_st c

inline_for_extraction noextract
let copy_st (c:index) =
  s0:state' c ->
  r: HS.rid ->
  ST (state' c)
  (requires (fun h0 ->
    invariant c h0 s0 /\
    HyperStack.ST.is_eternal_region r))
  (ensures (fun h0 s h1 ->
    invariant c h1 s /\
    freeable c h1 s /\
    seen c h1 s == seen c h0 s0 /\
    key c h1 s == key c h0 s0 /\
    B.(modifies loc_none h0 h1) /\
    B.fresh_loc (footprint c h1 s) h0 h1 /\
    B.(loc_includes (loc_region_only true r) (footprint c h1 s))))

inline_for_extraction noextract
val copy: #c:index -> copy_st c

inline_for_extraction noextract
let alloca_st (c:index) =
  k:c.key.s ->
  StackInline (state' c)
  (requires (fun h0 ->
    c.key.invariant h0 k))
  (ensures (fun h0 s h1 ->
    invariant c h1 s /\
    seen c h1 s == S.empty /\
    key c h1 s == c.key.v h0 k /\
    B.(modifies loc_none h0 h1) /\
    B.fresh_loc (footprint c h1 s) h0 h1 /\
    B.(loc_includes (loc_region_only true (HS.get_tip h1)) (footprint c h1 s))))

inline_for_extraction noextract
val alloca: #c:index -> alloca_st c

/// Note: this is more like a "reinit" function so that clients can reuse the state.
inline_for_extraction noextract
let init_st (c:index) =
  k:c.key.s ->
  s:state' c ->
  Stack unit
  (requires (fun h0 ->
    c.key.invariant h0 k /\
    B.loc_disjoint (c.key.footprint h0 k) (footprint c h0 s) /\
    invariant c h0 s))
  (ensures (fun h0 _ h1 ->
    invariant c h1 s /\
    seen c h1 s == S.empty /\
    key c h1 s == c.key.v h0 k /\
    footprint c h0 s == footprint c h1 s /\
    B.(modifies (footprint c h0 s) h0 h1) /\
    preserves_freeable c s h0 h1))

inline_for_extraction noextract
val init: #c:index -> init_st c

unfold noextract
let update_pre
  (c: index)
  (s: state' c)
  (data: B.buffer uint8)
  (len: UInt32.t)
  (h0: HS.mem)
=
  invariant c h0 s /\
  B.live h0 data /\
  U32.v len = B.length data /\
  B.(loc_disjoint (loc_buffer data) (footprint c h0 s))

unfold noextract
let update_post
  (c: index)
  (s: state' c)
  (data: B.buffer uint8)
  (len: UInt32.t)
  (h0 h1: HS.mem)
=
  invariant c h1 s /\
  B.(modifies (footprint c h0 s) h0 h1) /\
  footprint c h0 s == footprint c h1 s /\
  seen c h1 s == seen c h0 s `S.append` B.as_seq h0 data /\
  key c h1 s == key c h0 s /\
  preserves_freeable c s h0 h1

inline_for_extraction noextract
let update_st (c:index) =
  s:state' c ->
  data: B.buffer uint8 ->
  len: UInt32.t ->
  Stack Hacl.Streaming.Types.error_code
    (requires fun h0 -> update_pre c s data len h0)
    (ensures fun h0 s' h1 ->
      let open Hacl.Streaming.Types in
      match s' with
      | Success ->
          U32.v c.init_input_len + S.length (seen c h0 s) + UInt32.v len <= U64.v c.max_input_len /\
          update_post c s data len h0 h1
      | MaximumLengthExceeded ->
          U32.v c.init_input_len + S.length (seen c h0 s) + UInt32.v len > U64.v c.max_input_len /\
          h0 == h1
      | _ ->
          False)

inline_for_extraction noextract
val update: #c:index -> update_st c


inline_for_extraction noextract
let finish_st (c: index) =
  s:state' c ->
  dst:B.buffer uint8 ->
  l:c.output_length_t { B.length dst == c.output_length l } ->
  Stack unit
    (requires fun h0 ->
      invariant c h0 s /\
      B.live h0 dst /\
      B.(loc_disjoint (loc_buffer dst) (footprint c h0 s)))
    (ensures fun h0 s' h1 ->
      invariant c h1 s /\
      seen c h0 s == seen c h1 s /\
      key c h1 s == key c h0 s /\
      footprint c h0 s == footprint c h1 s /\
      B.(modifies (loc_union (loc_buffer dst) (footprint c h0 s)) h0 h1) /\ (
      seen_bounded c h0 s;
      S.equal (B.as_seq h1 dst) (c.spec_s (key c h0 s) (seen c h0 s) l)) /\
      preserves_freeable c s h0 h1)

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
val mk_finish: #c:index -> finish_st c

inline_for_extraction noextract
let free_st
  (c:index) =
  s:state' c ->
  ST unit
  (requires fun h0 ->
    invariant c h0 s /\
    freeable c h0 s)
  (ensures fun h0 _ h1 ->
    B.modifies (footprint c h0 s) h0 h1)

inline_for_extraction noextract
val free: #c:index -> free_st c
