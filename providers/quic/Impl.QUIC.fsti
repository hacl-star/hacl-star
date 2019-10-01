/// An implementation of Spec.QUIC.fst that is concerned only with functional
/// correctness (no notion of model for now).
module Impl.QUIC

module G = FStar.Ghost
module B = LowStar.Buffer
module S = FStar.Seq
module HS = FStar.HyperStack

module U64 = FStar.UInt64
module U32 = FStar.UInt32
module U8 = FStar.UInt8

open FStar.HyperStack
open FStar.HyperStack.ST

open EverCrypt.Helpers
open EverCrypt.Error

#set-options "--max_fuel 0 --max_ifuel 0"

type role = | Reader | Writer

unfold noextract
let hash_alg = Spec.Hash.Definitions.hash_alg

unfold noextract
let aead_alg = Spec.AEAD.alg

unfold noextract
let lbytes = Spec.QUIC.lbytes

/// This is not a cryptographic index; rather, this is just a regular type
/// index, where instead of indexing on a single algorithm (like, say, AEAD), we
/// index on three values.
///
/// The record is here to limit the profileration of hide/reveal in the stateful
/// functions, and to give easier projectors (ADL, JP).
type index = {
  role: role;
  hash_alg: Spec.Hash.Definitions.hash_alg;
  aead_alg: Spec.AEAD.alg;
}

/// Boilerplate
/// -----------

[@CAbstractStruct]
val state_s: index -> Type0

let state i = B.pointer (state_s i)

val footprint_s: #i:index -> state_s i -> GTot B.loc
let footprint (#i:index) (m: HS.mem) (s: state i) =
  B.(loc_union (loc_addr_of_buffer s) (footprint_s (B.deref m s)))

let loc_includes_union_l_footprint_s
  (l1 l2: B.loc) (#i: index) (s: state_s i)
: Lemma
  (requires (
    B.loc_includes l1 (footprint_s s) \/ B.loc_includes l2 (footprint_s s)
  ))
  (ensures (B.loc_includes (B.loc_union l1 l2) (footprint_s s)))
  [SMTPat (B.loc_includes (B.loc_union l1 l2) (footprint_s s))]
= B.loc_includes_union_l l1 l2 (footprint_s s)

val invariant_s: (#i:index) -> HS.mem -> state_s i -> Type0
let invariant (#i:index) (m: HS.mem) (s: state i) =
  B.live m s /\
  B.(loc_disjoint (loc_addr_of_buffer s) (footprint_s (B.deref m s))) /\
  invariant_s m (B.get m s 0)

val invariant_loc_in_footprint
  (#i: index)
  (s: state i)
  (m: HS.mem)
: Lemma
  (requires (invariant m s))
  (ensures (B.loc_in (footprint m s) m))
  [SMTPat (invariant m s)]

/// Ghost accessors
/// ---------------
///
/// We need to define those, so that we can state a framing lemma for them.
/// Attempting a new convention to distinguish ghost accessors from stateful
/// functions: a ``g_`` prefix.

val g_aead_key: #i:index -> (s: state_s i) -> (h: HS.mem) -> Spec.AEAD.kv i.aead_alg
val g_static_iv: #i:index -> (s: state_s i) -> (h: HS.mem) -> lbytes 12
val g_counter: #i:index -> (s: state_s i) -> (h: HS.mem) -> Spec.QUIC.nat62
val g_hash: #i:index -> (s: state_s i) -> (h: HS.mem) -> Spec.Hash.Definitions.bytes_hash i.hash_alg

/// Preserving all the ghost accessors via a single framing lemma only works
/// because we don't do stack allocation. See comments in
/// EverCrypt.Hash.Incremental.
val frame_invariant: #i:index -> l:B.loc -> s:state i -> h0:HS.mem -> h1:HS.mem -> Lemma
  (requires (
    invariant h0 s /\
    B.loc_disjoint l (footprint h0 s) /\
    B.modifies l h0 h1))
  (ensures (
    invariant h1 s /\
    footprint h0 s == footprint h1 s /\
    g_aead_key (B.deref h0 s) == g_aead_key (B.deref h1 s) /\
    g_static_iv (B.deref h0 s) == g_static_iv (B.deref h1 s) /\
    g_counter (B.deref h0 s) == g_counter (B.deref h1 s) /\
    g_hash (B.deref h0 s) == g_hash (B.deref h1 s)
    ))
  // Assertion failure: unexpected pattern term
  (*[ SMTPat (B.modifies l h0 h1); SMTPatOr [
    [ SMTPat (invariant h1 s) ];
    [ SMTPat (footprint h1 s) ];
    [ SMTPat (g_aead_key (B.deref h1 s)) ];
    [ SMTPat (g_static_iv (B.deref h1 s)) ];
    [ SMTPat (g_counter (B.deref h1 s)) ]
  ]]*)

/// Actual stateful API
/// -------------------
///
/// Note that we do not store the role at run-time, since the representation is
/// the same regardless of the role. It's just the *interpretation* of the
/// packet number that varies according to the role.

val aead_alg_of_state (i: G.erased index) (s: state (G.reveal i)): Stack aead_alg
  (requires (fun h0 -> invariant #(G.reveal i) h0 s))
  (ensures (fun h0 a h1 ->
    a == (G.reveal i).aead_alg /\
    h0 == h1))

val hash_alg_of_state (i: G.erased index) (s: state (G.reveal i)): Stack hash_alg
  (requires (fun h0 -> invariant #(G.reveal i) h0 s))
  (ensures (fun h0 a h1 ->
    a == (G.reveal i).hash_alg /\
    h0 == h1))

// TODO: move to spec
val label_key : Spec.QUIC.lbytes 3
val label_iv : Spec.QUIC.lbytes 2
val label_hp : Spec.QUIC.lbytes 2

val encrypt: #i:G.erased index -> (
  let i = G.reveal i in
  s: state i ->
  dst: B.buffer U8.t ->
  h: header ->
  plain: B.buffer U8.t ->
  plain_len: U32.t {
    3 <= U32.v plain_len /\
    U32.v plain_len < Spec.QUIC.max_plain_length /\
    B.length plain = U32.v plain_len
  } ->
  pn_len: u2 ->
  Stack error_code
    (requires fun h0 ->
      // Memory & preservation
      B.live h0 plain /\ B.live h0 dst /\
      B.disjoint plain dst /\ // JP: probably needed, along with many others
      invariant h0 s /\

      i.role = Writer /\
      // TODO: same length condition as in QuicCrypto.fsti

      True)
    (ensures fun h0 r h1 ->
      // Memory & preservation
      B.modifies (footprint h0 s) h0 h1 /\
      invariant h1 s /\
      footprint h1 s == footprint h0 s /\ (

      // Functional correctness
      let s0 = g_hash (B.deref h0 s) in
      let k = Spec.QUIC.derive_secret i.hash_alg s0 label_key (Spec.AEAD.key_length a.ea) in
      let iv = Spec.QUIC.derive_secret i.hash_alg s0 label_iv 12 in
      let pne = Spec.QUIC.derive_secret i.hash_alg s0 label_hp (Spec.QUIC.ae_keysize a.ea) in
      let plain: Spec.QUIC.pbytes = B.as_seq h0 plain in
      let packet: Spec.QUIC.packet = B.as_seq h1 out in
      let ctr = pnT s Writer h0 in
      packet == Spec.QUIC.encrypt a.ea k iv pne (U8.v pn_len) ctr (spec_header h h0) plain)))
