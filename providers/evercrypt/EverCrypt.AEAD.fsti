module EverCrypt.AEAD

/// The new AEAD interface for EverCrypt, which supersedes the functions found
/// in EverCrypt.fst
///
/// The expected usage for this module is as follows:
/// - client expands key, obtaining an ``expanded_key a``
/// - client uses ``encrypt``/``decrypt`` with the same ``expanded_key a`` repeatedly.
///
/// This usage protocol is enforced for verified F* clients but, naturally,
/// isn't for C clients.

module S = FStar.Seq
module G = FStar.Ghost

module HS = FStar.HyperStack
module ST = FStar.HyperStack.ST
module MB = LowStar.Monotonic.Buffer
module B = LowStar.Buffer

open FStar.HyperStack.ST
open FStar.Integers

open Spec.AEAD
open EverCrypt.Error

/// Note: if the fst and the fsti are running on different fuel settings,
/// something that works in the interactive mode for the fsti, when
/// "re-interpreted" in the fst, might stop working!
#set-options "--max_fuel 0 --max_ifuel 0"


/// Abstract footprints, with the same machinery as EverCrypt.Hash
/// --------------------------------------------------------------
///
/// Differences from EverCrypt.Hash include: combined framing lemma, the
/// equivalent of the ``repr`` function does *not* require the memory, and order
/// of arguments to be in line with ``B.as_seq``, etc. which take the memory
/// first.

[@CAbstractStruct]
val state_s: alg -> Type0

let state alg = B.pointer (state_s alg)

val freeable_s: #(a: alg) -> state_s a -> Type0

let freeable (#a: alg) (h: HS.mem) (p: state a) =
  B.freeable p /\ freeable_s (B.deref h p)

let preserves_freeable #a (s: state a) (h0 h1: HS.mem): Type0 =
  freeable h0 s ==> freeable h1 s

val footprint_s: #a:alg -> state_s a -> GTot B.loc
let footprint (#a:alg) (m: HS.mem) (s: state a) =
  B.(loc_union (loc_addr_of_buffer s) (footprint_s (B.deref m s)))

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
  (l1 l2: B.loc) (#a: alg) (s: state_s a)
: Lemma
  (requires (
    B.loc_includes l1 (footprint_s s) \/ B.loc_includes l2 (footprint_s s)
  ))
  (ensures (B.loc_includes (B.loc_union l1 l2) (footprint_s s)))
  [SMTPat (B.loc_includes (B.loc_union l1 l2) (footprint_s s))]
= B.loc_includes_union_l l1 l2 (footprint_s s)

val invariant_s: (#a:alg) -> HS.mem -> state_s a -> Type0
let invariant (#a:alg) (m: HS.mem) (s: state a) =
  B.live m s /\
  B.(loc_disjoint (loc_addr_of_buffer s) (footprint_s (B.deref m s))) /\
  invariant_s m (B.get m s 0)

val invariant_loc_in_footprint
  (#a: alg)
  (s: state a)
  (m: HS.mem)
: Lemma
  (requires (invariant m s))
  (ensures (B.loc_in (footprint m s) m))
  [SMTPat (invariant m s)]

val frame_invariant: #a:alg -> l:B.loc -> s:state a -> h0:HS.mem -> h1:HS.mem -> Lemma
  (requires (
    invariant h0 s /\
    B.loc_disjoint l (footprint h0 s) /\
    B.modifies l h0 h1))
  (ensures (
    invariant h1 s /\
    footprint h0 s == footprint h1 s))


/// Actual stateful API
/// -------------------

noextract
let bytes = Seq.seq UInt8.t

val alg_of_state (a: G.erased alg) (s: state (G.reveal a)): Stack alg
  (requires (fun h0 -> invariant #(G.reveal a) h0 s))
  (ensures (fun h0 a' h1 ->
    a' == G.reveal a /\
    h0 == h1))

/// The API is constructed in a way that one can always get the original key
/// value behind a state, any any memory.
val as_kv: (#a: alg) -> state_s a -> GTot (kv a)

inline_for_extraction noextract
let create_in_st (a: alg) =
  r:HS.rid ->
  dst:B.pointer (B.pointer_or_null (state_s a)) ->
  k:B.buffer UInt8.t { B.length k = key_length a } ->
  ST error_code
    (requires fun h0 ->
      ST.is_eternal_region r /\
      B.live h0 k /\ B.live h0 dst)
    (ensures fun h0 e h1 ->
      match e with
      | UnsupportedAlgorithm ->
          B.(modifies loc_none h0 h1)
      | Success ->
          let s = B.deref h1 dst in
          // Sanity
          is_supported_alg a /\
          not (B.g_is_null s) /\
          invariant h1 s /\

          // Memory stuff
          B.(modifies (loc_buffer dst) h0 h1) /\
          B.fresh_loc (footprint h1 s) h0 h1 /\
          B.(loc_includes (loc_region_only true r) (footprint h1 s)) /\
          freeable h1 s /\

          // Useful stuff
          as_kv (B.deref h1 s) == B.as_seq h0 k
      | _ -> False)

/// This function takes a pointer to a caller-allocated reference ``dst`` then,
/// if the algorithm is supported, allocates a fresh state and modifies ``dst``
/// to point to it. The key-value associated with this can be obtained via ``kv
/// (B.deref dst)``; as long as ``dst`` is not modified, then the caller can
/// derive that the ``kv`` remains the same, which will be required for encrypt.
(** @type: true
*)
val create_in: #a:alg -> create_in_st a

let iv_p a = iv:B.buffer UInt8.t { iv_length (B.length iv) a }
let ad_p a = ad:B.buffer UInt8.t { B.length ad <= max_length a }
let plain_p a = p:B.buffer UInt8.t { B.length p <= max_length a }
let cipher_p a = p:B.buffer UInt8.t { B.length p + tag_length a <= max_length a }

inline_for_extraction noextract
let encrypt_st (a: supported_alg) =
  s:B.pointer_or_null (state_s a) ->
  iv:iv_p a ->
  iv_len: UInt32.t { v iv_len = B.length iv /\ v iv_len > 0 } ->
  ad:ad_p a ->
  ad_len: UInt32.t { v ad_len = B.length ad /\ v ad_len <= pow2 31 } ->
  plain: plain_p a ->
  plain_len: UInt32.t { v plain_len = B.length plain /\ v plain_len <= max_length a } ->
  cipher: B.buffer UInt8.t { B.length cipher = B.length plain } ->
  tag: B.buffer UInt8.t { B.length tag = tag_length a } ->
  Stack error_code
    (requires fun h0 ->
      not (B.g_is_null s) ==>
        invariant h0 s /\
        B.(loc_disjoint (footprint h0 s) (loc_buffer iv)) /\
        B.(loc_disjoint (footprint h0 s) (loc_buffer ad)) /\
        B.(loc_disjoint (footprint h0 s) (loc_buffer tag)) /\
        B.(loc_disjoint (footprint h0 s) (loc_buffer plain)) /\
        B.(loc_disjoint (footprint h0 s) (loc_buffer cipher)) /\
        MB.(all_live h0 [ buf iv; buf ad; buf plain; buf cipher; buf tag ]) /\
        (B.disjoint plain cipher \/ plain == cipher) /\
        B.disjoint cipher tag /\
        B.disjoint iv cipher /\ B.disjoint iv tag /\
        B.disjoint plain tag /\
        B.disjoint plain ad /\
        B.disjoint ad cipher /\ B.disjoint ad tag)
    (ensures fun h0 r h1 ->
      match r with
      | Success ->
          not (B.g_is_null s) /\
        B.(modifies (loc_union (footprint h1 s) (loc_union (loc_buffer cipher) (loc_buffer tag))) h0 h1) /\
        invariant h1 s /\
        footprint h0 s == footprint h1 s /\
          S.equal (S.append (B.as_seq h1 cipher) (B.as_seq h1 tag))
            (encrypt #a (as_kv (B.deref h0 s)) (B.as_seq h0 iv) (B.as_seq h0 ad) (B.as_seq h0 plain))
      | InvalidKey ->
          B.(modifies loc_none h0 h1)
      | _ -> False)

/// This function takes a previously expanded key and performs encryption.
///
/// Possible return values are:
/// - ``Success``: encryption was successfully performed
/// - ``InvalidKey``: the function was passed a NULL expanded key (see above)
(** @type: true
*)
val encrypt: #a:G.erased (supported_alg) -> encrypt_st (G.reveal a)

inline_for_extraction noextract
let decrypt_st (a: supported_alg) =
  s:B.pointer_or_null (state_s a) ->
  iv:iv_p a ->
  iv_len:UInt32.t { v iv_len = B.length iv /\ v iv_len > 0 } ->
  ad:ad_p a ->
  ad_len: UInt32.t { v ad_len = B.length ad /\ v ad_len <= pow2 31 } ->
  cipher: cipher_p a ->
  cipher_len: UInt32.t { v cipher_len = B.length cipher } ->
  tag: B.buffer UInt8.t { B.length tag = tag_length a } ->
  dst: B.buffer UInt8.t { B.length dst = B.length cipher } ->
  Stack error_code
    (requires fun h0 ->
      not (B.g_is_null s) ==>
        invariant h0 s /\
        B.(loc_disjoint (footprint h0 s) (loc_buffer iv)) /\
        B.(loc_disjoint (footprint h0 s) (loc_buffer ad)) /\
        B.(loc_disjoint (footprint h0 s) (loc_buffer tag)) /\
        B.(loc_disjoint (footprint h0 s) (loc_buffer dst)) /\
        B.(loc_disjoint (footprint h0 s) (loc_buffer cipher)) /\
        MB.(all_live h0 [ buf iv; buf ad; buf cipher; buf tag; buf dst ]) /\
        B.disjoint tag dst /\ B.disjoint tag cipher /\
        B.disjoint tag ad /\
        B.disjoint cipher ad /\ B.disjoint dst ad /\
        (B.disjoint cipher dst \/ cipher == dst))
    (ensures fun h0 err h1 ->
      let cipher_tag = B.as_seq h0 cipher `S.append` B.as_seq h0 tag in
      match err with
      | InvalidKey ->
          B.(modifies loc_none h0 h1)
      | Success ->
          not (B.g_is_null s) /\ (
          let plain = decrypt #a (as_kv (B.deref h0 s)) (B.as_seq h0 iv) (B.as_seq h0 ad) cipher_tag in
          B.(modifies (loc_union (footprint h1 s) (loc_buffer dst)) h0 h1) /\
          invariant h1 s /\
          footprint h0 s == footprint h1 s /\
          Some? plain /\ S.equal (Some?.v plain) (B.as_seq h1 dst))
      | AuthenticationFailure ->
          not (B.g_is_null s) /\ (
          let plain = decrypt #a (as_kv (B.deref h0 s)) (B.as_seq h0 iv) (B.as_seq h0 ad) cipher_tag in
          B.(modifies (loc_union (footprint h1 s) (loc_buffer dst)) h0 h1) /\
          invariant h1 s /\
          footprint h0 s == footprint h1 s /\
          None? plain)
      | _ ->
          False)


/// This function takes a previously expanded key and performs decryption.
///
/// Possible return values are:
/// - ``Success``: decryption was successfully performed
/// - ``InvalidKey``: the function was passed a NULL expanded key (see above)
/// - ``Failure``: cipher text could not be decrypted (e.g. tag mismatch)
(** @type: true
*)
val decrypt: #a:G.erased supported_alg -> decrypt_st (G.reveal a)

(** @type: true
*)
val free:
  #a:G.erased supported_alg -> (
  let a = Ghost.reveal a in
  s:state a -> ST unit
  (requires fun h0 ->
    freeable h0 s /\
    invariant h0 s)
  (ensures fun h0 _ h1 ->
    B.(modifies (footprint h0 s) h0 h1)))
