module EverCrypt.CTR

module ST = FStar.HyperStack.ST
module HS = FStar.HyperStack
module B = LowStar.Buffer
module G = FStar.Ghost

module Spec = Spec.Agile.CTR

open FStar.HyperStack.ST
open EverCrypt.Error

unfold noextract
let alg = Spec.cipher_alg

/// Classic boilerplate
/// -------------------

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
  [ SMTPat (invariant h1 s); SMTPat (B.modifies l h0 h1) ]

/// Ghost accessors
/// ---------------

/// We keep ghost values for the key and the iv, meaning that their value
/// doesn't depend on the heap, once we dereference past the initial pointer.
/// This should give preservation of key and iv automatically to clients.
val kv: #a:alg -> state_s a -> GTot (Spec.key a)
val iv: #a:alg -> state_s a -> GTot (Spec.nonce a)

/// ctr is mutated from call to call
val ctr: #a:alg -> h:HS.mem -> state a -> GTot Spec.ctr

/// Stateful API
/// ------------

let uint8 = Lib.IntTypes.uint8
let xor8 = Lib.IntTypes.((^.) #U8 #SEC)

let e_alg = G.erased alg

val alg_of_state: a:e_alg -> (
  let a = G.reveal a in
  s: state a -> Stack alg
  (fun h0 -> invariant h0 s)
  (fun h0 a' h1 -> h0 == h1 /\ a' == a))

inline_for_extraction noextract
let create_in_st (a:alg) =
  r:HS.rid ->
  dst:B.pointer (B.pointer_or_null (state_s a)) ->
  k:B.buffer uint8 { B.length k = Spec.Agile.CTR.key_length a } ->
  nonce: B.buffer uint8 ->
  nonce_len: UInt32.t { Spec.nonce_bound a (UInt32.v nonce_len) /\ B.len nonce = nonce_len } ->
  c: UInt32.t ->
  ST error_code
    (requires fun h0 ->
      ST.is_eternal_region r /\
      B.live h0 dst /\ B.live h0 k /\ B.live h0 nonce)
    (ensures fun h0 e h1 ->
      match e with
      | UnsupportedAlgorithm ->
          B.(modifies loc_none h0 h1)
      | InvalidIVLength ->
          B.(modifies loc_none h0 h1) /\ UInt32.v nonce_len < 12
      | Success ->
          let s = B.deref h1 dst in
          // Sanity
          not (B.g_is_null s) /\
          invariant h1 s /\

          // Memory stuff
          B.(modifies (loc_buffer dst) h0 h1) /\
          B.fresh_loc (footprint h1 s) h0 h1 /\
          B.(loc_includes (loc_region_only true r) (footprint h1 s)) /\
          freeable h1 s /\

          // Useful stuff
          kv (B.deref h1 s) == B.as_seq h0 k /\
          iv (B.deref h1 s) == B.as_seq h0 nonce /\
          ctr h1 s = UInt32.v c
      | _ -> False)

val create_in: a:alg -> create_in_st a

/// Initializes state to start at a given counter. This allows client to
/// generate a counter-block directly for a given counter, or to just start at
/// zero and do encryption block-by-block. Note that we use a C-like API where
/// the length comes after the buffer.
val init: a:e_alg -> (
  let a = G.reveal a in
  s:state a ->
  k:B.buffer uint8 { B.length k = Spec.Agile.CTR.key_length a } ->
  nonce: B.buffer uint8 ->
  nonce_len: UInt32.t { Spec.nonce_bound a (UInt32.v nonce_len) /\ B.len nonce = nonce_len } ->
  c: UInt32.t ->
  Stack unit
    (requires (fun h0 ->
      B.live h0 k /\
      B.live h0 nonce /\
      B.(loc_disjoint (loc_buffer k) (footprint h0 s)) /\
      B.(loc_disjoint (loc_buffer nonce) (footprint h0 s)) /\
      invariant h0 s))
    (ensures (fun h0 _ h1 ->
      preserves_freeable #a s h0 h1 /\
      invariant #a h1 s /\
      footprint h0 s == footprint #a h1 s /\
      B.(modifies (footprint #a h0 s) h0 h1) /\
      kv (B.deref h1 s) == B.as_seq h0 k /\
      iv (B.deref h1 s) == B.as_seq h0 nonce /\
      ctr h1 s = UInt32.v c
      )))

/// Process exactly one block, incrementing the counter contained in the state
/// in passing. The expected usage is repeated calls to update_block as more
/// data comes in, followed by a call to update_last.
inline_for_extraction noextract
let update_block_st (a: alg) =
  s:state a ->
  dst:B.buffer uint8 { B.length dst = Spec.block_length a } ->
  src:B.buffer uint8 { B.length src = Spec.block_length a } ->
  Stack unit
    (requires (fun h0 ->
      B.live h0 src /\ B.live h0 dst /\
      B.(loc_disjoint (loc_buffer src) (footprint h0 s)) /\
      B.(loc_disjoint (loc_buffer dst) (footprint h0 s)) /\
      B.disjoint src dst /\
      invariant h0 s))
    (ensures (fun h0 _ h1 ->
      preserves_freeable s h0 h1 /\
      invariant h1 s /\
      B.(modifies (footprint_s (B.deref h0 s) `loc_union` loc_buffer dst) h0 h1) /\
      footprint h0 s == footprint h1 s /\
      (ctr h0 s < pow2 32 - 1 ==> ctr h1 s == ctr h0 s + 1) /\
      B.as_seq h1 dst == Spec.Loops.seq_map2 xor8 (B.as_seq h0 src)
        (Spec.ctr_block a (kv (B.deref h0 s)) (iv (B.deref h0 s)) (ctr h0 s))))

val update_block: a:e_alg -> update_block_st (G.reveal a)

// TODO: update_blocks, update_last... then an incremental API for CTR encryption.

val free: a:e_alg -> (
  let a = G.reveal a in
  s:state a ->
  ST unit
    (requires (fun h0 ->
      freeable h0 s /\
      invariant h0 s))
    (ensures (fun h0 _ h1 ->
      B.(modifies (footprint h0 s) h0 h1))))
