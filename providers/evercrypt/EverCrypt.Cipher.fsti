module EverCrypt.Cipher

module ST = FStar.HyperStack.ST
module HS = FStar.HyperStack
module B = LowStar.Buffer
module G = FStar.Ghost

module Spec = Spec.Agile.Cipher

open FStar.HyperStack.ST

unfold noextract
let alg = Spec.Agile.Cipher.cipher_alg

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

/// Ghost accessors
/// ---------------

/// TODO: unify this definition with the ones in Spec.AEAD
let kv a = Lib.ByteSequence.lbytes (Spec.key_len a)

val as_kv: #a:alg -> state_s a -> GTot (kv a)

val repr: #a:alg -> h:HS.mem -> state a -> GTot (Spec.state a)

// MISSING
val ctr: #a:alg -> s:Spec.state a -> nat

/// Stateful API
/// ------------

open Lib.Buffer
open Lib.IntTypes

let e_alg = G.erased alg

val alg_of_state: a:e_alg -> (
  let a = G.reveal a in
  s: state a -> Stack alg
  (fun h0 -> invariant h0 s)
  (fun h0 a' h1 -> h0 == h1 /\ a' == a))

val create_in (a: alg) (r: HS.rid): ST (state a)
  (requires (fun _ ->
    HyperStack.ST.is_eternal_region r))
  (ensures (fun h0 s h1 ->
    invariant h1 s /\
    B.(modifies loc_none h0 h1) /\
    B.fresh_loc (footprint h1 s) h0 h1 /\
    B.(loc_includes (loc_region_only true r) (footprint h1 s)) /\
    freeable h1 s))

/// Resets an existing state to have counter 0.
val init: a:e_alg -> (
  let a = G.reveal a in
  s:state a ->
  key: lbuffer uint8 (size (Spec.key_len a)) ->
  nonce: buffer uint8 ->
  nonce_len: UInt32.t { Spec.nonce_bound a (UInt32.v nonce_len) /\ B.len nonce = nonce_len } ->
  Stack unit
    (requires (fun h0 ->
      live h0 key /\
      live h0 nonce /\
      B.loc_disjoint (loc key) (footprint h0 s) /\
      B.loc_disjoint (loc nonce) (footprint h0 s) /\
      invariant h0 s))
    (ensures (fun h0 _ h1 ->
      preserves_freeable #a s h0 h1 /\
      invariant #a h1 s /\
      footprint h0 s == footprint #a h1 s /\
      B.(modifies (footprint #a h0 s) h0 h1) /\
      repr #a h1 s == Spec.Agile.Cipher.init a (as_seq h0 key)
        (UInt32.v nonce_len) (B.as_seq h0 nonce) 0
      )))

/// Process exactly one block, incrementing the counter contained in the state
/// in passing. The expected usage is repeated calls to update_block as more
/// data comes in, followed by a call to update_last.
val update_block: a:e_alg -> (
  let a = G.reveal a in
  s:state a ->
  dst:lbuffer uint8 (size (Spec.block_len a)) ->
  src:lbuffer uint8 (size (Spec.block_len a)) ->
  Stack unit
    (requires (fun h0 ->
      B.loc_disjoint (loc src) (footprint h0 s) /\
      B.loc_disjoint (loc dst) (footprint h0 s) /\
      disjoint src dst /\
      invariant h0 s /\
      ctr (repr h0 s) < pow2 32 - 1))
    (ensures (fun h0 _ h1 ->
      preserves_freeable s h0 h1 /\
      invariant h1 s /\
      B.(modifies (footprint h0 s) h0 h1) /\
      footprint h0 s == footprint h1 s /\
      repr h1 s == Spec.add_counter a (repr h0 s) 1 /\
      as_seq h1 dst ==
        Spec.Agile.CTR.process_block a (repr h0 s) (ctr (repr h0 s)) (as_seq h0 src))))

// TODO: update_blocks, update_last

/// For custom clients, e.g. libquiccrypto: does not modify the state in place and allows directly passing a custom value for the counter.
val single_block: a:e_alg -> (
  let a = G.reveal a in
  s:state a ->
  dst:lbuffer uint8 (size (Spec.block_len a)) ->
  src:lbuffer uint8 (size (Spec.block_len a)) ->
  c:UInt32.t ->
  Stack unit
    (requires (fun h0 ->
      B.loc_disjoint (loc src) (footprint h0 s) /\
      B.loc_disjoint (loc dst) (footprint h0 s) /\
      disjoint src dst /\
      invariant h0 s /\
      ctr (repr h0 s) + UInt32.v c <= pow2 32 - 1))
    (ensures (fun h0 _ h1 ->
      preserves_freeable s h0 h1 /\
      invariant h1 s /\
      B.(modifies (footprint h0 s) h0 h1) /\
      footprint h0 s == footprint h1 s /\
      repr h1 s == repr h0 s /\
      as_seq h1 dst ==
        Spec.Agile.CTR.process_block a (repr h0 s) (ctr (repr h0 s) + UInt32.v c) (as_seq h0 src))))

// TODO: perhaps it's not much use having update_block. What we could do instead
// which would be more general is to offer i) single_block (which does not
// modify the underlying state) and ii) increment_counter (which modifies the
// state). This way, custom clients like libquiccrypt would just use single
// block, and the module above this one (EverCrypt.Cipher.Incremental) could
// take care of incrementing the counter whenever a full block has been
// processed.
