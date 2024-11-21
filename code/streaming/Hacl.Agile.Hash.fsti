module Hacl.Agile.Hash

open FStar.HyperStack.ST
open FStar.Integers
open Spec.Hash.Definitions
open Hacl.Hash.Definitions

module HS = FStar.HyperStack
module B = LowStar.Buffer
module M = LowStar.Modifies
module G = FStar.Ghost

open LowStar.BufferOps

#set-options "--max_fuel 0 --max_ifuel 0 --z3rlimit 100"

/// This module largely follows EverCrypt.Hash, but with the caveat that it is
/// indexed over an implementation rather than a choice of algorithm. This means
/// that it is up to the caller (presumably, in C), to determine what is the
/// best choice of implementation for their target platform.
///
/// This follows a rather plain realization: most libraries want to handle CPU
/// auto-detection themselves, and as such, modules like EverCrypt.Hash, in
/// spite of being conceptually very cool (tm), never met any real-world
/// adoption.

inline_for_extraction noextract
val _sync_decl: unit

let is_valid_impl (i: impl) =
  let open Hacl.Impl.Blake2.Core in
  match i with
  | (| MD5, () |)
  | (| SHA1, () |)
  | (| SHA2_224, () |)
  | (| SHA2_256, () |)
  | (| SHA2_384, () |)
  | (| SHA2_512, () |)
  | (| SHA3_224, () |)
  | (| SHA3_256, () |)
  | (| SHA3_384, () |)
  | (| SHA3_512, () |)
  | (| Blake2S, M32 |)
  | (| Blake2S, M128 |)
  | (| Blake2B, M32 |)
  | (| Blake2B, M256 |) -> true
  | _ -> false

let impl = i:impl { is_valid_impl i }
let e_impl = G.erased impl

let state_s (i: impl) = EverCrypt.Hash.state_s (dfst i)
let state (i: impl) = EverCrypt.Hash.state (dfst i)

inline_for_extraction noextract
val freeable_s: #(i: impl) -> state_s i -> Type0

inline_for_extraction noextract
let freeable (#a: impl) (h: HS.mem) (p: state a) =
  B.freeable p /\ freeable_s (B.deref h p)

val footprint_s: #a:impl -> state_s a -> GTot M.loc
let footprint (#a:impl) (s: state a) (m: HS.mem) =
  M.(loc_union (loc_addr_of_buffer s) (footprint_s (B.deref m s)))

let loc_includes_union_l_footprint_s
  (l1 l2: M.loc) (#a: impl) (s: state_s a)
: Lemma
  (requires (
    M.loc_includes l1 (footprint_s s) \/ M.loc_includes l2 (footprint_s s)
  ))
  (ensures (M.loc_includes (M.loc_union l1 l2) (footprint_s s)))
  [SMTPat (M.loc_includes (M.loc_union l1 l2) (footprint_s s))]
= M.loc_includes_union_l l1 l2 (footprint_s s)

inline_for_extraction noextract
val invariant_s: (#a:impl) -> state_s a -> HS.mem -> Type0

inline_for_extraction noextract
let invariant (#a:impl) (s: state a) (m: HS.mem) =
  B.live m s /\
  M.(loc_disjoint (loc_addr_of_buffer s) (footprint_s (B.deref m s))) /\
  invariant_s (B.get m s 0) m

val repr: #a:impl ->
  s:state a -> h:HS.mem -> GTot (words_state (dfst a))

val alg_of_state: a:e_impl -> (
  let a = G.reveal a in
  s: state a -> Stack impl
  (fun h0 -> invariant s h0)
  (fun h0 a' h1 -> h0 == h1 /\ a' == a))

val fresh_is_disjoint: l1:M.loc -> l2:M.loc -> h0:HS.mem -> h1:HS.mem -> Lemma
  (requires (B.fresh_loc l1 h0 h1 /\ l2 `B.loc_in` h0))
  (ensures (M.loc_disjoint l1 l2))

val invariant_loc_in_footprint
  (#a: impl)
  (s: state a)
  (m: HS.mem)
: Lemma
  (requires (invariant s m))
  (ensures (B.loc_in (footprint s m) m))
  [SMTPat (invariant s m)]

val frame_invariant: #a:impl -> l:M.loc -> s:state a -> h0:HS.mem -> h1:HS.mem -> Lemma
  (requires (
    invariant s h0 /\
    M.loc_disjoint l (footprint s h0) /\
    M.modifies l h0 h1))
  (ensures (
    invariant s h1 /\
    repr s h0 == repr s h1))

let frame_invariant_implies_footprint_preservation
  (#a: impl)
  (l: M.loc)
  (s: state a)
  (h0 h1: HS.mem): Lemma
  (requires (
    invariant s h0 /\
    M.loc_disjoint l (footprint s h0) /\
    M.modifies l h0 h1))
  (ensures (
    footprint s h1 == footprint s h0))
=
  ()

inline_for_extraction noextract
let preserves_freeable #a (s: state a) (h0 h1: HS.mem): Type0 =
  freeable h0 s ==> freeable h1 s

/// This function will generally not extract properly, so it should be used with
/// great care. Callers must:
/// - run with evercrypt/fst in scope to benefit from the definition of this function
/// - know, at call-site, the concrete value of a via suitable usage of inline_for_extraction
inline_for_extraction noextract
val alloca: a:impl -> StackInline (state a)
  (requires (fun _ -> True))
  (ensures (fun h0 s h1 ->
    invariant s h1 /\
    M.(modifies loc_none h0 h1) /\
    B.fresh_loc (footprint s h1) h0 h1 /\
    M.(loc_includes (loc_region_only true (HS.get_tip h1)) (footprint s h1))))

(** @type: true
*)
val create_in: a:impl -> r:HS.rid -> ST (state a)
  (requires (fun _ ->
    HyperStack.ST.is_eternal_region r))
  (ensures (fun h0 s h1 ->
    invariant s h1 /\
    M.(modifies loc_none h0 h1) /\
    B.fresh_loc (footprint s h1) h0 h1 /\
    M.(loc_includes (loc_region_only true r) (footprint s h1)) /\
    freeable h1 s))

(** @type: true
*)
val create: a:impl -> ST (state a)
  (requires fun h0 -> True)
  (ensures fun h0 s h1 ->
    invariant s h1 /\
    M.(modifies loc_none h0 h1) /\
    B.fresh_loc (footprint s h1) h0 h1 /\
    freeable h1 s)

(** @type: true
*)
val init: #a:e_impl -> (
  let a = Ghost.reveal a in
  s: state a -> Stack unit
  (requires invariant s)
  (ensures fun h0 _ h1 ->
    invariant s h1 /\
    repr s h1 == Spec.Agile.Hash.init (dfst a) /\
    M.(modifies (footprint s h0) h0 h1) /\
    footprint s h0 == footprint s h1 /\
    preserves_freeable s h0 h1))

inline_for_extraction noextract
let ev_of_uint64 a (prevlen: UInt64.t { UInt64.v prevlen % block_length a = 0 }): Spec.Hash.Definitions.extra_state a =
  (if is_blake a then UInt64.v prevlen else ())

(** @type: true
*)
val update_multi:
  #a:e_impl -> (
  let a = Ghost.reveal a in
  s:state a ->
  prevlen : UInt64.t { UInt64.v prevlen % block_length (dfst a) = 0 } ->
  blocks:B.buffer Lib.IntTypes.uint8 { B.length blocks % block_length (dfst a) = 0 } ->
  len: UInt32.t { v len = B.length blocks } ->
  Stack unit
  (requires fun h0 ->
    invariant s h0 /\
    B.live h0 blocks /\
    Spec.Agile.Hash.update_multi_pre (dfst a) (ev_of_uint64 (dfst a) prevlen) (B.as_seq h0 blocks) /\
    M.(loc_disjoint (footprint s h0) (loc_buffer blocks)))
  (ensures fun h0 _ h1 ->
    M.(modifies (footprint s h0) h0 h1) /\
    footprint s h0 == footprint s h1 /\
    invariant s h1 /\
    repr s h1 == Spec.Agile.Hash.update_multi (dfst a) (repr s h0)
      (ev_of_uint64 (dfst a) prevlen) (B.as_seq h0 blocks) /\
    preserves_freeable s h0 h1))

inline_for_extraction noextract
let prev_len_of_uint64 a (prevlen: UInt64.t { UInt64.v prevlen % block_length a = 0 }): Spec.Hash.Incremental.prev_length_t a =
  (if is_keccak a then () else UInt64.v prevlen)

(** @type: true
*)
val update_last:
  #a:e_impl -> (
  let a = Ghost.reveal a in
  s:state a ->
  prev_len:UInt64.t ->
  last:B.buffer Lib.IntTypes.uint8 { B.length last <= block_length (dfst a) } ->
  last_len:UInt32.t {
    v last_len = B.length last /\
    (v prev_len + v last_len) `less_than_max_input_length` (dfst a) /\
    v prev_len % block_length (dfst a) = 0 } ->
  Stack unit
  (requires fun h0 ->
    invariant s h0 /\
    B.live h0 last /\
    Spec.Agile.Hash.update_multi_pre (dfst a) (ev_of_uint64 (dfst a) prev_len) (B.as_seq h0 last) /\
    M.(loc_disjoint (footprint s h0) (loc_buffer last)))
  (ensures fun h0 _ h1 ->
    invariant s h1 /\
    repr s h1 ==
      Spec.Hash.Incremental.update_last (dfst a) (repr s h0) (prev_len_of_uint64 (dfst a) prev_len)
                                             (B.as_seq h0 last) /\
    M.(modifies (footprint s h0) h0 h1) /\
    footprint s h0 == footprint s h1 /\
    preserves_freeable s h0 h1))

(** @type: true
*)
val finish:
  #a:e_impl -> (
  let a = Ghost.reveal a in
  s:state a ->
  dst:B.buffer Lib.IntTypes.uint8 { B.length dst = hash_length (dfst a) } ->
  Stack unit
  (requires fun h0 ->
    invariant s h0 /\
    B.live h0 dst /\
    M.(loc_disjoint (footprint s h0) (loc_buffer dst)))
  (ensures fun h0 _ h1 ->
    invariant s h1 /\
    M.(modifies (loc_buffer dst `loc_union` footprint s h0) h0 h1) /\
    footprint s h0 == footprint s h1 /\
    B.as_seq h1 dst == Spec.Agile.Hash.finish (dfst a) (repr s h0) () /\
    preserves_freeable s h0 h1))

(** @type: true
*)
val free_:
  #a:e_impl -> (
  let a = Ghost.reveal a in
  s:state a -> ST unit
  (requires fun h0 ->
    freeable h0 s /\
    invariant s h0)
  (ensures fun h0 _ h1 ->
    M.(modifies (footprint s h0) h0 h1)))

// Avoids C-level collisions with the stdlib free.
// Not clear why we need to repeat the type annotation.
inline_for_extraction noextract
let free: #a:e_impl -> (
  let a = Ghost.reveal a in
  s:state a -> ST unit
  (requires fun h0 ->
    freeable h0 s /\
    invariant s h0)
  (ensures fun h0 _ h1 ->
    M.(modifies (footprint s h0) h0 h1)))
 = free_

(** @type: true
*)
val copy:
  #a:e_impl -> (
  let a = Ghost.reveal a in
  s_src:state a ->
  s_dst:state a ->
  Stack unit
    (requires (fun h0 ->
      invariant s_src h0 /\
      invariant s_dst h0 /\
      B.(loc_disjoint (footprint s_src h0) (footprint s_dst h0))))
    (ensures fun h0 _ h1 ->
      M.(modifies (footprint s_dst h0) h0 h1) /\
      footprint s_dst h0 == footprint s_dst h1 /\
      preserves_freeable s_dst h0 h1 /\
      invariant s_dst h1 /\
      repr s_dst h1 == repr s_src h0))
