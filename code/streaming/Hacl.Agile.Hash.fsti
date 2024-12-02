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

/// A corollary is that we need the type of implementations to be representable,
/// instead of being a meta-time parameter that is evaluated away. The `impl`
/// dependent pair in Hash.Definitions is thus ill-suited.

inline_for_extraction noextract
val _sync_decl1: unit

type impl =
  | MD5
  | SHA1
  | SHA2_224
  | SHA2_256
  | SHA2_384
  | SHA2_512
  | SHA3_224
  | SHA3_256
  | SHA3_384
  | SHA3_512
  | Blake2S_32
  | Blake2S_128
  | Blake2B_32
  | Blake2B_256

inline_for_extraction noextract
val _sync_decl2: unit

let alg_of_impl (i: impl): fixed_len_alg =
  let _ = allow_inversion impl in
  match i with
  | MD5 -> Spec.Agile.Hash.MD5
  | SHA1 -> Spec.Agile.Hash.SHA1
  | SHA2_224 -> Spec.Agile.Hash.SHA2_224
  | SHA2_256 -> Spec.Agile.Hash.SHA2_256
  | SHA2_384 -> Spec.Agile.Hash.SHA2_384
  | SHA2_512 -> Spec.Agile.Hash.SHA2_512
  | SHA3_224 -> Spec.Agile.Hash.SHA3_224
  | SHA3_256 -> Spec.Agile.Hash.SHA3_256
  | SHA3_384 -> Spec.Agile.Hash.SHA3_384
  | SHA3_512 -> Spec.Agile.Hash.SHA3_512
  | Blake2S_32 -> Spec.Agile.Hash.Blake2S
  | Blake2S_128 -> Spec.Agile.Hash.Blake2S
  | Blake2B_32 -> Spec.Agile.Hash.Blake2B
  | Blake2B_256 -> Spec.Agile.Hash.Blake2B

let e_impl = G.erased impl

[@CAbstractStruct]
val state_s: (i: impl) -> Type0
let state alg = B.pointer (state_s alg)

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
  s:state a -> h:HS.mem -> GTot (words_state (alg_of_impl a))

val impl_of_state: a:e_impl -> (
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

[@@ Comment "Returns NULL if the choice of implemenatation is not supported on
the target platform. For instance, attempting to create a Blake2B_256 HMAC on an
ARM machine will fail."]
val malloc_in: a:impl -> r:HS.rid -> FStar.HyperStack.ST.ST (B.buffer (state_s a))
  (requires (fun _ ->
    HyperStack.ST.is_eternal_region r))
  (ensures (fun h0 s h1 ->
    if a = Blake2S_128 && not EverCrypt.TargetConfig.hacl_can_compile_vec128 ||
      a = Blake2B_256 && not EverCrypt.TargetConfig.hacl_can_compile_vec256
    then
      s == B.null
    else
      B.length s == 1 /\ // this turns the result type into state a
      invariant s h1 /\
      M.(modifies loc_none h0 h1) /\
      B.fresh_loc (footprint s h1) h0 h1 /\
      M.(loc_includes (loc_region_only true r) (footprint s h1)) /\
      freeable h1 s))

(** @type: true
*)
val malloc: a:impl -> FStar.HyperStack.ST.ST (B.buffer (state_s a))
  (requires fun h0 -> True)
  (ensures fun h0 s h1 ->
    if a = Blake2S_128 && not EverCrypt.TargetConfig.hacl_can_compile_vec128 ||
      a = Blake2B_256 && not EverCrypt.TargetConfig.hacl_can_compile_vec256
    then
      s == B.null
    else
      B.length s == 1 /\ // this turns the result type into state a
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
    repr s h1 == Spec.Agile.Hash.init (alg_of_impl a) /\
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
  prevlen : UInt64.t { UInt64.v prevlen % block_length (alg_of_impl a) = 0 } ->
  blocks:B.buffer Lib.IntTypes.uint8 { B.length blocks % block_length (alg_of_impl a) = 0 } ->
  len: UInt32.t { v len = B.length blocks } ->
  Stack unit
  (requires fun h0 ->
    invariant s h0 /\
    B.live h0 blocks /\
    Spec.Agile.Hash.update_multi_pre (alg_of_impl a) (ev_of_uint64 (alg_of_impl a) prevlen) (B.as_seq h0 blocks) /\
    M.(loc_disjoint (footprint s h0) (loc_buffer blocks)))
  (ensures fun h0 _ h1 ->
    M.(modifies (footprint s h0) h0 h1) /\
    footprint s h0 == footprint s h1 /\
    invariant s h1 /\
    repr s h1 == Spec.Agile.Hash.update_multi (alg_of_impl a) (repr s h0)
      (ev_of_uint64 (alg_of_impl a) prevlen) (B.as_seq h0 blocks) /\
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
  last:B.buffer Lib.IntTypes.uint8 { B.length last <= block_length (alg_of_impl a) } ->
  last_len:UInt32.t {
    v last_len = B.length last /\
    (v prev_len + v last_len) `less_than_max_input_length` (alg_of_impl a) /\
    v prev_len % block_length (alg_of_impl a) = 0 } ->
  Stack unit
  (requires fun h0 ->
    invariant s h0 /\
    B.live h0 last /\
    Spec.Agile.Hash.update_multi_pre (alg_of_impl a) (ev_of_uint64 (alg_of_impl a) prev_len) (B.as_seq h0 last) /\
    M.(loc_disjoint (footprint s h0) (loc_buffer last)))
  (ensures fun h0 _ h1 ->
    invariant s h1 /\
    repr s h1 ==
      Spec.Hash.Incremental.update_last (alg_of_impl a) (repr s h0) (prev_len_of_uint64 (alg_of_impl a) prev_len)
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
  dst:B.buffer Lib.IntTypes.uint8 { B.length dst = hash_length (alg_of_impl a) } ->
  Stack unit
  (requires fun h0 ->
    invariant s h0 /\
    B.live h0 dst /\
    M.(loc_disjoint (footprint s h0) (loc_buffer dst)))
  (ensures fun h0 _ h1 ->
    invariant s h1 /\
    M.(modifies (loc_buffer dst `loc_union` footprint s h0) h0 h1) /\
    footprint s h0 == footprint s h1 /\
    B.as_seq h1 dst == Spec.Agile.Hash.finish (alg_of_impl a) (repr s h0) () /\
    preserves_freeable s h0 h1))

(** @type: true
*)
val free_:
  #a:e_impl -> (
  let a = Ghost.reveal a in
  s:state a -> FStar.HyperStack.ST.ST unit
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
  s:state a -> FStar.HyperStack.ST.ST unit
  (requires fun h0 ->
    freeable h0 s /\
    invariant s h0)
  (ensures fun h0 _ h1 ->
    M.(modifies (footprint s h0) h0 h1)))
 = free_

[@ Comment "Warning: this function cannot copy across implementations of the
same algorithm. Therefore, you must make sure that you do not attempt to copy,
say, a Blake2B_32 state into a Blake2B_256 or vice-versa. This typically happens
if the CPU run-time detection code on the client side executes after state
creation, leading to a non-SIMD state being created, and later on, SIMD states
appearing for the same algorithm." ]
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
