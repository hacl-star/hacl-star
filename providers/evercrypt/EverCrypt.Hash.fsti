module EverCrypt.Hash

open EverCrypt.Helpers
open FStar.HyperStack.ST
open FStar.Integers
open Spec.Hash.Definitions
open Hacl.Hash.Definitions

#set-options "--max_fuel 0 --max_ifuel 0 --z3rlimit 100"

/// Algorithmic agility for hash specifications. We reuse the agile
/// specifications from HACL*'s specs/ directory.

/// SUPPORTED ALGORITHMS see e.g. https://en.wikipedia.org/wiki/SHA-1
/// for a global comparison and lengths
///
/// * We support all variants of SHA2.
/// * MD5 and SHA1 are still required by TLS 1.2, included for legacy
///   purpose only
/// * SHA3 will be provided by HACL*
///
/// ``hash_alg``, from Spec.Hash.Definitions, lists all supported algorithms
unfold
let alg = hash_alg

/// TODO: move this one to Hacl.Hash.Definitions
val string_of_alg: alg -> C.String.t

/// kept only for functional backward compatibility, never assumed to be secure
type broken_alg = a:alg {a = MD5 \/ a = SHA1}

/// HMAC/HKDF ALGORITHMS; we make security assumptions only for constructions
/// based on those.
type alg13 = a:alg { a=SHA2_256 \/ a=SHA2_384 \/ a=SHA2_512 }

/// No pattern (would fire too often)!
let uint32_fits_maxLength (a: alg) (x: UInt32.t): Lemma
  (requires True)
  (ensures UInt32.v x <= max_input_length a)
=
  assert_norm (pow2 32 < pow2 61);
  assert_norm (pow2 61 < pow2 125)

/// To specify their low-level incremental computations, we assume
/// Merkle-Damgard/sponge-like algorithms:
///
/// The hash state is kept in an accumulator, with
/// - an initial value
/// - an update function, adding a block of bytes;
/// - an extract (also: "finish") function, returning a hash tag.
///
/// Before hashing, some algorithm-specific padding and length encoding is
/// appended to the input bytestring.
///
/// This is not a general-purpose incremental specification, which would support
/// adding text fragments of arbitrary lengths (for that, see
/// EverCrypt.Hash.Incremental).


/// Stateful interface implementing the agile specifications.

module HS = FStar.HyperStack
module B = LowStar.Buffer
module M = LowStar.Modifies
module G = FStar.Ghost

open LowStar.BufferOps

/// do not use as argument of ghost functions
type e_alg = G.erased alg

// abstract implementation state
[@CAbstractStruct]
val state_s: alg -> Type0

// pointer to abstract implementation state
let state alg = b:B.pointer (state_s alg)

// abstract freeable (deep) predicate; only needed for create/free pairs
val freeable_s: #(a: alg) -> state_s a -> Type0

let freeable (#a: alg) (h: HS.mem) (p: state a) =
  B.freeable p /\ freeable_s (B.deref h p)

// NS: note that the state is the first argument to the invariant so that we can
// do partial applications in pre- and post-conditions
val footprint_s: #a:alg -> state_s a -> GTot M.loc
let footprint (#a:alg) (s: state a) (m: HS.mem) =
  M.(loc_union (loc_addr_of_buffer s) (footprint_s (B.deref m s)))

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
  (l1 l2: M.loc) (#a: alg) (s: state_s a)
: Lemma
  (requires (
    M.loc_includes l1 (footprint_s s) \/ M.loc_includes l2 (footprint_s s)
  ))
  (ensures (M.loc_includes (M.loc_union l1 l2) (footprint_s s)))
  [SMTPat (M.loc_includes (M.loc_union l1 l2) (footprint_s s))]
= M.loc_includes_union_l l1 l2 (footprint_s s)

val invariant_s: (#a:alg) -> state_s a -> HS.mem -> Type0
let invariant (#a:alg) (s: state a) (m: HS.mem) =
  B.live m s /\
  M.(loc_disjoint (loc_addr_of_buffer s) (footprint_s (B.deref m s))) /\
  invariant_s (B.get m s 0) m

//18-07-06 as_acc a better name? not really a representation
val repr: #a:alg ->
  s:state a -> h:HS.mem -> GTot (words_state a)

val alg_of_state: a:e_alg -> (
  let a = G.reveal a in
  s: state a -> Stack alg
  (fun h0 -> invariant s h0)
  (fun h0 a' h1 -> h0 == h1 /\ a' == a))

val fresh_is_disjoint: l1:M.loc -> l2:M.loc -> h0:HS.mem -> h1:HS.mem -> Lemma
  (requires (B.fresh_loc l1 h0 h1 /\ l2 `B.loc_in` h0))
  (ensures (M.loc_disjoint l1 l2))

// TR: this lemma is necessary to prove that the footprint is disjoint
// from any fresh memory location.

val invariant_loc_in_footprint
  (#a: alg)
  (s: state a)
  (m: HS.mem)
: Lemma
  (requires (invariant s m))
  (ensures (B.loc_in (footprint s m) m))
  [SMTPat (invariant s m)]

// TR: frame_invariant, just like all lemmas eliminating `modifies`
// clauses, should have `modifies_inert` as a precondition instead of
// `modifies`, in order to use it in all cases where a modifies clause
// is produced but should not be composed with `modifies_trans` for
// pattern reasons (e.g. push_frame, pop_frame)

// 18-07-12 why not bundling the next two lemmas?
val frame_invariant: #a:alg -> l:M.loc -> s:state a -> h0:HS.mem -> h1:HS.mem -> Lemma
  (requires (
    invariant s h0 /\
    M.loc_disjoint l (footprint s h0) /\
    M.modifies l h0 h1))
  (ensures (
    invariant s h1 /\
    repr s h0 == repr s h1))

let frame_invariant_implies_footprint_preservation
  (#a: alg)
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

let preserves_freeable #a (s: state a) (h0 h1: HS.mem): Type0 =
  freeable h0 s ==> freeable h1 s

/// This function will generally not extract properly, so it should be used with
/// great care. Callers must:
/// - run with evercrypt/fst in scope to benefit from the definition of this function
/// - know, at call-site, the concrete value of a via suitable usage of inline_for_extraction
inline_for_extraction noextract
val alloca: a:alg -> StackInline (state a)
  (requires (fun _ -> True))
  (ensures (fun h0 s h1 ->
    invariant s h1 /\
    M.(modifies loc_none h0 h1) /\
    B.fresh_loc (footprint s h1) h0 h1 /\
    M.(loc_includes (loc_region_only true (HS.get_tip h1)) (footprint s h1))))

(** @type: true
*)
val create_in: a:alg -> r:HS.rid -> ST (state a)
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
val create: a:alg -> ST (state a)
  (requires fun h0 -> True)
  (ensures fun h0 s h1 ->
    invariant s h1 /\
    M.(modifies loc_none h0 h1) /\
    B.fresh_loc (footprint s h1) h0 h1 /\
    freeable h1 s)

(** @type: true
*)
val init: #a:e_alg -> (
  let a = Ghost.reveal a in
  s: state a -> Stack unit
  (requires invariant s)
  (ensures fun h0 _ h1 ->
    invariant s h1 /\
    repr s h1 == Spec.Agile.Hash.init a /\
    M.(modifies (footprint s h0) h0 h1) /\
    footprint s h0 == footprint s h1 /\
    preserves_freeable s h0 h1))

val update_multi_256: Hacl.Hash.Definitions.update_multi_st SHA2_256

inline_for_extraction noextract
val update_multi_224: Hacl.Hash.Definitions.update_multi_st SHA2_224

// Note: this function relies implicitly on the fact that we are running with
// code/lib/kremlin and that we know that machine integers and secret integers
// are the same. In the long run, we should standardize on a secret integer type
// in F*'s ulib and have evercrypt use it.
(** @type: true
*)
val update:
  #a:e_alg -> (
  let a = Ghost.reveal a in
  s:state a ->
  block:B.buffer Lib.IntTypes.uint8 { B.length block = block_length a } ->
  Stack unit
  (requires fun h0 ->
    invariant s h0 /\
    B.live h0 block /\
    M.(loc_disjoint (footprint s h0) (loc_buffer block)))
  (ensures fun h0 _ h1 ->
    M.(modifies (footprint s h0) h0 h1) /\
    footprint s h0 == footprint s h1 /\
    invariant s h1 /\
    repr s h1 == Spec.Agile.Hash.update a (repr s h0) (B.as_seq h0 block) /\
    preserves_freeable s h0 h1))

// Note that we pass the data length in bytes (rather than blocks).
(** @type: true
*)
val update_multi:
  #a:e_alg -> (
  let a = Ghost.reveal a in
  s:state a ->
  blocks:B.buffer Lib.IntTypes.uint8 { B.length blocks % block_length a = 0 } ->
  len: UInt32.t { v len = B.length blocks } ->
  Stack unit
  (requires fun h0 ->
    invariant s h0 /\
    B.live h0 blocks /\
    M.(loc_disjoint (footprint s h0) (loc_buffer blocks)))
  (ensures fun h0 _ h1 ->
    M.(modifies (footprint s h0) h0 h1) /\
    footprint s h0 == footprint s h1 /\
    invariant s h1 /\
    repr s h1 == Spec.Agile.Hash.update_multi a (repr s h0) (B.as_seq h0 blocks) /\
    preserves_freeable s h0 h1))

val update_last_256: Hacl.Hash.Definitions.update_last_st SHA2_256

inline_for_extraction noextract
val update_last_224: Hacl.Hash.Definitions.update_last_st SHA2_224

// 18-03-05 note the *new* length-passing convention!
// 18-03-03 it is best to let the caller keep track of lengths.
// 18-03-03 the last block is *never* complete so there is room for the 1st byte of padding.
// 18-10-10 using uint64 for the length as the is the only thing that TLS needs
//   and also saves the need for a (painful) indexed type
// 18-10-15 a crucial bit is that this function reveals that last @| padding is a multiple of the
//   block size; indeed, any caller will want to know this in order to reason
//   about that sequence concatenation
(** @type: true
*)
val update_last:
  #a:e_alg -> (
  let a = Ghost.reveal a in
  s:state a ->
  last:B.buffer Lib.IntTypes.uint8 { B.length last < block_length a } ->
  total_len:uint64_t {
    v total_len <= max_input_length a /\
    (v total_len - B.length last) % block_length a = 0 } ->
  Stack unit
  (requires fun h0 ->
    invariant s h0 /\
    B.live h0 last /\
    M.(loc_disjoint (footprint s h0) (loc_buffer last)))
  (ensures fun h0 _ h1 ->
    invariant s h1 /\
    (B.length last + Seq.length (Spec.Hash.PadFinish.pad a (v total_len))) % block_length a = 0 /\
    repr s h1 ==
      Spec.Agile.Hash.update_multi a (repr s h0)
        (Seq.append (B.as_seq h0 last) (Spec.Hash.PadFinish.pad a (v total_len))) /\
    M.(modifies (footprint s h0) h0 h1) /\
    footprint s h0 == footprint s h1 /\
    preserves_freeable s h0 h1))

(** @type: true
*)
val finish:
  #a:e_alg -> (
  let a = Ghost.reveal a in
  s:state a ->
  dst:B.buffer Lib.IntTypes.uint8 { B.length dst = hash_length a } ->
  Stack unit
  (requires fun h0 ->
    invariant s h0 /\
    B.live h0 dst /\
    M.(loc_disjoint (footprint s h0) (loc_buffer dst)))
  (ensures fun h0 _ h1 ->
    invariant s h1 /\
    M.(modifies (loc_buffer dst) h0 h1) /\
    footprint s h0 == footprint s h1 /\
    B.as_seq h1 dst == Spec.Hash.PadFinish.finish a (repr s h0) /\
    preserves_freeable s h0 h1))

(** @type: true
*)
val free:
  #a:e_alg -> (
  let a = Ghost.reveal a in
  s:state a -> ST unit
  (requires fun h0 ->
    freeable h0 s /\
    invariant s h0)
  (ensures fun h0 _ h1 ->
    M.(modifies (footprint s h0) h0 h1)))

(** @type: true
*)
val copy:
  #a:e_alg -> (
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

val hash_256: Hacl.Hash.Definitions.hash_st SHA2_256
val hash_224: Hacl.Hash.Definitions.hash_st SHA2_224

(** @type: true
*)
val hash:
  a:alg ->
  dst:B.buffer Lib.IntTypes.uint8 {B.length dst = hash_length a} ->
  input:B.buffer Lib.IntTypes.uint8 ->
  len:uint32_t {B.length input = v len /\ v len <= max_input_length a} ->
  Stack unit
  (requires fun h0 ->
    B.live h0 dst /\
    B.live h0 input /\
    M.(loc_disjoint (loc_buffer input) (loc_buffer dst)))
  (ensures fun h0 _ h1 ->
    M.(modifies (loc_buffer dst) h0 h1) /\
    B.as_seq h1 dst == Spec.Agile.Hash.hash a (B.as_seq h0 input))
