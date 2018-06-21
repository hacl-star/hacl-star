module EverCrypt.Hash

open EverCrypt.Helpers
open FStar.HyperStack.ST
open FStar.Integers

module HS = FStar.HyperStack
module B = LowStar.Buffer
module M = LowStar.Modifies

open LowStar.BufferOps

val state_s: Type0
let state = B.pointer state_s

// NS: note that the state is the first argument to the invariant so that we can
// do partial applications in pre- and post-conditions
val invariant_s: state_s -> HS.mem -> Type0
let invariant (s: state) (m: HS.mem) =
  B.live m s /\ invariant_s (B.get m s 0) m
val footprint_s: state_s -> GTot M.loc
let footprint (s: state) (m: HS.mem) =
  M.(loc_union (loc_buffer s) (footprint_s (B.get m s 0)))

type alg =
| SHA256
| SHA384

let type_of = function
| SHA256 -> uint_32
| SHA384 -> uint_64

let size_of: _ -> nat = function
| SHA256 -> 8
| SHA384 -> 8

val alg_of_s: s:state_s -> GTot alg

let alg_of (s: state) (h: HS.mem): GTot alg =
  alg_of_s (B.get h s 0)

let repr_of_alg (a: alg) =
  Seq.lseq (type_of a) (size_of a)

// TODO: define repr_s?
val repr: s:state -> h:HS.mem { invariant s h } -> GTot (repr_of_alg (alg_of s h))


// TODO: define these over memory locations
val used_in: M.loc -> HS.mem -> Type0
val fresh_loc: M.loc -> HS.mem -> HS.mem -> Type0
val fresh_is_disjoint: l1:M.loc -> l2:M.loc -> h0:HS.mem -> h1:HS.mem -> Lemma
  (requires (fresh_loc l1 h0 h1 /\ l2 `used_in` h0))
  (ensures (M.loc_disjoint l1 l2))

#reset-options "--using_facts_from '* -Hacl -Spec'"

val frame_invariant: l:M.loc -> s:state -> h0:HS.mem -> h1:HS.mem -> Lemma
  (requires (
    invariant s h0 /\
    M.loc_disjoint l (footprint s h0) /\
    M.modifies l h0 h1))
  (ensures (
    invariant s h1 /\
    (assert (alg_of s h0 = alg_of s h1);
    repr s h0 === repr s h1))) // #606

let frame_invariant_implies_footprint_preservation
  (l: M.loc)
  (s: state)
  (h0 h1: HS.mem): Lemma
  (requires (
    invariant s h0 /\
    M.loc_disjoint l (footprint s h0) /\
    M.modifies l h0 h1))
  (ensures (
    footprint s h1 == footprint s h0 /\
    alg_of s h1 == alg_of s h0))
=
  ()

val create: a:alg -> ST state
  (requires fun h0 -> True)
  (ensures fun h0 s h1 ->
    invariant s h1 /\
    M.(modifies loc_none h0 h1) /\
    fresh_loc (footprint s h1) h0 h1 /\
    alg_of s h1 == a)

#reset-options "--lax"

let init_repr (a: alg): repr_of_alg a =
  match a with
  | SHA256 -> EverCrypt.Spec.SHA2_256.h_0
  | SHA384 -> EverCrypt.Spec.SHA2_384.h_0

#reset-options "--using_facts_from '* -Hacl -Spec'"

val init: s:state -> ST unit
  (requires (invariant s))
  (ensures (fun h0 _ h1 ->
    invariant s h1 /\
    M.(modifies (footprint s h0) h0 h1) /\
    footprint s h0 == footprint s h1 /\
    alg_of s h0 == alg_of s h1 /\
    repr s h1 === init_repr (alg_of s h0)))
