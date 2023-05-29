module Hacl.Streaming.Stateful

open FStar.HyperStack.ST
open FStar.Integers

/// First abstract interface that the streaming functor is authored against: a
/// stateful piece of data, i.e. one that obeys the compositional laws of Low*
/// vis à vis framing, free-ability, etc.

#set-options "--max_fuel 0 --max_ifuel 0 --z3rlimit 100"

module HS = FStar.HyperStack
module ST = FStar.HyperStack.ST
module B = LowStar.Buffer
module G = FStar.Ghost
module S = FStar.Seq
module U32 = FStar.UInt32
module U64 = FStar.UInt64

open LowStar.BufferOps
open FStar.Mul

inline_for_extraction noextract
let uint8 = Lib.IntTypes.uint8

inline_for_extraction noextract
let uint32 = Lib.IntTypes.uint32

/// The type class of stateful types: a low-level representation, a high-level
/// value, and a ``v`` function to switch between the two.
///
/// The low-level representation needs to abide by all the important framing
/// principles to allow clients to efficiently work with a ``stateful index``.
///
/// More interestingly, we require some extra operations that arise in the
/// process of manipulating instances of this type class:
/// - the ability to allocate on the stack (useful for temporaries)
/// - the ability to allocate on the heap (useful for retaining a copy of a stateful)
/// - the ability to copy
/// - a predicate that captures the fact that the invariant depends only on the
///   footprint of the stateful, i.e. does not rely on some gcmalloc'd global
///   state in the global scope.
///
/// This may seem like a lot but actually most low-level representations satisfy
/// these principles!

noeq
type index = {
  s: Type0;

  // Astract footprint.
  footprint: h:HS.mem -> s:s -> GTot B.loc;
  freeable: h:HS.mem -> p:s -> Type;
  invariant: h:HS.mem -> s:s -> Type;

  // A pure representation of an s
  t: Type0;
  v:  h:HS.mem -> s:s -> GTot t;

  // Adequate framing lemmas, relying on v.
  invariant_loc_in_footprint: h:HS.mem -> s:s -> Lemma
    (requires (invariant h s))
    (ensures (B.loc_in (footprint h s) h))
    [ SMTPat (invariant h s) ];

  frame_invariant: l:B.loc -> s:s -> h0:HS.mem -> h1:HS.mem -> Lemma
    (requires (
      invariant h0 s /\
      B.loc_disjoint l (footprint h0 s) /\
      B.modifies l h0 h1))
    (ensures (
      invariant h1 s /\
        v h0 s == v h1 s /\
      footprint h1 s == footprint h0 s))
    [ SMTPat (invariant h1 s); SMTPat (B.modifies l h0 h1) ];

  frame_freeable: l:B.loc -> s:s -> h0:HS.mem -> h1:HS.mem -> Lemma
    (requires (
      invariant h0 s /\
      freeable h0 s /\
      B.loc_disjoint l (footprint h0 s) /\
      B.modifies l h0 h1))
    (ensures (
      freeable h1 s))
    [ SMTPat (freeable h1 s); SMTPat (B.modifies l h0 h1) ];
}

// Stateful operations
let alloca_st (i:index) = unit -> StackInline i.s
  (requires (fun _ -> True))
  (ensures (fun h0 s h1 ->
    i.invariant h1 s /\
    B.(modifies loc_none h0 h1) /\
    B.fresh_loc (i.footprint h1 s) h0 h1 /\
    B.(loc_includes (loc_region_only true (HS.get_tip h1)) (i.footprint h1 s))))

val alloca: #i:index -> alloca_st i

let create_in_st (i:index) =
  r:HS.rid ->
  ST i.s
  (requires (fun h0 ->
    HyperStack.ST.is_eternal_region r))
  (ensures (fun h0 s h1 ->
    i.invariant h1 s /\
    B.(modifies loc_none h0 h1) /\
    B.fresh_loc (i.footprint h1 s) h0 h1 /\
    B.(loc_includes (loc_region_only true r) (i.footprint h1 s)) /\
    i.freeable h1 s))

val create_in: #i:index -> create_in_st i

let free_st (i: index) =
  s:i.s -> ST unit
  (requires fun h0 ->
    i.freeable h0 s /\
    i.invariant h0 s)
  (ensures fun h0 _ h1 ->
    B.(modifies (i.footprint h0 s) h0 h1))

val free: #i: G.erased index -> free_st i

let copy_st (i: index) =
  s_src:i.s ->
  s_dst:i.s ->
  Stack unit
    (requires (fun h0 ->
      i.invariant h0 s_src /\
      i.invariant h0 s_dst /\
      B.(loc_disjoint (i.footprint h0 s_src) (i.footprint h0 s_dst))))
    (ensures fun h0 _ h1 ->
      B.(modifies (i.footprint h0 s_dst) h0 h1) /\
      i.footprint h0 s_dst == i.footprint h1 s_dst /\
      (i.freeable h0 s_dst ==> i.freeable h1 s_dst) /\
      i.invariant h1 s_dst /\
      i.v h1 s_dst == i.v h0 s_src)

val copy: #i:G.erased index -> copy_st i

// ----------------------------
// Instances for this interface
// ----------------------------

inline_for_extraction noextract
let index_buffer (a: Type) (l: UInt32.t { UInt32.v l > 0 }): index = {
  s = (b:B.buffer a { B.len b == l });
  footprint = (fun h s -> B.loc_addr_of_buffer s);
  freeable = (fun h s -> B.freeable s);
  invariant = (fun h s -> B.live h s);
  t = (s:S.seq a { S.length s == UInt32.v l });
  v = (fun h s -> B.as_seq h s);
  invariant_loc_in_footprint = (fun h s -> ());
  frame_invariant = (fun l s h0 h1 -> ());
  frame_freeable = (fun l s h0 h1 -> ());
}

inline_for_extraction noextract
let alloca_buffer #a #l #zero: alloca_st (index_buffer a l) = fun () ->
  B.alloca zero l

inline_for_extraction noextract
let create_in_buffer #a #l #zero: create_in_st (index_buffer a l) = fun r ->
  B.malloc r zero l

inline_for_extraction noextract
let free_buffer #a #l: free_st (index_buffer a l) = fun s ->
  B.free s

inline_for_extraction noextract
let copy_buffer #a #l: copy_st (index_buffer a l) = fun s_src s_dst ->
  B.blit s_src 0ul s_dst 0ul l


inline_for_extraction noextract
let index_unused (t: Type0): index = {
  s = unit;
  footprint = (fun h s -> B.loc_none);
  freeable = (fun h s -> True);
  invariant = (fun h s -> True);
  t = unit;
  v = (fun h s -> s);
  invariant_loc_in_footprint = (fun h s -> ());
  frame_invariant = (fun l s h0 h1 -> ());
  frame_freeable = (fun l s h0 h1 -> ());
}

inline_for_extraction noextract
let alloca_unused #a: alloca_st (index_unused a) = fun () ->
  ()

inline_for_extraction noextract
let create_in_unused #a: create_in_st (index_unused a) = fun r ->
  ()

inline_for_extraction noextract
let free_unused #a: free_st (index_unused a) = fun s ->
  ()

inline_for_extraction noextract
let copy_unused #a: copy_st (index_unused a) = fun s_src s_dst ->
  ()
