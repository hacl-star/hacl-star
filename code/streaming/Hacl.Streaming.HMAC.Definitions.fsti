module Hacl.Streaming.HMAC.Definitions

/// Helper definitions with an interface so as to friend Spec.Agile.HMAC

open FStar.HyperStack.ST
open LowStar.BufferOps

module HS = FStar.HyperStack
module ST = FStar.HyperStack.ST
module B = LowStar.Buffer
module M = LowStar.Modifies
module G = FStar.Ghost
module S = FStar.Seq
module D = Hacl.Hash.Definitions

open Hacl.Agile.Hash
open Hacl.Streaming.Interface

val _sync_decl: unit

#set-options "--fuel 0 --ifuel 0 --z3rlimit 100"

/// We find ourselves in the same situation as with the most recent iteration of
/// Blake2: the key here is variable length, and the copy function would be
/// really hard to write if the source and destination had possibly different
/// key lengths (what to do? reallocate?), so we fix the key length *in the
/// index* so that we can statically enforce that the lengths match. This means
/// that a client of the streaming HMAC interface cannot copy from one state to
/// another if their key lengths differ.
let key_length i = l:UInt32.t { Spec.Agile.HMAC.keysized (alg_of_impl i) (UInt32.v l) }
type index = i:impl & key_length i

// Code quality (non-inlining variants)
let hash_len a = D.hash_len a
let block_len a = D.block_len a
let max_input_len64 a = D.max_input_len64 a

//////////////////////////////////////////////////////////////////////
// Stateful key definition, used only at initialization and reset-time
//////////////////////////////////////////////////////////////////////

let key_and_len (i: index) = (b:B.buffer uint8 { B.len b == dsnd i }) & UInt32.t

let state = key_and_len

let footprint (#i: index) h (s: state i): GTot B.loc =
  let k, l = s in
  if dsnd i = 0ul then B.loc_none else B.loc_addr_of_buffer k

let invariant (#i: index) h (s: state i): Type0 =
  let k, l = s in
  B.len k == l /\ l == dsnd i /\ (dsnd i <> 0ul ==> B.live h k)

let index_of_state (i: G.erased index) (s: Hacl.Agile.Hash.state (dfst i)) (k: state i): Stack index
  (requires (fun h0 -> Hacl.Agile.Hash.invariant s h0 /\ invariant h0 k))
  (ensures (fun h0 i' h1 -> h0 == h1 /\ G.reveal i == i'))
=
  let k: state i = k in
  let _, kl = k in
  let i: impl = impl_of_state (dfst i) s in
  (| i, kl |)

let t (i: index) =
  s:S.seq uint8 { S.length s == UInt32.v (dsnd i) }

let v (i: index) h (s: state i) =
  let k, l = s in
  (B.as_seq h k <: t i)

let frame_invariant (#i:index) (l:B.loc) (s:state i) (h0:HS.mem) (h1:HS.mem): Lemma
    (requires (
      invariant h0 s /\
      B.loc_disjoint l (footprint h0 s) /\
      B.modifies l h0 h1))
    (ensures (
      invariant h1 s /\
      v i h0 s == v i h1 s /\
      footprint h1 s == footprint h0 s))
=
  let k, l = s in
  if dsnd i = 0ul then begin
    let v0 = v i h0 s in
    let v1 = v i h1 s in
    assert (v0 `S.equal` v1)
  end;
  ()


let freeable #i h (s: state i) =
  let k, l = s in
  if dsnd i <> 0ul then B.freeable k else True

inline_for_extraction noextract
let stateful_runtime_key: stateful index =
  Stateful
    (* s *) (fun i -> state i)
    (* footprint *) footprint
    (* freeable *) (fun #i h s -> freeable h s)
    (* invariant *) (fun #i h s -> invariant h s)
    (* t *) (fun i -> t i)
    (* v *) v
    (* invariant_loc_in_footprint *) (fun #_ h s -> let k, l = s in ())
    (* frame_invariant *) frame_invariant
    (* frame_freeable *) (fun #_ l s h0 h1 -> ())
    (* alloca *) (fun i ->
      let l = dsnd i in
      if l = 0ul then
        let k = B.null in
        let h = ST.get () in
        k, l
      else
        B.alloca (Lib.IntTypes.u8 0) l, l
    )
    (* create_in *) (fun i r ->
      if dsnd i = 0ul then
        Some (B.null, dsnd i)
      else
        let k = fallible_malloc r Lib.IntTypes.(u8 0) (dsnd i) in
        if B.is_null k then
          None
        else
          Some (k, dsnd i)
    )
    (* free *) (fun _ (k, l) -> if l <> 0ul then B.free k)
    (* copy *) (fun i s_src s_dst ->
      let k_src, l_src = s_src in
      let k_dst, l_dst = s_dst in
      assert (l_src == l_dst);
      let h0 = ST.get () in
      if l_src <> 0ul then
        B.blit k_src 0ul k_dst 0ul l_src;
      let h1 = ST.get () in
      assert (S.equal (B.as_seq h1 k_dst) (B.as_seq h1 k_src)))

////////////////////////////////////
// Instance of the double-hash state
////////////////////////////////////

inline_for_extraction noextract
let alg (i: index) = alg_of_impl (dfst i)

let two_state (i: index) = Hacl.Agile.Hash.(state (dfst i) & state (dfst i))

let two_repr (i: index) h (s1, s2) = Hacl.Agile.Hash.(repr #(dfst i) s1 h, repr #(dfst i) s2 h)

let two_invariant (#i: index) h (s1, s2) =
  let open Hacl.Agile.Hash in
  invariant #(dfst i) s1 h /\ invariant #(dfst i) s2 h /\
      footprint #(dfst i) s1 h `B.loc_disjoint` footprint #(dfst i) s2 h

let two_footprint (#i: index) h (s1, s2) =
  let open Hacl.Agile.Hash in
  footprint #(dfst i) s1 h `B.loc_union` footprint #(dfst i) s2 h

let two_freeable (#i: index) h (s1, s2) =
  let open Hacl.Agile.Hash in
  freeable #(dfst i) h s1 /\ freeable #(dfst i) h s2

inline_for_extraction noextract
let stateful_agile_hash_state: Hacl.Streaming.Interface.stateful index =
  let open Hacl.Agile.Hash in
  Hacl.Streaming.Interface.Stateful
    two_state
    two_footprint
    two_freeable
    two_invariant
    (fun i -> Spec.Hash.Definitions.(words_state (alg_of_impl (dfst i)) & words_state (alg_of_impl (dfst i))))
    two_repr
    (fun #i h (s1, s2) -> invariant_loc_in_footprint s1 h; invariant_loc_in_footprint s2 h)
    (fun #i l (s1, s2) h0 h1 ->
      frame_invariant l s1 h0 h1;
      frame_invariant_implies_footprint_preservation l s1 h0 h1;
      frame_invariant l s2 h0 h1;
      frame_invariant_implies_footprint_preservation l s2 h0 h1)
    (fun #i l (s1, s2) h0 h1 -> ())
    (fun i ->
      let s1 = alloca (dfst i) in
      let h0 = ST.get () in
      let s2 = alloca (dfst i) in
      let h1 = ST.get () in
      frame_invariant B.loc_none s1 h0 h1;
      s1, s2
    )
    (fun i r ->
      let h0 = ST.get () in
      let s1 = malloc_ (dfst i) r in
      let h1 = ST.get () in
      if B.is_null s1 then
        None
      else
        let s2 = malloc_ (dfst i) r in
        if B.is_null s2 then (
          B.free s1;
          let h2 = ST.get () in
          B.(modifies_only_not_unused_in loc_none h0 h2);
          None
        ) else
          let h2 = ST.get () in
          frame_invariant B.loc_none s1 h1 h2;
          Some (s1, s2))
    (fun i (s1, s2) ->
      let h0 = ST.get () in
      free #(dfst i) s1;
      let h1 = ST.get () in
      frame_invariant (footprint s1 h0) s2 h0 h1;
      free #(dfst i) s2
    )
    (fun i (s1, s2) (s1', s2') ->
      let h0 = ST.get () in
      copy #(dfst i) s1 s1';
      let h1 = ST.get () in
      frame_invariant (footprint s1' h0) s2 h0 h1;
      frame_invariant (footprint s1' h0) s2' h0 h1;
      frame_invariant (footprint s1' h0) s1 h0 h1;
      copy #(dfst i) s2 s2';
      let h2 = ST.get () in
      frame_invariant (footprint s2' h1) s1 h1 h2;
      frame_invariant (footprint s2' h1) s1' h1 h2
    )

val init: (i:G.erased index -> (
    let i: index = G.reveal i in
    k: state i ->
    buf_: B.buffer uint8 { B.length buf_ = UInt32.v (D.block_len (alg i)) } ->
    s: two_state i -> Stack unit
    (requires fun h0 ->
      invariant #i h0 k /\
      B.live h0 buf_ /\
      two_invariant #i h0 s /\
      B.loc_disjoint (footprint h0 k) (two_footprint h0 s) /\
      B.loc_disjoint (footprint h0 k) (B.loc_buffer buf_) /\
      B.loc_disjoint (B.loc_buffer buf_) (two_footprint h0 s))
    (ensures fun h0 _ h1 ->
      invariant h1 k /\
      (freeable h0 k ==> freeable h1 k) /\
      two_invariant h1 s /\
      two_repr i h1 s == Spec.HMAC.Incremental.init (alg i) (v i h0 k) /\
      S.equal (S.slice (B.as_seq h1 buf_) 0 (UInt32.v (D.block_len (alg i)))) (Spec.HMAC.Incremental.init_input (alg i) (v i h0 k)) /\
      B.(modifies (loc_union (two_footprint h0 s) (loc_buffer buf_)) h0 h1) /\
      two_footprint h0 s == two_footprint h1 s /\
      (two_freeable h0 s ==> two_freeable h1 s))))

val finish: (
    i: G.erased index -> (
    let i = G.reveal i in
    k: state i ->
    s: two_state i ->
    dst:B.buffer uint8 ->
    l: UInt32.t { B.length dst == Spec.Agile.Hash.hash_length (alg i) } ->
    Stack unit
    (requires fun h0 ->
      two_invariant h0 s /\
      B.live h0 dst /\
      B.(loc_disjoint (two_footprint h0 s) (loc_buffer dst)) /\ (
      invariant h0 k /\
      B.(loc_disjoint (footprint h0 k) (loc_buffer dst)) /\
      B.(loc_disjoint (footprint h0 k) (two_footprint h0 s))))
    (ensures fun h0 _ h1 ->
      two_invariant h1 s /\
      B.(modifies (loc_buffer dst `loc_union` (two_footprint h0 s)) h0 h1) /\
      two_footprint h0 s == two_footprint h1 s /\
      B.as_seq h1 dst == Spec.HMAC.Incremental.finish (alg i) (v i h0 k) (two_repr i h0 s) /\
      (two_freeable h0 s ==> two_freeable h1 s))))
