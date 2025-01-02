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

#set-options "--max_fuel 0 --max_ifuel 0 --z3rlimit 100"

/// We find ourselves in the same situation as with the most recent iteration of
/// Blake2: the key here is variable length, and the copy function would be
/// really hard to write if the source and destination had possibly different
/// key lengths (what to do? reallocate?), so we fix the key length *in the
/// index* so that we can statically enforce that the lengths match. This means
/// that a client of the streaming HMAC interface cannot copy from one state to
/// another if they key lengths differ.
let key_length i = l:UInt32.t { Spec.Agile.HMAC.keysized (alg_of_impl i) (UInt32.v l) }
type index = i:impl & key_length i

// Code quality (non-inlining variants)
let hash_len a = D.hash_len a
let block_len a = D.block_len a
let max_input_len64 a = D.max_input_len64 a

///////////////////////////////////////////////////////
// Stateful key definition, keeps its length at runtime
///////////////////////////////////////////////////////

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
    (* frame_invariant *) (fun (#i: index) l (s: state i) (h0: HS.mem) (h1: HS.mem) ->
      let k, l = s in
      if dsnd i = 0ul then begin
        let v0 = v i h0 s in
        let v1 = v i h1 s in
        assert (v0 `S.equal` v1)
      end;
      ()
    )
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
    (* create_in *) (fun i r -> Some ((if dsnd i = 0ul then B.null else B.malloc r Lib.IntTypes.(u8 0) (dsnd i)), dsnd i))
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

/////////////////////////////////////////////////
// Helper functions that need to be under an fsti
/////////////////////////////////////////////////

inline_for_extraction noextract
let alg (i: index) = alg_of_impl (dfst i)

val init: (i:G.erased index -> (
    let i: index = G.reveal i in
    k: state i ->
    buf_: B.buffer uint8 { B.length buf_ = UInt32.v (D.block_len (alg i)) } ->
    s: Hacl.Agile.Hash.state (dfst i) -> Stack unit
    (requires fun h0 ->
      invariant #i h0 k /\
      B.live h0 buf_ /\
      Hacl.Agile.Hash.invariant #(dfst i) s h0 /\
      B.loc_disjoint (footprint h0 k) (Hacl.Agile.Hash.footprint s h0) /\
      B.loc_disjoint (footprint h0 k) (B.loc_buffer buf_) /\
      B.loc_disjoint (B.loc_buffer buf_) (Hacl.Agile.Hash.footprint s h0))
    (ensures fun h0 _ h1 ->
      invariant h1 k /\
      (freeable h0 k ==> freeable h1 k) /\
      Hacl.Agile.Hash.invariant s h1 /\
      Hacl.Agile.Hash.repr s h1 == Spec.HMAC.Incremental.init (alg i) (v i h0 k) /\
      S.equal (S.slice (B.as_seq h1 buf_) 0 (UInt32.v (D.block_len (alg i)))) (Spec.HMAC.Incremental.init_input (alg i) (v i h0 k)) /\
      B.(modifies (loc_union (Hacl.Agile.Hash.footprint s h0) (loc_buffer buf_)) h0 h1) /\
      Hacl.Agile.Hash.footprint s h0 == Hacl.Agile.Hash.footprint s h1 /\
      (Hacl.Agile.Hash.freeable h0 s ==> Hacl.Agile.Hash.freeable h1 s))))

val finish: (
    i: G.erased index -> (
    let i = G.reveal i in
    k: state i ->
    s: Hacl.Agile.Hash.state (dfst i) ->
    dst:B.buffer uint8 ->
    l: UInt32.t { B.length dst == Spec.Agile.Hash.hash_length (alg i) } ->
    Stack unit
    (requires fun h0 ->
      Hacl.Agile.Hash.invariant s h0 /\
      B.live h0 dst /\
      B.(loc_disjoint (Hacl.Agile.Hash.footprint s h0) (loc_buffer dst)) /\ (
      invariant h0 k /\
      B.(loc_disjoint (footprint h0 k) (loc_buffer dst)) /\
      B.(loc_disjoint (footprint h0 k) (Hacl.Agile.Hash.footprint s h0))))
    (ensures fun h0 _ h1 ->
      Hacl.Agile.Hash.invariant s h1 /\
      B.(modifies (loc_buffer dst `loc_union` (Hacl.Agile.Hash.footprint s h0)) h0 h1) /\
      Hacl.Agile.Hash.footprint s h0 == Hacl.Agile.Hash.footprint s h1 /\
      B.as_seq h1 dst == Spec.HMAC.Incremental.finish (alg i) (v i h0 k) (Hacl.Agile.Hash.repr s h0) /\
      (Hacl.Agile.Hash.freeable h0 s ==> Hacl.Agile.Hash.freeable h1 s))))
