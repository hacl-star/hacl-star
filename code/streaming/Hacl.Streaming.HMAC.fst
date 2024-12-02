module Hacl.Streaming.HMAC

/// A streaming API for HMAC, with agility of the choice of implementation (not algorithm!).

open FStar.HyperStack.ST
open LowStar.BufferOps

module HS = FStar.HyperStack
module ST = FStar.HyperStack.ST
module B = LowStar.Buffer
module M = LowStar.Modifies
module G = FStar.Ghost
module S = FStar.Seq

open Hacl.Agile.Hash
open Hacl.Streaming.Interface

#set-options "--max_fuel 0 --max_ifuel 0 --z3rlimit 100"

/// We find ourselves in the same situation as with the most recent iteration of
/// Blake2: the key here is variable length, and the copy function would be
/// really hard to write if the source and destination had possibly different
/// key lengths (what to do? reallocate?), so we fix the key length *in the
/// index* so that we can statically enforce that the lengths match. This means
/// that a client of the streaming HMAC interface cannot copy from one state to
/// another if they key lengths differ.
type index = impl & UInt32.t

let state (i: index) = B.buffer uint8 & B.pointer UInt32.t

let footprint (#i: index) h (s: state i): GTot B.loc =
  let k, l = s in
  (if snd i = 0ul then B.loc_none else B.loc_addr_of_buffer k) `B.loc_union` B.loc_addr_of_buffer l

let invariant #i h (s: state i) =
  let k, l = s in
  B.len k == B.deref h l /\ B.live h l /\ B.deref h l == snd i /\ (
  snd i <> 0ul ==>
    B.(loc_disjoint (loc_addr_of_buffer k) (loc_addr_of_buffer l)) /\ B.live h k)

let v (i: index) h (s: state i) =
  let k, l = s in
  B.as_seq h k

inline_for_extraction noextract
let stateful_runtime_key: stateful index =
  Stateful
    (* s *) state
    (* footprint *) footprint
    (* freeable *) (fun #i h (k, l) -> (if snd i <> 0ul then B.freeable k else True) /\ B.freeable l)
    (* invariant *) invariant
    (* t *) (fun i -> S.seq uint8)
    (* v *) v
    (* invariant_loc_in_footprint *) (fun #_ h s -> let k, l = s in ())
    (* frame_invariant *) (fun (#i: index) l (s: state i) (h0: HS.mem) (h1: HS.mem) ->
      let k, l = s in
      if snd i = 0ul then begin
        let v0 = v i h0 s in
        let v1 = v i h1 s in
        assert (v0 `S.equal` v1)
      end;
      ()
    )
    (* frame_freeable *) (fun #_ l s h0 h1 -> ())
    (* alloca *) (fun i ->
      let l = snd i in
      if l = 0ul then
        let k = B.null in
        let l = B.alloca l 1ul in
        let h = ST.get () in
        k, l
      else
        B.alloca (Lib.IntTypes.u8 0) l, B.alloca l 1ul
    )
    (* create_in *) (fun i r -> (if snd i = 0ul then B.null else B.malloc r Lib.IntTypes.(u8 0) (snd i)), B.malloc r (snd i) 1ul)
    (* free *) (fun _ (k, l) -> if !*l <> 0ul then B.free k; B.free l)
    (* copy *) (fun i s_src s_dst ->
      let k_src, l_src = s_src in
      let k_dst, l_dst = s_dst in
      let l_src = !*l_src in
      let l_dst = !*l_dst in
      assert (l_src == l_dst);
      let h0 = ST.get () in
      if l_src <> 0ul then
        B.blit k_src 0ul k_dst 0ul l_src;
      let h1 = ST.get () in
      assert (S.equal (B.as_seq h1 k_dst) (B.as_seq h1 k_src)))

inline_for_extraction noextract
let hmac: block impl =
  Block
    Runtime
    stateful_agile_hash_state
    
