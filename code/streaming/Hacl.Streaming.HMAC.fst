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
module D = Hacl.Hash.Definitions

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
type index = i:impl & l:UInt32.t { Spec.Agile.HMAC.keysized (alg_of_impl i) (UInt32.v l) }

let stateful_agile_hash_state: Hacl.Streaming.Interface.stateful index =
  Hacl.Streaming.Interface.Stateful
    (fun i -> state (dfst i))
    (fun #i h s -> footprint #(dfst i) s h)
    (fun #i h s -> freeable #(dfst i) h s)
    (fun #i h s -> invariant #(dfst i) s h)
    (fun i -> Spec.Hash.Definitions.words_state (alg_of_impl (dfst i)))
    (fun i h s -> repr s h)
    (fun #i h s -> invariant_loc_in_footprint s h)
    (fun #i l s h0 h1 ->
      frame_invariant l s h0 h1;
      frame_invariant_implies_footprint_preservation l s h0 h1)
    (fun #i l s h0 h1 -> ())
    (fun i -> alloca (dfst i))
    (fun i r -> create_in (dfst i) r)
    (fun i -> free #(dfst i))
    (fun i -> copy #(dfst i))

// Stateful key definition, keeps its length at runtime

let state (i: index) = (b:B.buffer uint8 { B.len b == dsnd i }) & B.pointer UInt32.t

let footprint (#i: index) h (s: state i): GTot B.loc =
  let k, l = s in
  (if dsnd i = 0ul then B.loc_none else B.loc_addr_of_buffer k) `B.loc_union` B.loc_addr_of_buffer l

let invariant (#i: index) h (s: state i): Type0 =
  let k, l = s in
  B.len k == B.deref h l /\ B.live h l /\ B.deref h l == dsnd i /\ (
  dsnd i <> 0ul ==>
    B.(loc_disjoint (loc_addr_of_buffer k) (loc_addr_of_buffer l)) /\ B.live h k)

let t (i: index) =
  s:S.seq uint8 { S.length s == UInt32.v (dsnd i) }

let v (i: index) h (s: state i) =
  let k, l = s in
  (B.as_seq h k <: t i)

inline_for_extraction noextract
let stateful_runtime_key: stateful index =
  Stateful
    (* s *) (fun i -> state i)
    (* footprint *) footprint
    (* freeable *) (fun #i h (k, l) -> (if dsnd i <> 0ul then B.freeable k else True) /\ B.freeable l)
    (* invariant *) (fun #i h s -> invariant #i h s)
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
        let l = B.alloca l 1ul in
        let h = ST.get () in
        k, l
      else
        B.alloca (Lib.IntTypes.u8 0) l, B.alloca l 1ul
    )
    (* create_in *) (fun i r -> (if dsnd i = 0ul then B.null else B.malloc r Lib.IntTypes.(u8 0) (dsnd i)), B.malloc r (dsnd i) 1ul)
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
let alg (i: index) = alg_of_impl (dfst i)

#set-options "--max_fuel 0 --max_ifuel 0 --z3rlimit 100"

let index_of_state (i: G.erased index) (s: Hacl.Agile.Hash.state (dfst i)) (k: state i): Stack index
  (requires (fun h0 -> Hacl.Agile.Hash.invariant s h0 /\ invariant h0 k))
  (ensures (fun h0 i' h1 -> h0 == h1 /\ G.reveal i == i'))
=
  let k: state i = k in
  let _, kl = k in
  let kl: UInt32.t = !*kl in
  let i: impl = impl_of_state (dfst i) s in
  (| i, kl |)

inline_for_extraction noextract
let hmac: block index =
  Block
    (* km *) Runtime
    (* state *) stateful_agile_hash_state
    (* key *) stateful_runtime_key
    (* output_length_t *) UInt32.t
    (* max_input_len *) (fun i ->
      D.max_input_len64 (alg i))
    (* output_length *) (fun i _ ->
      Spec.Hash.Definitions.hash_length (alg i))
    (* block_len *) (fun i ->
      D.block_len (alg i))
    (* blocks_state_len *) (fun i ->
      D.block_len (alg i))
    (* init_input_len *) (fun i ->
      D.block_len (alg i))
    (* init_input_s *) (fun i k ->
      Spec.HMAC.Incremental.init_input (alg i) k)
    (* init_s *) (fun i k ->
      Spec.HMAC.Incremental.init (alg i) k)
    (* update_multi_s *) (fun i s prevlen data ->
      let a = alg i in
      if Spec.Hash.Definitions.is_blake a then
        Spec.Agile.Hash.update_multi (alg i) s prevlen data
      else
        Spec.Agile.Hash.update_multi (alg i) s () data)
    (* update_last_s *) (fun i s prevlen data ->
      let a = alg i in
      if Spec.Hash.Definitions.is_keccak a then
        Spec.Hash.Incremental.Definitions.update_last (alg i) s () data
      else
        Spec.Hash.Incremental.Definitions.update_last (alg i) s prevlen data)
    (* finish_s *) (fun i k s l ->
      Spec.HMAC.Incremental.finish (alg i) k s)
    (* spec_s *) (fun i k input l ->
      Spec.Agile.HMAC.hmac (alg i) k input)
    (* update_multi_zero *) (fun i s prevlen ->
      let a = alg i in
      if Spec.Hash.Definitions.is_blake a then
        Spec.Hash.Lemmas.update_multi_zero_blake a (prevlen <: Spec.Hash.Definitions.extra_state a) s
      else
        Spec.Hash.Lemmas.update_multi_zero a s)
    (* update_multi_associative *) (fun i s prevlen1 prevlen2 input1 input2 ->
      let a = alg i in
      if Spec.Hash.Definitions.is_blake a then
        Spec.Hash.Lemmas.update_multi_associative_blake a s prevlen1 prevlen2 input1 input2
      else
        Spec.Hash.Lemmas.update_multi_associative a s input1 input2)
    (* spec_is_incremental *) (fun i k input l ->
      Spec.HMAC.Incremental.hmac_is_hmac_incremental (alg i) k input)
    (* index_of_state *) index_of_state
    (* init *) (fun i k buf s -> admit ())
    (* update_multi *) (fun i s prevlen blocks len ->
      Hacl.Agile.Hash.update_multi s prevlen blocks len
    )
    (* update_last *) (fun i s prevlen last last_len ->
      Hacl.Agile.Hash.update_last s prevlen last last_len
    )
    (* finish *) (fun i k s dst l -> admit ())
