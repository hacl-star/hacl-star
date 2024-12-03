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

inline_for_extraction noextract
let stateful_agile_hash_state: Hacl.Streaming.Interface.stateful Hacl.Streaming.HMAC.Definitions.index =
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

open Hacl.Streaming.HMAC.Definitions

let index_of_state (i: G.erased index) (s: Hacl.Agile.Hash.state (dfst i)) (k: state i): Stack index
  (requires (fun h0 -> Hacl.Agile.Hash.invariant s h0 /\ invariant h0 k))
  (ensures (fun h0 i' h1 -> h0 == h1 /\ G.reveal i == i'))
=
  let k: state i = k in
  let _, kl = k in
  let i: impl = impl_of_state (dfst i) s in
  (| i, kl |)

#push-options "--z3rlimit 200"

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
    (* init *) (fun i k buf s -> init i k buf s)
    (* update_multi *) (fun i s prevlen blocks len ->
      Hacl.Agile.Hash.update_multi s prevlen blocks len
    )
    (* update_last *) (fun i s prevlen last last_len ->
      Hacl.Agile.Hash.update_last s prevlen last last_len
    )
    (* finish *) (fun i k s dst l -> finish i k s dst l)
