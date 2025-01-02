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
    (fun i r -> Some (create_in (dfst i) r))
    (fun i -> free #(dfst i))
    (fun i -> copy #(dfst i))

open Hacl.Streaming.HMAC.Definitions

#push-options "--z3rlimit 200"

inline_for_extraction noextract
let hmac: block index =
  Block
    (* km *) Runtime
    (* state *) stateful_agile_hash_state
    (* key *) stateful_runtime_key
    (* output_length_t *) UInt32.t
    (* max_input_len *) (fun i ->
      max_input_len64 (alg i))
    (* output_length *) (fun i _ ->
      Spec.Hash.Definitions.hash_length (alg i))
    (* block_len *) (fun i ->
      block_len (alg i))
    (* blocks_state_len *) (fun i ->
      block_len (alg i))
    (* init_input_len *) (fun i ->
      block_len (alg i))
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

module F = Hacl.Streaming.Functor

let agile_state i = F.state_s hmac i (stateful_agile_hash_state.s i) (state i)

inline_for_extraction noextract
let alloca i = F.alloca hmac i (stateful_agile_hash_state.s i) (state i)

private
let malloc_internal i = F.malloc hmac i (stateful_agile_hash_state.s i) (state i)

inline_for_extraction noextract
let mk #impl (k:B.buffer uint8) (k_len:key_length impl { k_len == B.len k }): key_and_len (| impl, k_len |) =
  k, k_len

[@ Comment "This function returns NULL if the user requests a choice of
implementation that has not been enabled at build-time (e.g. Blake2b_256 on an
ARM machine). As with other `malloc` functions for streaming APIs, this function
also returns NULL on allocation failure." ]
val malloc:
  impl:impl -> k:B.buffer uint8 -> k_len:key_length impl { k_len == B.len k } -> (
  let c = hmac in
  let i = (| impl, k_len |) in
  let k = mk #impl k k_len in
  let t = Hacl.Agile.Hash.state impl in
  let t' = state i in
  let open F in
  r:HS.rid ->
  ST (B.buffer (state_s c i t t'))
  (requires (fun h0 ->
    c.key.invariant #i h0 k /\
    HyperStack.ST.is_eternal_region r))
  (ensures (fun h0 s h1 ->
    if B.g_is_null s then
      B.(modifies loc_none h0 h1)
    else
      B.length s == 1 /\
      invariant c i h1 s /\
      freeable c i h1 s /\
      seen c i h1 s == S.empty /\
      reveal_key c i h1 s == c.key.v i h0 k /\
      B.(modifies loc_none h0 h1) /\
      B.fresh_loc (footprint c i h1 s) h0 h1 /\
      B.(loc_includes (loc_region_only true r) (footprint c i h1 s)))))

private
let is_blake2b_256 = function Blake2B_256 _ -> true | _ -> false
private
let is_blake2s_128 = function Blake2S_128 _ -> true | _ -> false

let malloc impl key key_length r =
  if not EverCrypt.TargetConfig.hacl_can_compile_vec256 && is_blake2b_256 impl then
    B.null
  else if not EverCrypt.TargetConfig.hacl_can_compile_vec128 && is_blake2s_128 impl then
    B.null
  else
    malloc_internal (| impl, key_length |) (mk key key_length) r

inline_for_extraction noextract
let mk' (#i: index) (k:B.buffer uint8) (k_len:key_length (dfst i) { k_len == B.len k /\ k_len == dsnd i }): hmac.key.s i =
  k, k_len

val reset:
  i: G.erased index -> (
  let c = hmac in
  let i = G.reveal i in
  let t = Hacl.Agile.Hash.state (dfst i) in
  let t' = state i in
  let open F in
  state:state c i t t' ->
  k:B.buffer uint8 ->
  k_len:key_length (dfst i) { k_len == B.len k } ->
  Stack Hacl.Streaming.Types.error_code
  (requires (fun h0 ->
    invariant c i h0 state /\ (
    k_len == dsnd i ==> (
    let key = mk' #i k k_len in
    c.key.invariant #i h0 key /\
    B.loc_disjoint (c.key.footprint #i h0 key) (footprint c i h0 state)))))
  (ensures (fun h0 r h1 ->
    let open Hacl.Streaming.Types in
    match r with
    | InvalidLength -> k_len <> dsnd i
    | Success ->
        k_len == dsnd i /\ (
        let key = mk k k_len in
        invariant c i h1 state /\
        seen c i h1 state == S.empty /\
        reveal_key c i h1 state == c.key.v i h0 key /\
        footprint c i h0 state == footprint c i h1 state /\
        B.(modifies (footprint c i h0 state) h0 h1) /\
        preserves_freeable c i state h0 h1)
    | _ -> False)))

let get_impl (i: G.erased index) = F.index_of_state hmac i (stateful_agile_hash_state.s i) (state i)

private
let reset_internal (i: G.erased index) = F.reset hmac i (stateful_agile_hash_state.s i) (state i)

let reset i state key key_length =
  let (| _, k_len |) = get_impl i state in
  if key_length <> k_len then
    Hacl.Streaming.Types.InvalidLength
  else begin
    reset_internal i state (key, key_length);
    Hacl.Streaming.Types.Success
  end

let update (i: G.erased index) = F.update hmac i (stateful_agile_hash_state.s i) (state i)
let digest (i: G.erased index) = F.digest_erased hmac i (stateful_agile_hash_state.s i) (state i)
let free (i: G.erased index) = F.free hmac i (stateful_agile_hash_state.s i) (state i)
let copy (i: G.erased index) = F.copy hmac i (stateful_agile_hash_state.s i) (state i)
