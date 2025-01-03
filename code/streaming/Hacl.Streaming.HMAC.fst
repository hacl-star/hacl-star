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
        Spec.Agile.Hash.update_multi (alg i) (fst s) prevlen data, snd s
      else
        Spec.Agile.Hash.update_multi (alg i) (fst s) () data, snd s)
    (* update_last_s *) (fun i s prevlen data ->
      let a = alg i in
      if Spec.Hash.Definitions.is_keccak a then
        Spec.Hash.Incremental.Definitions.update_last (alg i) (fst s) () data, snd s
      else
        Spec.Hash.Incremental.Definitions.update_last (alg i) (fst s) prevlen data, snd s)
    (* finish_s *) (fun i k s l ->
      Spec.HMAC.Incremental.finish (alg i) k s)
    (* spec_s *) (fun i k input l ->
      Spec.Agile.HMAC.hmac (alg i) k input)
    (* update_multi_zero *) (fun i s prevlen ->
      let a = alg i in
      if Spec.Hash.Definitions.is_blake a then
        Spec.Hash.Lemmas.update_multi_zero_blake a (prevlen <: Spec.Hash.Definitions.extra_state a) (fst s)
      else
        Spec.Hash.Lemmas.update_multi_zero a (fst s))
    (* update_multi_associative *) (fun i s prevlen1 prevlen2 input1 input2 ->
      let a = alg i in
      if Spec.Hash.Definitions.is_blake a then
        Spec.Hash.Lemmas.update_multi_associative_blake a (fst s) prevlen1 prevlen2 input1 input2
      else
        Spec.Hash.Lemmas.update_multi_associative a (fst s) input1 input2)
    (* spec_is_incremental *) (fun i k input l ->
      Spec.HMAC.Incremental.hmac_is_hmac_incremental (alg i) k input)
    (* index_of_state *) (fun i s k -> index_of_state i (fst s) k)
    (* init *) (fun i k buf s -> init i k buf s)
    (* update_multi *) (fun i s prevlen blocks len ->
      let s1, s2 = s in
      let h0 = ST.get () in
      Hacl.Agile.Hash.update_multi s1 prevlen blocks len;
      let h1 = ST.get () in
      Hacl.Agile.Hash.frame_invariant (Hacl.Agile.Hash.footprint s1 h0) s2 h0 h1
    )
    (* update_last *) (fun i s prevlen last last_len ->
      let s1, s2 = s in
      let h0 = ST.get () in
      Hacl.Agile.Hash.update_last s1 prevlen last last_len;
      let h1 = ST.get () in
      Hacl.Agile.Hash.frame_invariant (Hacl.Agile.Hash.footprint s1 h0) s2 h0 h1
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

private
let is_blake2b_256 = function Blake2B_256 _ -> true | _ -> false
private
let is_blake2s_128 = function Blake2S_128 _ -> true | _ -> false

[@ Comment "This function returns InvalidAlgorithm if the user requests a choice of
implementation that has not been enabled at build-time (e.g. Blake2b_256 on an
ARM machine). This function returns OutOfMemory on allocation failure." ]
val malloc_:
  impl:impl -> k:B.buffer uint8 -> k_len:key_length impl { k_len == B.len k } -> (
  let c = hmac in
  let i = (| impl, k_len |) in
  let k = mk #impl k k_len in
  let t = two_state (| impl, k_len |)  in
  let t' = state i in
  let open F in
  r:HS.rid ->
  dst: B.pointer (F.state c i t t') ->
  ST Hacl.Streaming.Types.error_code
  (requires (fun h0 ->
    c.key.invariant #i h0 k /\
    B.live h0 dst /\
    HyperStack.ST.is_eternal_region r))
  (ensures (fun h0 ret h1 ->
    let open Hacl.Streaming.Types in
    match ret with
    | OutOfMemory ->
        B.(modifies loc_none h0 h1)
    | InvalidAlgorithm ->
        not EverCrypt.TargetConfig.hacl_can_compile_vec256 && is_blake2b_256 impl ||
        not EverCrypt.TargetConfig.hacl_can_compile_vec128 && is_blake2s_128 impl
    | Success ->
        let s = B.deref h1 dst in
        invariant c i h1 s /\
        freeable c i h1 s /\
        seen c i h1 s == S.empty /\
        reveal_key c i h1 s == c.key.v i h0 k /\
        B.(modifies (loc_buffer dst) h0 h1) /\
        B.fresh_loc (footprint c i h1 s) h0 h1 /\
        B.(loc_includes (loc_region_only true r) (footprint c i h1 s))
    | _ ->
        False)))

let malloc_ impl key key_length r dst =
  let open Hacl.Streaming.Types in
  if not EverCrypt.TargetConfig.hacl_can_compile_vec256 && is_blake2b_256 impl then
    InvalidAlgorithm
  else if not EverCrypt.TargetConfig.hacl_can_compile_vec128 && is_blake2s_128 impl then
    InvalidAlgorithm
  else
    let h0 = ST.get () in
    let st = malloc_internal (| impl, key_length |) (mk key key_length) r in
    if B.is_null st then
      OutOfMemory
    else
      let open LowStar.BufferOps in
      let h1 = ST.get () in
      assert B.(loc_disjoint (loc_buffer dst) (F.footprint hmac (| impl, key_length |) h1 st));
      dst *= st;
      let h2 = ST.get () in
      F.frame_invariant hmac (| impl, key_length |) (B.loc_buffer dst) st h1 h2;
      Success

inline_for_extraction noextract
let mk' (#i: index) (k:B.buffer uint8) (k_len:key_length (dfst i) { k_len == B.len k /\ k_len == dsnd i }): hmac.key.s i =
  k, k_len

val reset:
  i: G.erased index -> (
  let c = hmac in
  let i = G.reveal i in
  let t = two_state i in
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
