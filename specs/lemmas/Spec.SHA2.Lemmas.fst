module Spec.SHA2.Lemmas

open Lib.IntTypes
module C = Spec.SHA2.Constants
module S = FStar.Seq

open Spec.Hash.Definitions
open Spec.SHA2

friend Spec.SHA2

(* Scheduling function *)

(* Recursive Version *)
let rec ws_aux (a:sha2_alg) (b:block_w a) (t:counter{t < size_k_w a}): Tot (word a) =
  if t < block_word_length then b.[t]
  else
    let t16 = ws_aux a b (t - 16) in
    let t15 = ws_aux a b (t - 15) in
    let t7  = ws_aux a b (t - 7) in
    let t2  = ws_aux a b (t - 2) in

    let s1 = _sigma1 a t2 in
    let s0 = _sigma0 a t15 in
    (s1 +. t7 +. s0 +. t16)

[@"opaque_to_smt"]
let ws = ws_aux

(* Core shuffling function *)
let shuffle_core_ (a:sha2_alg) (block:block_w a) (hash:words_state a) (t:counter{t < size_k_w a}): Tot (words_state a) =
  (**) assert(7 <= S.length hash);
  let a0 = hash.[0] in
  let b0 = hash.[1] in
  let c0 = hash.[2] in
  let d0 = hash.[3] in
  let e0 = hash.[4] in
  let f0 = hash.[5] in
  let g0 = hash.[6] in
  let h0 = hash.[7] in

  (**) assert(S.length (k0 a) = size_k_w a);
  let t1 = h0 +. (_Sigma1 a e0) +. (_Ch a e0 f0 g0) +. (k0 a).[t] +. (ws a block t) in
  let t2 = (_Sigma0 a a0) +. (_Maj a a0 b0 c0) in

  (**) assert(t < S.length (k0 a));
  let l = [ t1 +. t2; a0; b0; c0; d0 +. t1; e0; f0; g0 ] in
  assert_norm (List.Tot.length l = 8);
  S.seq_of_list l

[@"opaque_to_smt"]
let shuffle_core = shuffle_core_

(* Full shuffling function *)
let shuffle_aux (a:sha2_alg) (hash:words_state a) (block:block_w a): Tot (words_state a) =
  Spec.Loops.repeat_range 0 (size_k_w a) (shuffle_core a block) hash

#push-options "--max_fuel 1 --max_ifuel 0"

val shuffle_is_shuffle_pre: a:sha2_alg -> hash:words_state a -> block:block_w a ->
  Lemma (shuffle a hash block == shuffle_aux a hash block)
let shuffle_is_shuffle_pre a hash block =
  let rec repeati_is_repeat_range #a (n:nat)
    (f:a -> (i:nat{i < n}) -> Tot a)
    (f': (i:nat{i < n}) -> a -> Tot a)
    (i:nat{i <= n})
    (acc0:a)
    : Lemma
      (requires forall x i. f x i == f' i x)
      (ensures Spec.Loops.repeat_range 0 i f acc0 == Lib.LoopCombinators.repeati i f' acc0)
    = if i = 0 then (
         Lib.LoopCombinators.eq_repeati0 n f' acc0
      ) else (
         Spec.Loops.repeat_range_induction 0 i f acc0;
         Lib.LoopCombinators.unfold_repeati n f' acc0 (i-1);
         repeati_is_repeat_range n f f' (i-1) acc0
      )
  in
  let rec ws_is_ws_pre (i:nat{i <= size_k_w a}) : Lemma
    (ensures forall (j:nat{j < i}).
      ws a block j ==
      (Lib.LoopCombinators.repeati i
        (ws_pre_inner a block)
        (Seq.create (size_k_w a) (to_word a 0))).[j]
    )

    = if i = 0 then ()
      else (
        ws_is_ws_pre (i - 1);

        Lib.LoopCombinators.unfold_repeati (size_k_w a) (ws_pre_inner a block)
          (Seq.create (size_k_w a) (to_word a 0)) (i - 1);

        let f = ws_pre_inner a block in
        let acc0 = Seq.create (size_k_w a) (to_word a 0) in

        assert (Lib.LoopCombinators.repeati i f acc0 ==
          f (i - 1) (Lib.LoopCombinators.repeati (i-1) f acc0));
        reveal_opaque (`%ws) ws
      )
  in
  let ws = ws_pre a block in
  let k = k0 a in
  let shuffle_core_is_shuffle_core_pre
    hash
    (i:counter{i < size_k_w a})
    : Lemma (shuffle_core a block hash i == shuffle_core_pre a (k0 a).[i] (ws_pre a block).[i] hash)
    = ws_is_ws_pre (size_k_w a);
      reveal_opaque (`%ws_pre) ws_pre;
      reveal_opaque (`%shuffle_core) shuffle_core;
      reveal_opaque (`%shuffle_core_pre) shuffle_core_pre
  in
  Classical.forall_intro_2 shuffle_core_is_shuffle_core_pre;
  repeati_is_repeat_range (size_k_w a) (shuffle_core a block) (fun i h -> shuffle_core_pre a (k0 a).[i] (ws_pre a block).[i] h) (size_k_w a) hash;
  assert (shuffle_pre a hash block == shuffle_aux a hash block);
  reveal_opaque (`%shuffle) shuffle

#pop-options

(* Compression function *)
let update_aux (a:sha2_alg) (hash:words_state a) (block:bytes{S.length block = block_length a}): Tot (words_state a) =
  let block_w = words_of_bytes a #block_word_length block in
  let hash_1 = shuffle_aux a hash block_w in
  Lib.Sequence.map2 ( +. ) (hash <: Lib.Sequence.lseq (word a) (state_word_length a)) hash_1

val update_is_update_pre: a:sha2_alg -> hash:words_state a -> block:bytes{S.length block = block_length a} ->
  Lemma (update a hash block == update_aux a hash block)
let update_is_update_pre a hash block =
  let block_w = words_of_bytes a #block_word_length block in
  let hash_1 = shuffle a hash block_w in
  shuffle_is_shuffle_pre a hash block_w;
  let hash:Lib.Sequence.lseq (word a) (state_word_length a) = hash in
  reveal_opaque (`%update) update;
  let s1 = Lib.Sequence.map2 (+.) hash hash_1 in
  let s2 = Spec.Loops.seq_map2 (+.) hash hash_1 in
  assert (Seq.length s1 == Seq.length s2);
  let aux (i:nat{i < Seq.length s1}) : Lemma (Seq.index s1 i == Seq.index s2 i)
    =
      // Need Lib.Sequence.index in the context for map2's postcondition to trigger
      assert (Lib.Sequence.index s1 i == ( +. ) (Seq.index hash i) (Seq.index hash_1 i))
  in Classical.forall_intro aux;
  assert (s1 `Seq.equal` s2)

