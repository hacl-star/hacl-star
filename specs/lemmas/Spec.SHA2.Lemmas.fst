module Spec.SHA2.Lemmas

open Lib.IntTypes
module C = Spec.SHA2.Constants
module S = FStar.Seq

open Spec.Hash.Definitions
open Spec.SHA2

friend Spec.SHA2
friend Spec.Agile.Hash

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

#push-options "--max_fuel 1 --max_ifuel 0 --z3rlimit 200"
let update_224_256 hash block =
  let rec ws_224_256 (b: block_w SHA2_256) (t:counter{t < size_k_w SHA2_256}):
    Lemma
      (ensures (ws SHA2_224 b t == ws SHA2_256 b t))
    [ SMTPat (ws SHA2_256 b t) ]
  =
    reveal_opaque (`%ws) ws;
    assert_norm (block_w SHA2_256 == block_w SHA2_224);
    assert_norm (size_k_w SHA2_256 == size_k_w SHA2_224);
    assert_norm (_sigma1 SHA2_256 == _sigma1 SHA2_224);
    assert_norm (_sigma0 SHA2_256 == _sigma0 SHA2_224);
    // assert_norm (word_add_mod SHA2_256 == word_add_mod SHA2_224);
    if t < block_word_length then
      ()
    else begin
      ws_224_256 b (t - 16);
      ws_224_256 b (t - 15);
      ws_224_256 b (t - 7);
      ws_224_256 b (t - 2)
    end
  in
  let shuffle_core_224_256 (block:block_w SHA2_256) (hash:words_state SHA2_256) (t:counter{t < size_k_w SHA2_256}):
    Lemma (ensures (shuffle_core SHA2_224 block hash t == shuffle_core SHA2_256 block hash t))
    [ SMTPat (shuffle_core SHA2_256 block hash t) ]
  =
    reveal_opaque (`%shuffle_core) shuffle_core
  in
  let rec repeat_range_f (#a:Type) (min:nat) (max:nat{min <= max}) (f g:(a -> i:nat{i < max} -> Tot a)) (x: a):
    Lemma
      (requires (forall x (i: nat { i < max }). {:pattern f x i \/ g x i } f x i == g x i))
      (ensures (Spec.Loops.repeat_range min max f x == Spec.Loops.repeat_range min max g x))
      (decreases (max - min))
    [ SMTPat (Spec.Loops.repeat_range min max f x); SMTPat (Spec.Loops.repeat_range min max g x) ]
  =
    if min = max then
      ()
    else
      repeat_range_f (min + 1) max f g (f x min)
  in
  let shuffle_224_256 (hash:words_state SHA2_256) (block:block_w SHA2_256):
    Lemma (ensures (shuffle SHA2_224 hash block == shuffle SHA2_256 hash block))
    [ SMTPat (shuffle SHA2_256 hash block) ]
  =
    shuffle_is_shuffle_pre SHA2_224 hash block;
    shuffle_is_shuffle_pre SHA2_256 hash block;
    reveal_opaque (`%shuffle) shuffle;
    assert_norm (words_state SHA2_224 == words_state SHA2_256)
  in
  let rec seq_map2_f
    (#a:Type) (#b:Type) (#c:Type)
    (f g:(a -> b -> Tot c))
    (s:S.seq a) (s':S.seq b{S.length s = S.length s'}):
    Lemma
      (requires (forall x y. {:pattern f x y \/ g x y} f x y == g x y))
      (ensures (Spec.Loops.(seq_map2 f s s' == seq_map2 g s s')))
      (decreases (S.length s))
    [ SMTPat (Spec.Loops.seq_map2 f s s'); SMTPat (Spec.Loops.seq_map2 g s s') ]
  =
    if S.length s = 0 then
      ()
    else
      seq_map2_f f g (S.tail s) (S.tail s')
  in
  assert_norm (words_of_bytes SHA2_256 #block_word_length == words_of_bytes SHA2_224 #block_word_length);
  reveal_opaque (`%shuffle) shuffle;
  reveal_opaque (`%update) update


#pop-options

let rec update_multi_224_256 hash blocks =
  if S.length blocks = 0 then
    ()
  else
    let block, rem = Spec.Agile.Hash.split_block SHA2_256 blocks 1 in
    update_224_256 hash block;
    update_multi_224_256 (update SHA2_224 hash block) rem
