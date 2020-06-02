module Hacl.Spec.SHA2.EquivScalar

open FStar.Mul
open Lib.IntTypes
open Lib.Sequence
open Lib.LoopCombinators

open Spec.Hash.Definitions
open Hacl.Spec.SHA2

module Spec = Spec.SHA2
module LSeq = Lib.Sequence
module BSeq = Lib.ByteSequence
module PadFinish = Spec.Hash.PadFinish
module UpdLemmas = Lib.UpdateMulti.Lemmas
module LSeqLemmas = Lib.Sequence.Lemmas
module Loops = Lib.LoopCombinators

friend Spec.SHA2
friend Spec.Agile.Hash

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

val ws_next_inductive: a:sha2_alg -> ws0:k_w a -> k:nat{k <= 16} ->
  Pure (k_w a)
  (requires True)
  (ensures fun res ->
    res == Loops.repeati k (ws_next_inner a) ws0 /\
    (forall (i:nat{i < k}). index res i == index (ws_next_inner a i (Loops.repeati i (ws_next_inner a) ws0)) i) /\
    (forall (i:nat{i < k - 1}). index res i == index (Loops.repeati (k - 1) (ws_next_inner a) ws0) i) /\
    (forall (i:nat{k <= i /\ i < 16}). index res i == index ws0 i))

let ws_next_inductive a ws0 k =
  Loops.eq_repeati0 k (ws_next_inner a) ws0;
  repeati_inductive #(k_w a) k
  (fun i wsi ->
    wsi == Loops.repeati i (ws_next_inner a) ws0 /\
   (forall (i0:nat{i0 < i}). index wsi i0 == index (ws_next_inner a i0 (Loops.repeati i0 (ws_next_inner a) ws0)) i0) /\
   (forall (i0:nat{i0 < i - 1}). index wsi i0 == index (Loops.repeati (i - 1) (ws_next_inner a) ws0) i0) /\
   (forall (i0:nat{i <= i0 /\ i0 < 16}). index wsi i0 == index ws0 i0))
  (fun i wsi ->
    let ws = ws_next_inner a i wsi in
    Loops.unfold_repeati (i + 1) (ws_next_inner a) ws0 i;
    ws)
  ws0


val ws_next_lemma: a:sha2_alg -> ws0:k_w a -> k:pos{k <= 16} -> Lemma
  (let wsk : k_w a = Loops.repeati k (ws_next_inner a) ws0 in
   let wsk1 : k_w a = Loops.repeati (k - 1) (ws_next_inner a) ws0 in
   (forall (i:nat{i < k}). index wsk i == index (ws_next_inner a i (Loops.repeati i (ws_next_inner a) ws0)) i) /\
   (forall (i:nat{i < k - 1}). index wsk i == index wsk1 i) /\
   (forall (i:nat{k <= i /\ i < 16}). index wsk i == index ws0 i))

let ws_next_lemma a ws0 k =
  let _ = ws_next_inductive a ws0 k in ()


val ws_next_lemma_k: a:sha2_alg -> ws0:k_w a -> k:nat{k < 16} -> Lemma
  (let ws : k_w a = Loops.repeati 16 (ws_next_inner a) ws0 in
  let wsk : k_w a = Loops.repeati (k + 1) (ws_next_inner a) ws0 in
  Seq.index ws k == Seq.index wsk k)

let ws_next_lemma_k a ws0 k =
  ws_next_lemma a ws0 (k + 1);
  ws_next_lemma a ws0 16


val ws_pre_inductive: a:sha2_alg -> block:Spec.block_w a -> k:nat{k <= Spec.size_k_w a} ->
  Pure (Spec.k_w a)
  (requires True)
  (ensures  fun res ->
   (let ws0 = Seq.create (Spec.size_k_w a) (to_word a 0) in
    res == Loops.repeati k (Spec.ws_pre_inner a block) ws0 /\
    (forall (i:nat{i < k}).
      Seq.index res i ==
      Seq.index (Spec.ws_pre_inner a block i (Loops.repeati (i + 1) (Spec.ws_pre_inner a block) ws0)) i) /\
    (forall (i:nat{i < k - 1}).
      Seq.index res i == Seq.index (Loops.repeati (k - 1) (Spec.ws_pre_inner a block) ws0) i) /\
    (forall (i:nat{k <= i /\ i < Spec.size_k_w a}). Seq.index res i == Seq.index ws0 i)))

let ws_pre_inductive a block k =
  let ws0 = Seq.create (Spec.size_k_w a) (to_word a 0) in
  Loops.eq_repeati0 k (Spec.ws_pre_inner a block) ws0;
  repeati_inductive #(Spec.k_w a) k
  (fun i wsi ->
    wsi == Loops.repeati i (Spec.ws_pre_inner a block) ws0 /\
   (forall (i0:nat{i0 < i}).
     Seq.index wsi i0 ==
     Seq.index (Spec.ws_pre_inner a block i0 (Loops.repeati (i0 + 1) (Spec.ws_pre_inner a block) ws0)) i0) /\
   (forall (i0:nat{i0 < i - 1}). Seq.index wsi i0 == Seq.index (Loops.repeati (i - 1) (Spec.ws_pre_inner a block) ws0) i0) /\
   (forall (i0:nat{i <= i0 /\ i0 < Spec.size_k_w a}). Seq.index wsi i0 == Seq.index ws0 i0))
  (fun i wsi ->
    let ws = Spec.ws_pre_inner a block i wsi in
    Loops.unfold_repeati (i + 1) (Spec.ws_pre_inner a block) ws0 i;
    ws)
  ws0


val ws_pre_lemma: a:sha2_alg -> block:Spec.block_w a -> k:pos{k <= Spec.size_k_w a} -> Lemma
  (let ws0 = Seq.create (Spec.size_k_w a) (to_word a 0) in
   let wsk : Spec.k_w a = Loops.repeati k (Spec.ws_pre_inner a block) ws0 in
   let wsk1 : Spec.k_w a = Loops.repeati (k - 1) (Spec.ws_pre_inner a block) ws0 in
  (forall (i:nat{i < k}).
    Seq.index wsk i ==
    Seq.index (Spec.ws_pre_inner a block i (Loops.repeati (i + 1) (Spec.ws_pre_inner a block) ws0)) i) /\
  (forall (i:nat{i < k - 1}). Seq.index wsk i == Seq.index wsk1 i) /\
  (forall (i:nat{k <= i /\ i < Spec.size_k_w a}). Seq.index wsk i == Seq.index ws0 i))

let ws_pre_lemma a block k =
  let _ = ws_pre_inductive a block k in ()


val ws_pre_lemma_k: a:sha2_alg -> block:Spec.block_w a -> k:nat{k < Spec.size_k_w a} -> Lemma
  (let ws0 = Seq.create (Spec.size_k_w a) (to_word a 0) in
   let ws : Spec.k_w a = Loops.repeati (Spec.size_k_w a) (Spec.ws_pre_inner a block) ws0 in
   let wsk : Spec.k_w a = Loops.repeati (k + 1) (Spec.ws_pre_inner a block) ws0 in
   Seq.index wsk k == Seq.index ws k)

let ws_pre_lemma_k a block k =
  ws_pre_lemma a block (k + 1);
  ws_pre_lemma a block (Spec.size_k_w a)


val ws_next_pre_lemma_j_step:
    a:sha2_alg
  -> block:Spec.block_w a
  -> i:nat{i < num_rounds16 a - 1}
  -> j:nat{j < 16}
  -> ws1:Spec.k_w a
  -> ws_n1:k_w a ->
  Lemma
  (requires
   (let ws_n0 : k_w a = Seq.slice ws1 (16 * i) (16 * i + 16) in
    Seq.slice ws_n1 0 j == Seq.slice ws1 (16 * i + 16) (16 * i + 16 + j) /\
    Seq.slice ws_n1 j 16 == Seq.slice ws_n0 j 16))
  (ensures
    (let ws_n = ws_next_inner a j ws_n1 in
     let ws = Spec.ws_pre_inner a block (16 * i + 16 + j) ws1 in
     Seq.index ws_n j == Seq.index ws (16 * i + 16 + j)))

let ws_next_pre_lemma_j_step a block i j ws1 ws_n1 =
  let ws_n = ws_next_inner a j ws_n1 in
  let ws = Spec.ws_pre_inner a block (16 * i + 16 + j) ws1 in

  let s0_n = _sigma0 a ws_n1.[(j+1) % 16] in
  let s1_n = _sigma1 a ws_n1.[(j+14) % 16] in
  //assert (Seq.index ws_n j == s1_n +. ws_n1.[(j+9) % 16] +. s0_n +. ws_n1.[j]);

  let s0 = _sigma0 a ws1.[16 * i + 16 + j - 15] in
  let s1 = _sigma1 a ws1.[16 * i + 16 + j - 2] in
  //assert (Seq.index ws (16 * i + 16 + j) == s1 +. ws1.[16 * i + 16 + j - 7] +. s0 +. ws1.[16 * i + 16 + j - 16]);

  let ws_n1_index (k:nat{k < 16}) :
    Lemma (if k < j then ws_n1.[k] == ws1.[16 * i + 16 + k] else ws_n1.[k] == ws1.[16 * i + k]) =
    if k < j then Seq.lemma_index_slice ws_n1 0 j k
    else Seq.lemma_index_slice ws_n1 j 16 (k - j) in

  ws_n1_index ((j + 1) % 16);
  assert (ws_n1.[(j + 1) % 16] == ws1.[16 * i + j + 1]);
  ws_n1_index ((j + 14) % 16);
  assert (ws_n1.[(j + 14) % 16] == ws1.[16 * i + j + 14]);
  ws_n1_index ((j + 9) % 16);
  assert (ws_n1.[(j + 9) % 16] == ws1.[16 * i + j + 9]);
  ws_n1_index j;
  assert (ws_n1.[j] == ws1.[16 * i + j])


val ws_next_pre_lemma_aux:
    a:sha2_alg
  -> i:nat{i < num_rounds16 a - 1}
  -> j:pos{j <= 16}
  -> ws1:Spec.k_w a
  -> ws_n1:k_w a
  -> ws:Spec.k_w a
  -> ws_n:k_w a ->
  Lemma
  (requires
   (let ws_n0 : k_w a = Seq.slice ws (16 * i) (16 * i + 16) in
    Seq.slice ws_n1 0 (j - 1) == Seq.slice ws1 (16 * i + 16) (16 * i + 16 + j - 1) /\
    (forall (k:nat{k < 16 * i + 16 + j - 1}). Seq.index ws k == Seq.index ws1 k) /\
    (forall (k:nat{k < j - 1}). Seq.index ws_n k == Seq.index ws_n1 k) /\
    Seq.index ws_n (j - 1) == Seq.index ws (16 * i + 16 + j - 1) /\
    (forall (k:nat{j <= k /\ k < 16}). Seq.index ws_n k == Seq.index ws_n0 k)))
  (ensures
   (let ws_n0 : k_w a = Seq.slice ws (16 * i) (16 * i + 16) in
    Seq.slice ws_n 0 j == Seq.slice ws (16 * i + 16) (16 * i + 16 + j) /\
    Seq.slice ws_n j 16 == Seq.slice ws_n0 j 16))

let ws_next_pre_lemma_aux a i j ws1 ws_n1 ws ws_n =
  let ws_n0 : k_w a = Seq.slice ws (16 * i) (16 * i + 16) in
  assert (Seq.slice ws_n1 0 (j - 1) == Seq.slice ws1 (16 * i + 16) (16 * i + 16 + j - 1));

  let ws_n1_index1 (k:nat{k < j - 1}) : Lemma (Seq.index ws_n1 k == Seq.index ws1 (16 * i + 16 + k)) =
    Seq.lemma_index_slice ws_n1 0 (j - 1) k;
    Seq.lemma_index_slice ws1 (16 * i + 16) (16 * i + 16 + j - 1) k in

  let ws_n_index1 (k:nat{k < j}) : Lemma (Seq.index ws_n k == Seq.index ws (16 * i + 16 + k)) =
    if k < j - 1 then ws_n1_index1 k else () in

  let ws_n_index2 (k:nat{j <= k /\ k < 16}) : Lemma (Seq.index ws_n k == Seq.index ws_n0 k) =
    () in

  Classical.forall_intro ws_n_index1;
  Seq.lemma_eq_intro (Seq.slice ws_n 0 j) (Seq.slice ws (16 * i + 16) (16 * i + 16 + j));
  Classical.forall_intro ws_n_index2;
  Seq.lemma_eq_intro (Seq.slice ws_n j 16) (Seq.slice ws_n0 j 16)


val ws_next_pre_lemma_init:
    a:sha2_alg
  -> block:Spec.block_w a
  -> i:nat{i < num_rounds16 a - 1}
  -> j:pos{j <= 16} -> Lemma
  (let ws0 = Seq.create (Spec.size_k_w a) (to_word a 0) in
   let ws : Spec.k_w a = Loops.repeati (16 * i + 16 + j) (Spec.ws_pre_inner a block) ws0 in
   let ws1 : Spec.k_w a = Loops.repeati (16 * i + 16 + j - 1) (Spec.ws_pre_inner a block) ws0 in
   Seq.slice ws1 (16 * i) (16 * i + 16) == Seq.slice ws (16 * i) (16 * i + 16))

let ws_next_pre_lemma_init a block i j =
  let ws0 = Seq.create (Spec.size_k_w a) (to_word a 0) in
  let ws : Spec.k_w a = Loops.repeati (16 * i + 16 + j) (Spec.ws_pre_inner a block) ws0 in
  let ws1 : Spec.k_w a = Loops.repeati (16 * i + 16 + j - 1) (Spec.ws_pre_inner a block) ws0 in

  let s : Spec.block_w a = Seq.slice ws (16 * i) (16 * i + 16) in
  let s1 : Spec.block_w a = Seq.slice ws1 (16 * i) (16 * i + 16) in

  let aux (k:nat{k < 16}) : Lemma (Seq.index s k == Seq.index s1 k) =
    ws_pre_lemma a block (16 * i + 16 + j);
    ws_pre_lemma a block (16 * i + 16 + j - 1) in

  Classical.forall_intro aux;
  Seq.lemma_eq_intro s s1


val ws_next_pre_lemma_j:
    a:sha2_alg
  -> block:Spec.block_w a
  -> i:nat{i < num_rounds16 a - 1}
  -> j:nat{j <= 16} -> Lemma
  (let ws0 = Seq.create (Spec.size_k_w a) (to_word a 0) in
   let ws : Spec.k_w a = Loops.repeati (16 * i + 16 + j) (Spec.ws_pre_inner a block) ws0 in
   let ws_n0 : k_w a = Seq.slice ws (16 * i) (16 * i + 16) in
   let ws_n : k_w a = Loops.repeati j (ws_next_inner a) ws_n0 in
   Seq.slice ws_n 0 j == Seq.slice ws (16 * i + 16) (16 * i + 16 + j) /\
   Seq.slice ws_n j 16 == Seq.slice ws_n0 j 16)

let rec ws_next_pre_lemma_j a block i j =
  let ws_pre_f = Spec.ws_pre_inner a block in
  let ws_next_f = ws_next_inner a in

  let ws0 = Seq.create (Spec.size_k_w a) (to_word a 0) in
  let ws : Spec.k_w a = Loops.repeati (16 * i + 16 + j) ws_pre_f ws0 in
  let ws_n0 : k_w a = Seq.slice ws (16 * i) (16 * i + 16) in
  let ws_n : k_w a = Loops.repeati j ws_next_f ws_n0 in

  if j = 0 then
    Loops.eq_repeati0 j ws_next_f ws_n0
  else begin
    let ws1 : Spec.k_w a = Loops.repeati (16 * i + 16 + j - 1) ws_pre_f ws0 in
    ws_next_pre_lemma_init a block i j;
    assert (Seq.slice ws1 (16 * i) (16 * i + 16) == ws_n0);
    let ws_n1 : k_w a  = Loops.repeati (j - 1) ws_next_f ws_n0 in
    ws_next_pre_lemma_j a block i (j - 1);
    assert (Seq.slice ws_n1 0 (j - 1) == Seq.slice ws1 (16 * i + 16) (16 * i + 16 + j - 1));
    assert (Seq.slice ws_n1 (j - 1) 16 == Seq.slice ws_n0 (j - 1) 16);

    ws_pre_lemma a block (16 * i + 16 + j);
    assert (forall (k:nat{k < 16 * i + 16 + j - 1}). Seq.index ws k == Seq.index ws1 k);
    Loops.unfold_repeati (16 * i + 16 + j) ws_pre_f ws0 (16 * i + 16 + j - 1);
    //assert (ws == ws_pre_f (16 * i + 16 + j - 1) ws1);

    ws_next_lemma a ws_n0 j;
    assert (forall (k:nat{k < j - 1}). Seq.index ws_n k == Seq.index ws_n1 k);
    assert (forall (k:nat{j <= k /\ k < 16}). Seq.index ws_n k == Seq.index ws_n0 k);
    Loops.unfold_repeati j ws_next_f ws_n0 (j - 1);
    //assert (ws_n == ws_next_f (j - 1) ws_n1);
    ws_next_pre_lemma_j_step a block i (j - 1) ws1 ws_n1;
    assert (Seq.index ws_n (j - 1) == Seq.index ws (16 * i + 16 + j - 1));
    ws_next_pre_lemma_aux a i j ws1 ws_n1 ws ws_n;
    () end


val ws_next_pre_lemma:
    a:sha2_alg
  -> block:Spec.block_w a
  -> i:nat{i < num_rounds16 a - 1}
  -> j:nat{j < 16} -> Lemma
  (let ws : Spec.k_w a = Spec.ws_pre a block in
   let ws_n0 : k_w a = Seq.slice ws (16 * i) (16 * i + 16) in
   let ws_n : k_w a = ws_next a ws_n0 in
   Seq.index ws_n j == Seq.index ws (16 * i + 16 + j))

let ws_next_pre_lemma a block i j =
  reveal_opaque (`%Spec.ws_pre) Spec.ws_pre;
  let ws0 = Seq.create (Spec.size_k_w a) (to_word a 0) in
  let ws : Spec.k_w a = Loops.repeati (Spec.size_k_w a) (Spec.ws_pre_inner a block) ws0 in
  let ws_n0 : k_w a = Seq.slice ws (16 * i) (16 * i + 16) in
  let ws_n : k_w a = Loops.repeati 16 (ws_next_inner a) ws_n0 in

  let wsj : Spec.k_w a = Loops.repeati (16 * i + 16 + j + 1) (Spec.ws_pre_inner a block) ws0 in
  let ws_n0j : k_w a = Seq.slice wsj (16 * i) (16 * i + 16) in
  let ws_nj : k_w a = Loops.repeati (j + 1) (ws_next_inner a) ws_n0 in

  let aux (k:nat{k < 16}) : Lemma (Seq.index ws_n0 k == Seq.index ws_n0j k) =
    ws_pre_lemma a block (16 * i + 16 + j + 1);
    ws_pre_lemma a block (Spec.size_k_w a) in

  Classical.forall_intro aux;
  Seq.lemma_eq_intro ws_n0 ws_n0j;

  ws_next_pre_lemma_j a block i (j + 1);
  assert (Seq.slice ws_nj 0 (j + 1) == Seq.slice wsj (16 * i + 16) (16 * i + 16 + j + 1));
  Seq.lemma_index_slice ws_nj 0 (j + 1) j;
  assert (Seq.index ws_nj j == Seq.index wsj (16 * i + 16 + j));

  ws_pre_lemma_k a block (16 * i + 16 + j);
  assert (Seq.index wsj (16 * i + 16 + j) == Seq.index ws (16 * i + 16 + j));

  ws_next_lemma_k a ws_n0 j;
  assert (Seq.index ws_nj j == Seq.index ws_n j)


val shuffle_core_pre_lemma: a:sha2_alg -> k_t:word a -> ws_t:word a -> hash:words_state a ->
  Lemma (shuffle_core_pre a k_t ws_t hash == Spec.shuffle_core_pre a k_t ws_t hash)
let shuffle_core_pre_lemma a k_t ws_t hash =
  reveal_opaque (`%Spec.shuffle_core_pre) Spec.shuffle_core_pre


noextract
val shuffle_pre_inner: a:sha2_alg -> ws:Spec.k_w a -> i:nat{i < size_k_w a} -> st:words_state a -> words_state a
let shuffle_pre_inner a ws i st =
  let k = k0 a in
  shuffle_core_pre a k.[i] ws.[i] st


val shuffle_spec_lemma: a:sha2_alg -> st0:words_state a -> block:Spec.block_w a -> Lemma
  (let ws = Spec.ws_pre a block in
   Loops.repeati (Spec.size_k_w a) (shuffle_pre_inner a ws) st0 == Spec.shuffle a st0 block)

let shuffle_spec_lemma a st0 block =
  reveal_opaque (`%Spec.shuffle) Spec.shuffle;
  let ws = Spec.ws_pre a block in
  let k = Spec.k0 a in
  let aux (i:nat{i < Spec.size_k_w a}) (st:words_state a) :
    Lemma (shuffle_pre_inner a ws i st == Spec.shuffle_core_pre a k.[i] ws.[i] st) =
    let k = Spec.k0 a in
    shuffle_core_pre_lemma a k.[i] ws.[i] st in
  Classical.forall_intro_2 aux;
  LSeqLemmas.repeati_extensionality (Spec.size_k_w a)
    (shuffle_pre_inner a ws)
    (fun i h -> Spec.shuffle_core_pre a k.[i] ws.[i] h) st0


noextract
val shuffle_pre_inner16:
    a:sha2_alg
  -> ws:Spec.k_w a
  -> i:nat{i < num_rounds16 a}
  -> j:nat{j < 16}
  -> st:words_state a ->
  words_state a

let shuffle_pre_inner16 a ws i j st =
  let k = k0 a in
  shuffle_core_pre a k.[16 * i + j] ws.[16 * i + j] st


noextract
val shuffle_pre_inner_num_rounds:
    a:sha2_alg
  -> ws:Spec.k_w a
  -> i:nat{i < num_rounds16 a}
  -> st:words_state a ->
  words_state a

let shuffle_pre_inner_num_rounds a ws i st =
  Loops.repeati 16 (shuffle_pre_inner16 a ws i) st


val shuffle_spec_lemma16_step:
    a:sha2_alg
  -> block:Spec.block_w a
  -> i:nat{i < num_rounds16 a}
  -> st:words_state a
  -> j:nat{j <= 16} ->
  Lemma
   (let ws = Spec.ws_pre a block in
    Loops.repeati j (shuffle_pre_inner16 a ws i) st ==
    Loops.repeat_right (16 * i) (16 * i + j) (Loops.fixed_a (words_state a)) (shuffle_pre_inner a ws) st)

let rec shuffle_spec_lemma16_step a block i st j =
  let ws = Spec.ws_pre a block in
  let a_fixed = Loops.fixed_a (words_state a) in
  //let lp = Loops.repeati j (shuffle_pre_inner16 a ws i) st in
  //let rp = Loops.repeat_right (16 * i) (16 * i + j) a_fixed (shuffle_pre_inner a ws) st in
  if j = 0 then begin
    Loops.eq_repeati0 j (shuffle_pre_inner16 a ws i) st;
    Loops.eq_repeat_right (16 * i) (16 * i + j) a_fixed (shuffle_pre_inner a ws) st end
  else begin
    //let lp1 = Loops.repeati (j - 1) (shuffle_pre_inner16 a ws i) st in
    //let rp1 = Loops.repeat_right (16 * i) (16 * i + j - 1) a_fixed (shuffle_pre_inner a ws) st in
    Loops.unfold_repeati j (shuffle_pre_inner16 a ws i) st (j - 1);
    Loops.unfold_repeat_right (16 * i) (16 * i + j) a_fixed (shuffle_pre_inner a ws) st (16 * i + j - 1);
    //assert (lp == shuffle_pre_inner16 a ws i (j - 1) lp1);
    //assert (rp == shuffle_pre_inner a ws (16 * i + j - 1) rp1);
    shuffle_spec_lemma16_step a block i st (j - 1);
    () end


val shuffle_spec_lemma16: a:sha2_alg -> st0:words_state a -> block:Spec.block_w a -> Lemma
  (let ws = Spec.ws_pre a block in
   Loops.repeati (Spec.size_k_w a) (shuffle_pre_inner a ws) st0 ==
   Loops.repeati (num_rounds16 a) (shuffle_pre_inner_num_rounds a ws) st0)

let shuffle_spec_lemma16 a st0 block =
  //w = 16, n = num_rounds16 a, normalize_v = id
  let ws = Spec.ws_pre a block in
  let a_fixed = Loops.fixed_a (words_state a) in
  let aux (i:nat{i < num_rounds16 a}) (st:words_state a) :
    Lemma (shuffle_pre_inner_num_rounds a ws i st ==
      Loops.repeat_right (16 * i) (16 * (i + 1)) a_fixed (shuffle_pre_inner a ws) st) =
   shuffle_spec_lemma16_step a block i st 16 in

  Classical.forall_intro_2 aux;
  Lib.Vec.Lemmas.lemma_repeati_vec 16 (num_rounds16 a) (fun x -> x)
    (shuffle_pre_inner a ws)
    (shuffle_pre_inner_num_rounds a ws)
    st0


val ws_next_inner_lemma:
    a:sha2_alg
  -> block:k_w a
  -> i:nat{i < num_rounds16 a}
  -> ws1:k_w a ->
  Lemma
  (requires
   (let ws_s = Spec.ws_pre a block in
   (if i < num_rounds16 a - 1 then
      ws1 == Seq.slice ws_s (16 * i) (16 * i + 16)
    else
      ws1 == Seq.slice ws_s (16 * (num_rounds16 a - 1)) (16 * num_rounds16 a))))
  (ensures
   (let ws_s = Spec.ws_pre a block in
    let ws = if i < num_rounds16 a - 1 then ws_next a ws1 else ws1 in
   (if i < num_rounds16 a - 1 then
      ws == Seq.slice ws_s (16 * (i + 1)) (16 * (i + 1) + 16)
    else
      ws == Seq.slice ws_s (16 * (num_rounds16 a - 1)) (16 * num_rounds16 a))))

let ws_next_inner_lemma a block i ws1 =
  let ws_s : Spec.k_w a = Spec.ws_pre a block in
  let ws = if i < num_rounds16 a - 1 then ws_next a ws1 else ws1 in

  if i < num_rounds16 a - 1 then begin
    let aux (k:nat{k < 16}) : Lemma (Seq.index (ws_next a ws1) k == Seq.index ws_s (16 * (i + 1) + k)) =
      ws_next_pre_lemma a block i k in
    Classical.forall_intro aux;
    Seq.lemma_eq_intro (ws_next a ws1) (Seq.slice ws_s (16 * (i + 1)) (16 * (i + 1) + 16)) end
  else ()


val shuffle_lemma_i_step:
    a:sha2_alg
  -> block:k_w a
  -> st0:words_state a
  -> i:nat{i < num_rounds16 a}
  -> ws1:k_w a
  -> st1:words_state a ->
  Lemma
  (requires
   (let ws_s = Spec.ws_pre a block in
   (if i < num_rounds16 a - 1 then
      ws1 == Seq.slice ws_s (16 * i) (16 * i + 16)
    else
      ws1 == Seq.slice ws_s (16 * (num_rounds16 a - 1)) (16 * num_rounds16 a))))
  (ensures
   (let ws_s = Spec.ws_pre a block in
    let st_s = shuffle_pre_inner_num_rounds a ws_s i st1 in
    let (ws, st) = shuffle_inner_loop a i (ws1, st1) in
    st == st_s /\
   (if i < num_rounds16 a - 1 then
      ws == Seq.slice ws_s (16 * (i + 1)) (16 * (i + 1) + 16)
    else
      ws == Seq.slice ws_s (16 * (num_rounds16 a - 1)) (16 * num_rounds16 a))))

let shuffle_lemma_i_step a block st0 i ws1 st1 =
  let ws_s = Spec.ws_pre a block in
  let st_s = Loops.repeati 16 (shuffle_pre_inner16 a ws_s i) st1 in
  let st = Loops.repeati 16 (shuffle_inner a ws1 i) st1 in
  let ws = if i < num_rounds16 a - 1 then ws_next a ws1 else ws1 in
  ws_next_inner_lemma a block i ws1;

  let aux_st (j:nat{j < 16}) (hash:words_state a) :
    Lemma (shuffle_pre_inner16 a ws_s i j hash == shuffle_inner a ws1 i j hash) =
    let k_t = Seq.index (k0 a) (16 * i + j) in
    let lp = shuffle_core_pre a k_t ws_s.[16 * i + j] st in
    let rp = shuffle_core_pre a k_t ws1.[j] hash in
    assert (ws1.[j] == ws_s.[16 * i + j]) in

  Classical.forall_intro_2 aux_st;
  LSeqLemmas.repeati_extensionality 16 (shuffle_pre_inner16 a ws_s i) (shuffle_inner a ws1 i) st1


val ws_pre_init_lemma: a:sha2_alg -> block:k_w a -> Lemma
  (Seq.slice (Spec.ws_pre a block) 0 16 == block)

let ws_pre_init_lemma a block =
  reveal_opaque (`%Spec.ws_pre) Spec.ws_pre;
  let ws0 = Seq.create (Spec.size_k_w a) (to_word a 0) in
  let ws : Spec.k_w a = Loops.repeati (Spec.size_k_w a) (Spec.ws_pre_inner a block) ws0 in
  let aux (k:nat{k < 16}) : Lemma (Seq.index ws k == Seq.index block k) =
    ws_pre_lemma a block (k + 1);
    ws_pre_lemma_k a block k in

  Classical.forall_intro aux;
  Seq.lemma_eq_intro (Seq.slice (Spec.ws_pre a block) 0 16) block


val shuffle_lemma_i:
    a:sha2_alg
  -> block:k_w a
  -> st0:words_state a
  -> i:nat{i <= num_rounds16 a} ->
  Lemma
  (let ws_s = Spec.ws_pre a block in
   let (ws, st) : tuple2 (k_w a) (words_state a) =
     Loops.repeati i (shuffle_inner_loop a) (block, st0) in
   st == Loops.repeati i (shuffle_pre_inner_num_rounds a ws_s) st0 /\
   (if i < num_rounds16 a - 1 then
     ws == Seq.slice ws_s (16 * i) (16 * i + 16)
    else
     ws == Seq.slice ws_s (16 * (num_rounds16 a - 1)) (16 * num_rounds16 a)))

let rec shuffle_lemma_i a block st0 i =
  let ws_s = Spec.ws_pre a block in
  let (ws, st) = Loops.repeati i (shuffle_inner_loop a) (block, st0) in
  let st_s = Loops.repeati i (shuffle_pre_inner_num_rounds a ws_s) st0 in

  if i = 0 then begin
    Loops.eq_repeati0 i (shuffle_inner_loop a) (block, st0);
    Loops.eq_repeati0 i (shuffle_pre_inner_num_rounds a ws_s) st0;
    ws_pre_init_lemma a block;
    () end
  else begin
    let (ws1, st1) = Loops.repeati (i - 1) (shuffle_inner_loop a) (block, st0) in
    let st_s1 = Loops.repeati (i - 1) (shuffle_pre_inner_num_rounds a ws_s) st0 in
    Loops.unfold_repeati i (shuffle_inner_loop a) (block, st0) (i - 1);
    Loops.unfold_repeati i (shuffle_pre_inner_num_rounds a ws_s) st0 (i - 1);
    assert (st_s == shuffle_pre_inner_num_rounds a ws_s (i - 1) st_s1);
    assert ((ws, st) == shuffle_inner_loop a (i - 1) (ws1, st1));
    shuffle_lemma_i a block st0 (i - 1);
    //assert (st1 == st_s1);
    assert (st_s == shuffle_pre_inner_num_rounds a ws_s (i - 1) st1);
    shuffle_lemma_i_step a block st0 (i - 1) ws1 st1 end


val shuffle_lemma: a:sha2_alg -> block:k_w a -> st0:words_state a ->
  Lemma (shuffle a block st0 == Spec.shuffle a st0 block)
let shuffle_lemma a block st0 =
  let ws_s = Spec.ws_pre a block in
  //let st_s = Loops.repeati (Spec.size_k_w a) (shuffle_pre_inner a ws_s) st0 in
  shuffle_spec_lemma a st0 block;
  shuffle_spec_lemma16 a st0 block;
  //assert (Spec.shuffle a st0 block == Loops.repeati (num_rounds16 a) (shuffle_pre_inner_num_rounds a ws_s) st0);
  //let (ws, st) = Loops.repeati (num_rounds16 a) (shuffle_inner_loop a) (block, st0) in
  shuffle_lemma_i a block st0 (num_rounds16 a)


val update_lemma: a:sha2_alg -> block:block_t a -> hash:words_state a ->
  Lemma (update a block hash == Spec.update a hash block)
let update_lemma a block hash =
  reveal_opaque (`%Spec.update) Spec.update;
  let block_w = BSeq.uints_from_bytes_be #(word_t a) #SEC block in
  assert (block_w == words_of_bytes a #block_word_length block);
  let hash_1 = shuffle a block_w hash in
  shuffle_lemma a block_w hash;
  assert (hash_1 == Spec.shuffle a hash block_w);

  let res = map2 #_ #_ #_ #8 ( +. ) hash_1 hash in
  let res_comm = map2 #_ #_ #_ #8 ( +. ) hash hash_1 in
  let aux (i:nat{i < 8}) : Lemma (res.[i] == res_comm.[i]) =
    assert (index res i == hash_1.[i] +. hash.[i]);
    assert (index res_comm i == hash.[i] +. hash_1.[i]);
    assert (v (hash_1.[i] +. hash.[i]) == v (hash.[i] +. hash_1.[i]));
    assert (index res i == index res_comm i) in

  Classical.forall_intro aux;
  eq_intro res res_comm;
  eq_intro #_ #8 (update a block hash) (Spec.update_pre a hash block)


val finish_lemma: a:sha2_alg -> st:words_state a -> Lemma (finish a st == PadFinish.finish a st)
let finish_lemma a st =
  let hash_final_w = sub #_ #8 st 0 (hash_word_length a) in
  assert (PadFinish.finish a st == BSeq.uints_to_bytes_be #(word_t a) #SEC hash_final_w);
  assert (finish a st == sub (BSeq.uints_to_bytes_be #(word_t a) #SEC #8 st) 0 (hash_length a));
  assert (hash_length a == word_length a * hash_word_length a);

  let aux (i:nat{i < hash_length a}) : Lemma ((finish a st).[i] == (PadFinish.finish a st).[i]) =
    BSeq.index_uints_to_bytes_be #(word_t a) #SEC hash_final_w i;
    BSeq.index_uints_to_bytes_be #(word_t a) #SEC #8 st i in

  Classical.forall_intro aux;
  eq_intro (finish a st) (PadFinish.finish a st)

//TODO: move to Lib.Sequence.Lemmas
val repeat_blocks_multi_extensionality:
    #a:Type0
  -> #b:Type0
  -> blocksize:size_pos
  -> inp:seq a{length inp % blocksize = 0}
  -> f:(lseq a blocksize -> b -> b)
  -> g:(lseq a blocksize -> b -> b)
  -> init:b ->
  Lemma
  (requires
    (forall (block:lseq a blocksize) (acc:b). f block acc == g block acc))
  (ensures
    repeat_blocks_multi blocksize inp f init ==
    repeat_blocks_multi blocksize inp g init)

let repeat_blocks_multi_extensionality #a #b blocksize inp f g init =
  let len = length inp in
  let nb = len / blocksize in
  let f_rep = repeat_blocks_f blocksize inp f nb in
  let g_rep = repeat_blocks_f blocksize inp g nb in

  lemma_repeat_blocks_multi blocksize inp f init;
  lemma_repeat_blocks_multi blocksize inp g init;

  let aux (i:nat{i < nb}) (acc:b) : Lemma (f_rep i acc == g_rep i acc) =
    Math.Lemmas.lemma_mult_le_right blocksize (i + 1) nb;
    Seq.Properties.slice_slice inp 0 (nb * blocksize) (i * blocksize) (i * blocksize + blocksize) in

  Classical.forall_intro_2 aux;
  LSeqLemmas.repeati_extensionality nb f_rep g_rep init


val update_multi_is_repeat_blocks_multi:
     a:sha2_alg
  -> len:size_nat
  -> b:lseq uint8 len
  -> st0:words_state a
  -> pad_s:lseq uint8 (pad_length a len) ->
  Lemma
   (let blocks = Seq.append b pad_s in
    Spec.Agile.Hash.update_multi a st0 blocks ==
    LSeq.repeat_blocks_multi (block_length a) blocks (update a) st0)

let update_multi_is_repeat_blocks_multi a len b st0 pad_s =
  let blocks = Seq.append b pad_s in
  assert ((pad_length a len + len) % block_length a = 0);

  let upd_last (st:words_state a) s = st in
  UpdLemmas.update_full_is_repeat_blocks #(words_state a) (block_length a)
    (Spec.Agile.Hash.update a) upd_last st0 blocks blocks;

  let repeat_f = UpdLemmas.repeat_f (block_length a) (Spec.Agile.Hash.update a) in
  let repeat_l = UpdLemmas.repeat_l (block_length a) upd_last blocks in
  //assert
    //(Spec.Agile.Hash.update_multi a st0 blocks ==
    // LSeq.repeat_blocks (block_length a) blocks repeat_f repeat_l st0);

  LSeqLemmas.lemma_repeat_blocks_via_multi (block_length a) blocks repeat_f repeat_l st0;
  // assert
  //   (Spec.Agile.Hash.update_multi a st0 blocks ==
  //    LSeq.repeat_blocks_multi (block_length a) blocks repeat_f st0);

  Classical.forall_intro_2 (update_lemma a);
  repeat_blocks_multi_extensionality (block_length a) blocks repeat_f (update a) st0


val hash_is_repeat_blocks:
     a:sha2_alg
  -> len:size_nat
  -> b:lseq uint8 len
  -> st0:words_state a ->
  Lemma
   (let len':len_t a = Lib.IntTypes.cast #U32 #PUB (len_int_type a) PUB (size len) in
    let st = update_nblocks a len b st0 in
    let rem = len % block_length a in
    let mb = sub b (len - rem) rem in
    update_last a len' rem mb st ==
    LSeq.repeat_blocks (block_length a) b (update a) (update_last a len') st0)

let hash_is_repeat_blocks a len b st0 =
  let bs = block_length a in
  let nb = len / bs in
  let rem = len % bs in
  let acc = Loops.repeati nb (repeat_blocks_f bs b (update a) nb) st0 in

  let aux (i:nat{i < nb}) (acc:words_state a) :
    Lemma (repeat_blocks_f bs b (update a) nb i acc == update_block a len b i acc) = () in
  Classical.forall_intro_2 aux;
  LSeqLemmas.repeati_extensionality nb (repeat_blocks_f bs b (update a) nb) (update_block a len b) st0;
  assert (acc == update_nblocks a len b st0);

  let len':len_t a = Lib.IntTypes.cast #U32 #PUB (len_int_type a) PUB (size len) in
  LSeq.lemma_repeat_blocks bs b (update a) (update_last a len') st0;
  let last = Seq.slice b (nb * bs) len in
  assert (LSeq.repeat_blocks bs b (update a) (update_last a len') st0 == update_last a len' rem last acc)


val append_pad_last_length_lemma: a:sha2_alg -> len:size_nat ->
  Lemma
   (let blocksize = block_length a in
    let b_len = (blocksize - (len + len_length a + 1)) % blocksize + 1 + len_length a + len % blocksize in
    b_len = blocksize \/ b_len = 2 * blocksize)

let append_pad_last_length_lemma a len =
  let blocksize = block_length a in
  let x = 1 + len_length a + len % blocksize in
  let b_len = (blocksize - (len + len_length a + 1)) % blocksize + 1 + len_length a + len % blocksize in
  Math.Lemmas.lemma_mod_sub_distr (blocksize - len_length a - 1) len blocksize;
  assert (b_len == (blocksize - x) % blocksize + x)
  //if x < blocksize then b_len = blocksize else b_len = 2 * blocksize


val load_last_lemma:
     a:sha2_alg
  -> totlen:size_nat{totlen <= max_input_length a}
  -> totlen_seq:lseq uint8 (len_length a)
  -> b:bytes{length b = totlen % block_length a} ->
  Lemma
   (let rem = totlen % block_length a in
    let fin = padded_blocks a rem * block_length a in
    let last = create (2 * block_length a) (u8 0) in
    let last = update_sub last 0 rem b in
    let last = last.[rem] <- u8 0x80 in
    let last = update_sub last (fin - len_length a) (len_length a) totlen_seq in
    let firstbyte = create 1 (u8 0x80) in
    let zeros = create (pad0_length a totlen) (u8 0) in
    let pad = Seq.append (Seq.append firstbyte zeros) totlen_seq in
    Seq.equal (Seq.slice last 0 fin) (Seq.append b pad))

let load_last_lemma a totlen totlen_seq b =
  //last = b @| firstbyte @| zeros @| pad
  let firstbyte = create 1 (u8 0x80) in
  let zeros = create (pad0_length a totlen) (u8 0) in
  let pad = Seq.append (Seq.append firstbyte zeros) totlen_seq in
  assert (length pad == pad_length a totlen);
  append_pad_last_length_lemma a totlen;
  let rem = totlen % block_length a in
  let fin = padded_blocks a rem * block_length a in
  assert (fin - len_length a == rem + 1 + pad0_length a totlen);


  let last = create (2 * block_length a) (u8 0) in
  let last1 = update_sub last 0 rem b in
  Seq.lemma_eq_intro (Seq.slice last1 0 rem) b;
  let aux (i:nat{i < pad0_length a totlen}) : Lemma (last1.[rem + 1 + i] == zeros.[i]) =
    assert (index last1 (rem + 1 + i) == index zeros i) in //REALLY??
  Classical.forall_intro aux;
  Seq.lemma_eq_intro (Seq.slice last1 (rem + 1) (fin - len_length a)) zeros;

  let last2 = last1.[rem] <- u8 0x80 in
  Seq.lemma_eq_intro (Seq.slice last2 0 rem) b;
  Seq.lemma_eq_intro (Seq.slice last2 rem (rem + 1)) firstbyte;
  Seq.lemma_eq_intro (Seq.slice last2 (rem + 1) (fin - len_length a)) zeros;

  let last3 = update_sub last2 (fin - len_length a) (len_length a) totlen_seq in
  Seq.lemma_eq_intro (Seq.slice last3 (fin - len_length a) fin) totlen_seq;

  let aux (i:nat{i < fin - len_length a}) : Lemma (last3.[i] == last2.[i]) =
    assert (index last3 i == index last2 i) in //REALLY??
  Classical.forall_intro aux;
  Seq.lemma_eq_intro (Seq.slice last3 0 (fin - len_length a)) (Seq.slice last2 0 (fin - len_length a));
  Seq.lemma_eq_intro (Seq.slice last3 0 rem) b;
  Seq.lemma_eq_intro (Seq.slice last3 rem (rem + 1)) firstbyte;
  Seq.lemma_eq_intro (Seq.slice last3 (rem + 1) (fin - len_length a)) zeros;

  Seq.lemma_eq_intro (Seq.slice last3 0 fin) (Seq.append b pad)


val load_last_pad_lemma:
     a:sha2_alg
  -> len:size_nat{len <= max_input_length a}
  -> fin:size_nat{fin == block_length a \/ fin == 2 * block_length a}
  -> rem:size_nat{rem < block_length a}
  -> b:bytes{length b = rem} ->
  Lemma
   (let len':len_t a = Lib.IntTypes.cast #U32 #PUB (len_int_type a) PUB (size len) in
    let total_len_bits = secret (shift_left #(len_int_type a) len' 3ul) in
    let totlen_seq = BSeq.uint_to_bytes_be #(len_int_type a) total_len_bits in

    let firstbyte = create 1 (u8 0x80) in
    let zeros = create (pad0_length a len) (u8 0) in
    let pad = Seq.append (Seq.append firstbyte zeros) totlen_seq in
    PadFinish.pad a len == pad)

let load_last_pad_lemma a len fin rem b =
  let len':len_t a = Lib.IntTypes.cast #U32 #PUB (len_int_type a) PUB (size len) in
  let total_len_bits = secret (shift_left #(len_int_type a) len' 3ul) in
  assert (v total_len_bits == len * 8);

  let totlen_seq = BSeq.uint_to_bytes_be #(len_int_type a) total_len_bits in
  let firstbyte = create 1 (u8 0x80) in
  let zeros = create (pad0_length a len) (u8 0) in
  let pad = Seq.append (Seq.append firstbyte zeros) totlen_seq in
  Seq.lemma_eq_intro (PadFinish.pad a len) pad


val update_last_lemma:
     a:sha2_alg
  -> len:size_nat{len <= max_input_length a}
  -> b:lseq uint8 (len % block_length a) ->
  Lemma
  (let len':len_t a = Lib.IntTypes.cast #U32 #PUB (len_int_type a) PUB (size len) in
   let total_len_bits = secret (shift_left #(len_int_type a) len' 3ul) in
   let totlen_seq = BSeq.uint_to_bytes_be #(len_int_type a) total_len_bits in
   let blocksize = block_length a in
   let rem = len % blocksize in
   let blocks = padded_blocks a rem in
   let fin = blocks * block_length a in

   let last = create (2 * block_length a) (u8 0) in
   let last = update_sub last 0 rem b in
   let last = last.[rem] <- u8 0x80 in
   let last = update_sub last (fin - len_length a) (len_length a) totlen_seq in
   Seq.equal (Seq.slice last 0 fin) (Seq.append b (PadFinish.pad a len)))

let update_last_lemma a len b =
  let len':len_t a = Lib.IntTypes.cast #U32 #PUB (len_int_type a) PUB (size len) in
  let total_len_bits = secret (shift_left #(len_int_type a) len' 3ul) in
  let totlen_seq = BSeq.uint_to_bytes_be #(len_int_type a) total_len_bits in
  let blocksize = block_length a in
  let rem = len % blocksize in
  let blocks = padded_blocks a rem in
  let fin = blocks * block_length a in

  load_last_lemma a len totlen_seq b;
  load_last_pad_lemma a len fin rem b


val update_last_is_repeat_blocks_multi:
     a:sha2_alg
  -> len:size_nat{len <= max_input_length a}
  -> last:lseq uint8 (len % block_length a)
  -> st1:words_state a ->
  Lemma
  (requires
   (let blocksize = block_length a in
    (pad_length a len + len % blocksize) % blocksize = 0))
  (ensures
   (let len':len_t a = Lib.IntTypes.cast #U32 #PUB (len_int_type a) PUB (size len) in
    let pad_s = PadFinish.pad a len in
    let blocksize = block_length a in
    let rem = len % blocksize in
    let blocks1 = Seq.append last pad_s in
    update_last a len' rem last st1 ==
    repeat_blocks_multi blocksize blocks1 (update a) st1))

let update_last_is_repeat_blocks_multi a len last st1 =
  let pad_s = PadFinish.pad a len in
  let blocksize = block_length a in
  let rem = len % blocksize in
  let blocks1 = Seq.append last pad_s in
  append_pad_last_length_lemma a len;
  //assert (length blocks1 = blocksize \/ length blocks1 = 2 * blocksize);
  assert (length blocks1 == padded_blocks a rem * blocksize);
  let nb = padded_blocks a rem in
  Math.Lemmas.cancel_mul_mod nb blocksize;
  let res = repeat_blocks_multi blocksize blocks1 (update a) st1 in
  LSeq.lemma_repeat_blocks_multi blocksize blocks1 (update a) st1;
  assert (res == Loops.repeati nb (repeat_blocks_f blocksize blocks1 (update a) nb) st1);

  let len':len_t a = Lib.IntTypes.cast #U32 #PUB (len_int_type a) PUB (size len) in
  let total_len_bits = secret (shift_left #(len_int_type a) len' 3ul) in
  let totlen_seq = BSeq.uint_to_bytes_be #(len_int_type a) total_len_bits in
  let blocks = padded_blocks a rem in
  let fin = blocks * block_length a in
  let (b0, b1) = load_last a totlen_seq fin rem last in
  let st2 = update a b0 st1 in
  Loops.unfold_repeati nb (repeat_blocks_f blocksize blocks1 (update a) nb) st1 0;
  Loops.eq_repeati0 nb (repeat_blocks_f blocksize blocks1 (update a) nb) st1;
  update_last_lemma a len last;
  assert (st2 == repeat_blocks_f blocksize blocks1 (update a) nb 0 st1);

  if nb = 2 then begin
    let st3 = update a b1 st2 in
    Loops.unfold_repeati nb (repeat_blocks_f blocksize blocks1 (update a) nb) st1 1;
    assert (st3 == repeat_blocks_f blocksize blocks1 (update a) nb 1 st2) end


#push-options "--z3rlimit 150"
val hash_is_repeat_blocks_multi:
    a:sha2_alg
  -> len:size_nat{len <= max_input_length a}
  -> b:lseq uint8 len
  -> st0:words_state a ->
  Lemma
  (let len':len_t a = Lib.IntTypes.cast #U32 #PUB (len_int_type a) PUB (size len) in
   let pad_s = PadFinish.pad a len in
   repeat_blocks (block_length a) b (update a) (update_last a len') st0 ==
   repeat_blocks_multi (block_length a) (Seq.append b pad_s) (update a) st0)

let hash_is_repeat_blocks_multi a len b st0 =
  let pad_s = PadFinish.pad a len in
  let blocks = Seq.append b pad_s in
  let blocksize = block_length a in
  let nb = len / blocksize in
  let rem = len % blocksize in
  let len0 = nb * blocksize in
  Math.Lemmas.cancel_mul_mod nb blocksize;

  let res = repeat_blocks_multi blocksize blocks (update a) st0 in
  let blocks1 = Seq.slice blocks len0 (length blocks) in
  let blocks0 = Seq.slice blocks 0 len0 in
  let st1 = repeat_blocks_multi blocksize blocks0 (update a) st0 in
  LSeqLemmas.split_len_lemma0 blocksize (length blocks / blocksize) len0;
  LSeqLemmas.repeat_blocks_multi_split blocksize len0 blocks (update a) st0;
  //assert (res == repeat_blocks_multi blocksize blocks1 (update a) st1);

  let len':len_t a = Lib.IntTypes.cast #U32 #PUB (len_int_type a) PUB (size len) in
  LSeqLemmas.lemma_repeat_blocks_via_multi blocksize b (update a) (update_last a len') st0;
  Seq.lemma_eq_intro (Seq.slice b 0 len0) blocks0;
  let last = Seq.slice b len0 len in
  //assert (repeat_blocks blocksize b (update a) (update_last a len') st0 == update_last a len' rem last st1);
  Seq.lemma_eq_intro blocks1 (Seq.append last pad_s);
  update_last_is_repeat_blocks_multi a len last st1
#pop-options


let hash_agile_lemma #a len b =
  let st0 = Spec.Agile.Hash.init a in
  let pad_s = PadFinish.pad a len in
  let st_s = Spec.Agile.Hash.update_multi a st0 (Seq.append b pad_s) in
  hash_is_repeat_blocks a len b st0;
  update_multi_is_repeat_blocks_multi a len b st0 pad_s;
  hash_is_repeat_blocks_multi a len b st0;
  finish_lemma a st_s
