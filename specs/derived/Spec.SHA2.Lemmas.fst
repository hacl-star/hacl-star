module Spec.SHA2.Lemmas
module S = FStar.Seq

friend Spec.SHA2

open Spec.Hash.Definitions
open Spec.SHA2

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
