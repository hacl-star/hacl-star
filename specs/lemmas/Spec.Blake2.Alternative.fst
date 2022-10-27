module Spec.Blake2.Alternative

open Spec.Blake2

open FStar.Mul
open Lib.IntTypes
open Lib.RawIntTypes
open Lib.Sequence
open Lib.ByteSequence
open Lib.LoopCombinators
module Lems = Lib.Sequence.Lemmas
module UpdateMulti = Lib.UpdateMulti

#set-options "--fuel 0 --ifuel 0 --z3rlimit 50"

val lemma_shift_update_last:
    a:alg
  -> rem: nat
  -> b:block_s a
  -> d:bytes{length d + (size_block a) <= max_limb a /\ rem <= length d /\ rem <= size_block a}
  -> s:state a ->
  Lemma (
    blake2_update_last a 0 rem (b `Seq.append` d) s ==
    blake2_update_last a (size_block a) rem d s
  )

let lemma_shift_update_last a rem b d s =
  let m = b `Seq.append` d in
  assert (Seq.slice m (length m - rem) (length m) `Seq.equal` Seq.slice d (length d - rem) (length d));
  assert (get_last_padded_block a (b `Seq.append` d) rem == get_last_padded_block a d rem)

val lemma_update1_shift:
    a:alg
  -> b:block_s a
  -> d:bytes{length d + (size_block a) <= max_limb a}
  -> i:nat{i < length d / size_block a /\ (size_block a) + length d <= max_limb a}
  -> s:state a ->
  Lemma (
    blake2_update1 a 0 (b `Seq.append` d) (i + 1) s == blake2_update1 a (size_block a) d i s
  )

let lemma_update1_shift a b d i s =
  assert (get_blocki a (b `Seq.append` d) (i + 1) `Seq.equal` get_blocki a d i)

val repeati_update1:
    a:alg
  -> b:block_s a
  -> d:bytes{length d + (size_block a) <= max_limb a}
  -> nb:nat{nb > 0 /\ nb <= length (b `Seq.append` d) / size_block a}
  -> s:state a ->
  Lemma (
    repeati nb (blake2_update1 a 0 (b `Seq.append` d)) s ==
    repeati (nb - 1) (blake2_update1 a (size_block a) d) (blake2_update_block a false (size_block a) b s)
  )

#push-options "--z3rlimit 100"
let repeati_update1 a b d nb s =
  let f = blake2_update1 a 0 (b `Seq.append` d) in
  let f' = blake2_update1 a (size_block a) d in
  let s' = blake2_update_block a false (size_block a) b s in
  Classical.forall_intro_2 (lemma_update1_shift a b d);
  assert (forall i s. f (i + 1) s == f' i s);
  Lems.repeati_right_shift (nb - 1) f' f s;
  assert (get_blocki a (b `Seq.append` d) 0 `Seq.equal` b);
  assert (s' == f 0 s)
#pop-options

val lemma_unfold_update_blocks:
    a:alg
  -> b:block_s a
  -> d:bytes{length d > 0 /\ length d + (size_block a) <= max_limb a}
  -> s:state a ->
  Lemma (
    blake2_update_blocks a 0 (b `Seq.append` d) s ==
    blake2_update_blocks a (size_block a) d (blake2_update_block a false (size_block a) b s)
  )

val split_one_more_block:
    a:alg
  -> b:block_s a
  -> d:bytes{length d > 0} ->
  Lemma (
    let nb, rem = split a (length (b `Seq.append` d)) in
    let nb', rem' = split a (length d) in
    nb == nb' + 1 /\ rem == rem')

let split_one_more_block a b d = ()

let lemma_unfold_update_blocks a b d s =
  let nb, rem = split a (length (b `Seq.append` d)) in
  let nb', rem' = split a (length d) in
  // The condition `length d > 0` is needed for this assertion, otherwise,
  // we would have rem = size_block a and rem' = 0
  split_one_more_block a b d;
  repeati_update1 a b d nb s;
  let s_int = repeati nb (blake2_update1 a 0 (b `Seq.append` d)) s in
  lemma_shift_update_last a rem b d s_int

#push-options "--fuel 0 --ifuel 0 --z3rlimit 1000"
let lemma_spec_equivalence_update a kk k d s =
  let ll = length d in
  let key_block: bytes = if kk > 0 then blake2_key_block a kk k else Seq.empty in
  if kk = 0 then begin
    assert (key_block `Seq.equal` Seq.empty);
    assert ((key_block `Seq.append` d) `Seq.equal` d);
    ()
  end else if ll = 0 then
    let (nb,rem) = split a (length (blake2_key_block a kk k)) in
    // let s = repeati nb (blake2_update1 a prev (blake2_key_block a kk k)) s in
    calc (Seq.equal) {
      blake2_update a kk k d s;
    (Seq.equal) {}
      blake2_update_key a kk k ll s;
    (Seq.equal) {}
      blake2_update_block a true (size_block a) (blake2_key_block a kk k) s;
    (Seq.equal) { Lib.LoopCombinators.eq_repeati0 nb (blake2_update1 a 0 (blake2_key_block a kk k)) s }
      blake2_update_blocks a 0 (blake2_key_block a kk k) s;
    (Seq.equal) { Seq.append_empty_r (blake2_key_block a kk k) }
      blake2_update_blocks a 0 (blake2_key_block a kk k `Seq.append` Seq.empty) s;
    (Seq.equal) { Seq.lemma_empty d }
      blake2_update_blocks a 0 (blake2_key_block a kk k `Seq.append` d) s;
    (Seq.equal) { }
      blake2_update' a kk k d s;
    };
    ()
  else
    let (nb,rem) = split a (length (blake2_key_block a kk k `Seq.append` d)) in
    calc (Seq.equal) {
      blake2_update a kk k d s;
    (Seq.equal) {}
      blake2_update_blocks a (size_block a) d (blake2_update_key a kk k ll s);
    (Seq.equal) {}
      blake2_update_blocks a (size_block a) d (blake2_update_block a false (size_block a) (blake2_key_block a kk k) s);
    (Seq.equal) { lemma_unfold_update_blocks a (blake2_key_block a kk k) d s }
      blake2_update_blocks a 0 (blake2_key_block a kk k `Seq.append` d) s;
    }
#pop-options
