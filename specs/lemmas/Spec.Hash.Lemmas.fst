module Spec.Hash.Lemmas

module S = FStar.Seq
open Lib.IntTypes

open Spec.Agile.Hash
open Spec.Hash.Definitions

friend Spec.Agile.Hash

(** Lemmas about the behavior of update_multi / update_last *)

#push-options "--fuel 0 --ifuel 1 --z3rlimit 50"

let update_multi_zero a h =
  match a with
  | MD5 | SHA1 | SHA2_224 | SHA2_256 | SHA2_384 | SHA2_512 ->
    Lib.UpdateMulti.update_multi_zero (block_length a) (Spec.Agile.Hash.update a) h
  | SHA3_224 | SHA3_256 | SHA3_384 | SHA3_512 | Shake128 | Shake256 ->
    let rateInBytes = rate a / 8 in
    let f = Spec.SHA3.absorb_inner rateInBytes in
    Lib.Sequence.lemma_repeat_blocks_multi rateInBytes S.empty f h;

    let nb = 0 / rateInBytes in
    Lib.LoopCombinators.eq_repeati0 nb (Lib.Sequence.repeat_blocks_f rateInBytes S.empty f nb) h

let update_multi_zero_blake a prevlen h =
  Lib.LoopCombinators.eq_repeati0 (0 / block_length a) (Spec.Blake2.blake2_update1 (to_blake_alg a) prevlen S.empty) h
#pop-options

#push-options "--fuel 1"
let update_multi_update (a: md_alg) (h: words_state a) (input: bytes_block a): Lemma
  (ensures (update_multi a h () input) == (update a h input))
=
  let h1 = update_multi a h () input in
  assert(h1 == Lib.UpdateMulti.mk_update_multi (block_length a) (update a) h input);
  if S.length input = 0 then
    begin
    assert(h1 == h)
    end
  else
    begin
    let block, rem = Lib.UpdateMulti.split_block (block_length a) input 1 in
    let h2 = update a h block in
    assert(rem `Seq.equal` Seq.empty);
    assert(block `Seq.equal` input);
    let h3 = Lib.UpdateMulti.mk_update_multi (block_length a) (update a) h2 rem in
    assert(h1 == h3)
    end
#pop-options

let update_multi_associative (a: hash_alg{not (is_blake a)})
  (h: words_state a)
  (input1: bytes)
  (input2: bytes):
  Lemma
  (requires
    S.length input1 % block_length a == 0 /\
    S.length input2 % block_length a == 0)
  (ensures (
    let input = S.append input1 input2 in
    S.length input % block_length a == 0 /\
    update_multi a (update_multi a h () input1) () input2 == update_multi a h () input))
  = match a with
  | MD5 | SHA1 | SHA2_224 | SHA2_256 | SHA2_384 | SHA2_512 ->
    Lib.UpdateMulti.update_multi_associative (block_length a) (Spec.Agile.Hash.update a) h input1 input2
  | SHA3_224 | SHA3_256 | SHA3_384 | SHA3_512 | Shake128 | Shake256 ->
    let rateInBytes = rate a /8 in
    let f = Spec.SHA3.absorb_inner rateInBytes in
    let input = input1 `S.append` input2 in
    assert (input1 `S.equal` S.slice input 0 (S.length input1));
    assert (input2 `S.equal` S.slice input (S.length input1) (S.length input));
    Lib.Sequence.Lemmas.repeat_blocks_multi_split (block_length a) (S.length input1) input f h

let lemma_blocki_aux1 (a:blake_alg) (s1 s2:bytes) (i:nat{i < S.length s1 / block_length a})
  : Lemma (Spec.Blake2.get_blocki (to_blake_alg a) s1 i == Spec.Blake2.get_blocki (to_blake_alg a) (S.append s1 s2) i)
  = assert (Spec.Blake2.get_blocki (to_blake_alg a) s1 i `S.equal` Spec.Blake2.get_blocki (to_blake_alg a) (S.append s1 s2) i)

#push-options "--fuel 0 --ifuel 0 --z3rlimit 300"

open FStar.Mul

let lemma_blocki_aux2 (a:blake_alg) (s1 s2:bytes) (nb1 nb2:nat) (i:nat{i < nb2})
  : Lemma
    (requires
      S.length s1 == nb1 * block_length a /\
      S.length s2 == nb2 * block_length a)
    (ensures Spec.Blake2.get_blocki (to_blake_alg a) s2 i ==
           Spec.Blake2.get_blocki (to_blake_alg a) (S.append s1 s2) (i + nb1))
  = let s = s1 `S.append` s2 in
    let a' = to_blake_alg a in
    calc (==) {
          Spec.Blake2.get_blocki a' s (i + nb1);
          (==) { }
          S.slice s ((i + nb1) * block_length a) ((i + nb1 + 1) * block_length a);
          (==) { }
          S.slice s (i * block_length a + nb1 * block_length a) ((i + 1) * block_length a + nb1 * block_length a);
          (==) { }
          S.slice s (i * block_length a + S.length s1) ((i + 1) * block_length a + S.length s1);
          (==) { S.slice_slice s (S.length s1) (S.length s) (i * block_length a) ((i+1) * block_length a) }
          S.slice (S.slice s (S.length s1) (S.length s)) (i * block_length a) ((i+1) * block_length a);
          (==) { S.append_slices s1 s2; assert (s2 `S.equal` S.slice s (S.length s1) (S.length s)) }
          S.slice s2 (i * block_length a) ((i+1) * block_length a);
          (==) { }
          Spec.Blake2.get_blocki a' s2 i;
        }

let lemma_update_aux2 (a:blake_alg) (s1 s2:bytes) (nb1 nb2:nat) (prevlen1 prevlen2:nat) (i:nat{i < nb2}) (acc:words_state a)
  : Lemma
    (requires
      S.length s1 == nb1 * block_length a /\
      S.length s2 == nb2 * block_length a /\
      prevlen1 % block_length a == 0 /\
      prevlen2 = prevlen1 + S.length s1 /\
      (S.length (S.append s1 s2) + prevlen1) `less_than_max_input_length` a)
    (ensures
      Spec.Blake2.blake2_update1 (to_blake_alg a) prevlen1 (s1 `S.append` s2) (i + nb1) acc ==
      Spec.Blake2.blake2_update1 (to_blake_alg a) prevlen2 s2 i acc)
  = let s = s1 `S.append` s2 in
    let a' = to_blake_alg a in

    let open Spec.Blake2 in
    let f1 = blake2_update1 (to_blake_alg a) prevlen1 s in
    let f2 = blake2_update1 (to_blake_alg a) prevlen2 s2 in
    let totlen1 = prevlen1 + (i + nb1 + 1) * size_block a' in
    let totlen2 = prevlen2 + (i + 1) * size_block a' in
    // Proving totlen1 == totlen2 for the last calc step below
    calc (==) {
      totlen2;
      (==) { }
      prevlen2 + (i + 1) * block_length a;
      (==) { }
      prevlen1 + S.length s1 + (i + 1) * block_length a;
      (==) { }
      prevlen1 + nb1 * block_length a + (i + 1) * block_length a;
      (==) { Math.Lemmas.distributivity_add_left (i + 1) nb1 (block_length a) }
      prevlen1 + (i + 1 + nb1) * block_length a;
      (==) { }
      totlen1;
    };

    calc (==) {
      f1 (i + nb1) acc;
      (==) { }
      blake2_update_block a' false totlen1 (get_blocki a' s (i + nb1)) acc;
      (==) { lemma_blocki_aux2 a s1 s2 nb1 nb2 i }
      blake2_update_block a' false totlen1 (get_blocki a' s2 i) acc;
      (==) { }
      f2 i acc;

    }

let update_multi_associative_blake (a: blake_alg)
  (h: words_state a)
  (prevlen1: nat)
  (prevlen2: nat)
  (input1: bytes)
  (input2: bytes):
  Lemma
  (requires (
    prevlen1 % block_length a == 0 /\
    S.length input1 % block_length a == 0 /\
    S.length input2 % block_length a == 0 /\
    prevlen2 = prevlen1 + S.length input1 /\
    update_multi_pre a prevlen1 (S.append input1 input2)))
  (ensures (
    let input = S.append input1 input2 in
    S.length input % block_length a == 0 /\
    update_multi_pre a prevlen1 input1 /\
    update_multi_pre a prevlen2 input2 /\
    update_multi a (update_multi a h prevlen1 input1) prevlen2 input2 == update_multi a h prevlen1 input))
  = let input = S.append input1 input2 in
    let nb1 = S.length input1 / block_length a in
    let nb2 = S.length input2 / block_length a in
    let nb = S.length input / block_length a in
    let a' = to_blake_alg a in
    let f = Spec.Blake2.blake2_update1 a' prevlen1 input in
    let f1 = Spec.Blake2.blake2_update1 a' prevlen1 input1 in
    let f2 = Spec.Blake2.blake2_update1 a' prevlen2 input2 in
    let aux1 (i:nat{i < nb1}) (acc:words_state a) : Lemma (f i acc == f1 i acc)
      = lemma_blocki_aux1 a input1 input2 i
    in
    let open FStar.Mul in
    let aux2 (i:nat{i < nb2}) (acc:words_state a) : Lemma (f (i + nb1) acc == f2 i acc)
      = lemma_update_aux2 a input1 input2 nb1 nb2 prevlen1 prevlen2 i acc
    in
    let open Lib.LoopCombinators in
    let open Lib.Sequence.Lemmas in
    let fix = fixed_a (words_state a) in
    calc (==) {
      update_multi a h prevlen1 input;
      (==) { }
      repeati #(words_state a) nb f h;
      (==) { repeati_def nb f h }
      repeat_right 0 nb fix f h;
      (==) { repeat_right_plus 0 nb1 nb fix f h; repeati_def nb1 f h }
      repeat_right nb1 nb fix f (repeati nb1 f h);
      (==) { Classical.forall_intro_2 aux1; repeati_extensionality nb1 f f1 h }
      repeat_right nb1 nb fix f (update_multi a h prevlen1 input1);
      (==) { Classical.forall_intro_2 aux2; repeat_gen_right_extensionality nb2 nb1 fix fix f2 f (update_multi a h prevlen1 input1) }
      repeat_right 0 nb2 fix f2 (update_multi a h prevlen1 input1);
      (==) { repeati_def nb2 f2 (update_multi a h prevlen1 input1) }
      update_multi a (update_multi a h prevlen1 input1) prevlen2 input2;
    }

(* *)
let block_length_smaller_than_max_input (a:hash_alg) =
  normalize_term_spec(pow2 61 - 1);
  normalize_term_spec(pow2 125 - 1);
  normalize_term_spec(pow2 64 - 1)
