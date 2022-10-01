module Spec.Blake2.Incremental

module S = FStar.Seq
module Blake2 = Spec.Blake2
module Loops = Lib.LoopCombinators

open Spec.Agile.Hash
open Spec.Hash.Definitions
open Spec.Hash.Incremental.Definitions
open Spec.Hash.PadFinish
open Spec.Hash.Lemmas
open FStar.Mul

val repeati_blake2_update1_is_update_multi
  (a:hash_alg{is_blake a}) (nb prev : nat)
  (d : bytes)
  (hash : words_state' a) :
  Lemma
  (requires (
    nb * block_length a <= Seq.length d /\
    prev + Seq.length d <= Blake2.max_limb (to_blake_alg a) /\
    prev + nb * block_length a <= max_extra_state a))
  (ensures (
    (**) nb_blocks_props a nb prev (Seq.length d);
    let blocks, _ = Seq.split d (nb * block_length a) in
    (Loops.repeati #(words_state' a) nb (Blake2.blake2_update1 (to_blake_alg a) prev d) hash,
     nat_to_extra_state a (prev + nb * block_length a)) ==
       update_multi a (hash, nat_to_extra_state a prev) blocks))

val blake2_is_hash_incremental
  (a : blake_alg)
  (input : bytes {S.length input `less_than_max_input_length` a}) :
  Lemma (
    S.equal (Blake2.blake2 (to_blake_alg a) input 0 Seq.empty (Spec.Blake2.max_output (to_blake_alg a)))
            (hash_incremental a input))
