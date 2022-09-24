module Spec.Hash.Incremental

module S = FStar.Seq
module Blake2 = Spec.Blake2

open Spec.Agile.Hash
open Spec.Hash.Definitions
open Spec.Hash.PadFinish

open FStar.Mul
open Lib.Sequence
open Lib.ByteSequence
open Lib.IntTypes

module Loops = Lib.LoopCombinators
module UpdateMulti = Lib.UpdateMulti

#set-options "--fuel 0 --ifuel 0 --z3rlimit 50"

/// A declaration whose sole purpose is to force synchronize the .fst and the .fsti
[@must_erase_for_extraction]
private val _sync_decl : Type0

let last_split_blake (a:hash_alg{is_blake a}) (input:bytes)
  : Pure (bytes & bytes & nat)
    (requires True)
    (ensures fun (b, l, rem) ->
      S.length b % block_length a == 0 /\
      S.length l == block_length a /\
      rem <= block_length a /\
      rem <= S.length input)
  = let (nb, rem) = Spec.Blake2.split (to_blake_alg a) (S.length input) in
    let blocks = Seq.slice input 0 (nb * block_length a) in
    let last_block = Spec.Blake2.get_last_padded_block (to_blake_alg a) input rem in
    blocks, last_block, rem

let update_last_blake (a:hash_alg{is_blake a})
  (hash:words_state a)
  (prevlen:nat{prevlen % block_length a = 0})
  (input:bytes{(S.length input + prevlen) `less_than_max_input_length` a}):
  Tot (words_state a)
  = let blocks, last_block, rem = last_split_blake a input in
    let h' = update_multi a hash blocks in
    let ev' = extra_state_add_nat (snd h') rem in
    let h_f = Spec.Blake2.blake2_update_block (to_blake_alg a) true (extra_state_v ev')
                                              last_block (fst h') in
    (h_f, nat_to_extra_state a 0)

(* An incremental specification better suited to a stateful API, allowing the
   client to perform the padding at the last minute upon hitting the last chunk of
   data. *)
let update_last (a:hash_alg)
  (hash:words_state a)
  (prevlen:nat{prevlen % block_length a = 0})
  (input:bytes{(S.length input + prevlen) `less_than_max_input_length` a /\
    S.length input <= block_length a }):
  Tot (words_state a)
=
  if is_blake a then
    update_last_blake a hash prevlen input
  else if is_sha3 a then
    // VERY UNPLEASANT! Because of the lazy split for Blake2 we need to unroll...
    let rateInBytes = 1088 / 8 in
    let delimitedSuffix = byte 0x06 in
    let s, _ = hash in
    let l = S.length input in
    if l = block_length a then
      let s = Spec.SHA3.absorb_inner rateInBytes input s in
      Spec.SHA3.absorb_last delimitedSuffix rateInBytes 0 S.empty s, ()
    else
      Spec.SHA3.absorb_last delimitedSuffix rateInBytes (S.length input) input s, ()
  else
    let total_len = prevlen + S.length input in
    let padding = pad a total_len in
    (**) Math.Lemmas.lemma_mod_add_distr (S.length input + S.length padding) prevlen (block_length a);
    (**) assert(S.length S.(input @| padding) % block_length a = 0);
    update_multi a hash S.(input @| padding)

let split_blocks (a:hash_alg) (input:bytes)
  : Pure (bytes & bytes)
    (requires S.length input `less_than_max_input_length` a)
    (ensures fun (bs, l) ->
      S.length bs % block_length a = 0 /\
      S.length l <= block_length a /\
      S.append bs l == input) =
  UpdateMulti.split_at_last_lazy (block_length a) input

let hash_incremental_body
  (a:hash_alg)
  (input:bytes{S.length input `less_than_max_input_length` a})
  (s:words_state a)
  : Tot (words_state a)
  = let bs, l = split_blocks a input in
    let s = update_multi a s bs in
    update_last a s (S.length bs) l

let hash_incremental (a:hash_alg) (input:bytes{S.length input `less_than_max_input_length` a}):
  Tot (hash:bytes{S.length hash = (hash_length a)})
= let s = init a in
  let s = hash_incremental_body a input s in
  finish a s

let hash = Spec.Agile.Hash.hash

/// Auxiliary lemma to help type postconditions
private
val nb_blocks_props :
  a:hash_alg{is_blake a} -> nb : nat -> prev : nat -> data_length : nat ->
  Lemma
  (requires (
    nb * block_length a <= data_length /\
    prev + data_length <= Blake2.max_limb (to_blake_alg a) /\
    prev + nb * block_length a <= max_extra_state a))
  (ensures (
    nb * block_length a >= 0 /\
    nb <= data_length / Spec.Blake2.size_block (to_blake_alg a) /\
    nb * block_length a % block_length a = 0))

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
  (a: hash_alg{is_blake a})
  (input : bytes {S.length input `less_than_max_input_length` a}) :
  Lemma (
    let kk = 0 in
    let k = Seq.empty in
    S.equal (Blake2.blake2 (to_blake_alg a) input kk k (Spec.Blake2.max_output (to_blake_alg a)))
            (hash_incremental a input))

val sha3_state_is_hash_state: squash (words_state' SHA3_256 == Spec.SHA3.state)

val hash_is_hash_incremental (a: hash_alg) (input: bytes { S.length input `less_than_max_input_length` a }):
  Lemma (S.equal (hash a input) (hash_incremental a input))
