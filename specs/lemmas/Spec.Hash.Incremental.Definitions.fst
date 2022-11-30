module Spec.Hash.Incremental.Definitions

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
