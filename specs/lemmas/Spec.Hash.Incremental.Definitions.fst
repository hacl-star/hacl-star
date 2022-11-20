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

(* An incremental specification better suited to a stateful API, allowing the
   client to perform the padding at the last minute upon hitting the last chunk of
   data. *)
let update_last (a:hash_alg)
  (hash:words_state' a)
  (prevlen:nat{prevlen % block_length a = 0})
  (input:bytes{(S.length input + prevlen) `less_than_max_input_length` a /\
    S.length input <= block_length a }):
  Tot (words_state' a)
=
  if is_blake a then
    Spec.Blake2.blake2_update_last (to_blake_alg a) prevlen (S.length input) input hash
  else if is_sha3 a then
    // VERY UNPLEASANT! Because of the lazy split for Blake2 we need to unroll...
    let rateInBytes = 1088 / 8 in
    let delimitedSuffix = byte 0x06 in
    let s = hash in
    let l = S.length input in
    if l = block_length a then
      let s = Spec.SHA3.absorb_inner rateInBytes input s in
      Spec.SHA3.absorb_last delimitedSuffix rateInBytes 0 S.empty s
    else
      Spec.SHA3.absorb_last delimitedSuffix rateInBytes (S.length input) input s
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

let hash_incremental (a:hash_alg) (input:bytes{S.length input `less_than_max_input_length` a}):
  Tot (hash:bytes{S.length hash = (hash_length a)})
=
  let s = init a in
  let bs, l = split_blocks a input in
  let s = update_multi a s bs in
  let s: words_state' a =
    if is_blake a then begin
      let s: words_state' a & nat = s in
      assert (snd s == S.length bs);
      fst s
    end else
      s
  in
  let s = update_last a s (S.length bs) l in
  finish a s
