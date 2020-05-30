module Spec.Hash.Incremental

module S = FStar.Seq

open Spec.Agile.Hash
open Spec.Hash.Definitions
open Spec.Hash.PadFinish
open FStar.Mul
open Lib.IntTypes

#reset-options "--fuel 0 --ifuel 0 --z3rlimit 100"

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
  (input:bytes{S.length input + prevlen <= max_input_length a}):
  Tot (words_state a)
  = let blocks, last_block, rem = last_split_blake a input in
    let h' = update_multi a hash blocks in
    let ev' = extra_state_add_nat (snd h') rem in // (v (snd h' +. u64 rem))
    let h_f = Spec.Blake2.blake2_update_block (to_blake_alg a) true (extra_state_v ev')
                                              last_block (fst h') in
    (h_f, nat_to_extra_state a 0)

(* An incremental specification better suited to a stateful API, allowing the
   client to perform the padding at the last minute upon hitting the last chunk of
   data. *)
let update_last (a:hash_alg)
  (hash:words_state a)
  (prevlen:nat{prevlen % block_length a = 0})
  (input:bytes{S.length input + prevlen <= max_input_length a}):
  Tot (words_state a)
=
  if is_blake a then
    update_last_blake a hash prevlen input
  else
  let total_len = prevlen + S.length input in
  let padding = pad a total_len in
  update_multi a hash S.(input @| padding)

let split_blocks (a:hash_alg) (input:bytes)
  : Pure (bytes & bytes)
    (requires S.length input <= max_input_length a)
    (ensures fun (l, r) ->
      S.length l % block_length a == 0 /\
      S.length r <= block_length a /\
      S.append l r == input)
  = let open FStar.Mul in
    let n = S.length input / block_length a in
    // Ensuring that we always handle one block in update_last
    let n = if S.length input % block_length a = 0 && n > 0 then n-1 else n in
    let bs, l = S.split input (n * block_length a) in
    S.lemma_split input (n * block_length a);
    bs, l

let hash_incremental_body
  (a:hash_alg)
  (input:bytes{S.length input <= max_input_length a})
  (s:words_state a)
  : Tot (words_state a)
  = let bs, l = split_blocks a input in
    let s = update_multi a s bs in
    update_last a s (S.length bs) l

let hash_incremental (a:hash_alg) (input:bytes{S.length input <= (max_input_length a)}):
  Tot (hash:bytes{S.length hash = (hash_length a)})
= let s = init a in
  let s = hash_incremental_body a input s in
  finish a s

let hash = Spec.Agile.Hash.hash

val hash_is_hash_incremental (a: hash_alg) (input: bytes { S.length input <= max_input_length a }):
  Lemma (ensures (S.equal (hash a input) (hash_incremental a input)))
