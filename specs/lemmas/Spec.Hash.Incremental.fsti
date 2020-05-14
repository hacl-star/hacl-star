module Spec.Hash.Incremental

module S = FStar.Seq

open Spec.Agile.Hash
open Spec.Hash.Definitions
open Spec.Hash.PadFinish
open FStar.Mul
open Lib.IntTypes

#set-options "--max_fuel 0 --max_ifuel 0 --z3rlimit 300"

let update_last_blake (a:hash_alg{is_blake a})
  (hash:words_state a)
  (prevlen:nat{prevlen % block_length a = 0})
  (input:bytes{S.length input + prevlen <= max_input_length a}):
  Tot (words_state a)
  = let (nb, rem) = Spec.Blake2.split (to_blake_alg a) (S.length input) in
    let blocks = Seq.slice input 0 (nb * block_length a) in
    let (h', totlen) = update_multi a hash blocks in
    let last_block = Spec.Blake2.get_last_padded_block (to_blake_alg a) input rem in
    (Spec.Blake2.blake2_update_block (to_blake_alg a) true (v (totlen +. u64 rem)) last_block h', u64 0)

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

let hash_incremental (a:hash_alg) (input:bytes{S.length input <= (max_input_length a)}):
  Tot (hash:bytes{S.length hash = (hash_length a)})
=
  let open FStar.Mul in
  let n = S.length input / (block_length a) in
  // Ensuring that we always handle one block in update_last
  let n = if S.length input % block_length a = 0 && n > 0 then n-1 else n in
  let bs, l = S.split input (n * (block_length a)) in
  let hash = update_multi a (init a) bs in
  let hash = update_last a hash (n * (block_length a)) l in
  finish a hash

val concatenated_hash_incremental (a:hash_alg) (inp1:bytes_blocks a) (inp2:bytes)
  : Lemma
    (requires Seq.length (inp1 `S.append` inp2) <= max_input_length a /\ Seq.length inp2 > 0)
    (ensures finish a (update_last a (update_multi a (init a) inp1) (S.length inp1) inp2)
      `S.equal` hash_incremental a (inp1 `S.append` inp2))
