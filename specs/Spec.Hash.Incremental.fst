module Spec.Hash.Incremental

module S = FStar.Seq

open Spec.Hash
open Spec.Hash.Helpers

(* Compress full blocks, then pad the partial block and compress the last block *)
let update_last (a:hash_alg)
  (hash:hash_w a)
  (prevlen:nat{prevlen % size_block a = 0})
  (input:bytes{S.length input + prevlen < max_input8 a}):
  Tot (hash_w a)
=
  let total_len = prevlen + S.length input in
  let blocks = pad a total_len in
  update_multi a hash S.(input @| blocks)

let hash_incremental (a:hash_alg) (input:bytes{S.length input < (max_input8 a)}):
  Tot (hash:bytes{S.length hash = (size_hash a)})
=
  let open FStar.Mul in
  let n = S.length input / (size_block a) in
  let (bs,l) = S.split input (n * (size_block a)) in
  let hash = update_multi a (init a) bs in
  let hash = update_last a hash (n * (size_block a)) l in
  finish a hash

#set-options "--max_fuel 0 --max_ifuel 0"

let hash = Spec.Hash.Nist.hash

let hash_is_hash_incremental (a: hash_alg) (input: bytes { S.length input < max_input8 a }):
  Lemma (ensures (hash a input == hash_incremental a input))
=
  let open FStar.Mul in
  let n = S.length input / size_block a in
  // From hash:
  let padded_input = S.(input @| pad a (S.length input)) in
  let blocks, rest = split_block a padded_input n in
  update_multi_associative a (init a) padded_input (n * size_block a);
  assert (hash a input == finish a (update_multi a (update_multi a (init a) blocks) rest));
  // From hash_incremental:
  let blocks', rest' = S.split input (n * size_block a) in
  assert (hash_incremental a input ==
    finish a (update_last a (update_multi a (init a) blocks') (n * size_block a) rest'));
  // Then.
  assert (Seq.equal blocks blocks');
  assert (Seq.equal rest S.(rest' @| pad a (length input)));
  assert (
    let padding = pad a (S.length input) in
    hash_incremental a input ==
    finish a (update_multi a (update_multi a (init a) blocks) rest));
  ()
