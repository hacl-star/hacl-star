module Spec.Hash.Incremental

module S = FStar.Seq

open Spec.Hash
open Spec.Hash.Definitions
open Spec.Hash.PadFinish

#set-options "--max_fuel 0 --max_ifuel 0 --z3rlimit 300"

(* An incremental specification better suited to a stateful API, allowing the
   client to perform the padding at the last minute upon hitting the last chunk of
   data. *)
let update_last (a:hash_alg)
  (hash:hash_w a)
  (prevlen:nat{prevlen % size_block a = 0})
  (input:bytes{S.length input + prevlen < max_input8 a}):
  Tot (hash_w a)
=
  let total_len = prevlen + S.length input in
  let padding = pad a total_len in
  update_multi a hash S.(input @| padding)

let hash_incremental (a:hash_alg) (input:bytes{S.length input < (max_input8 a)}):
  Tot (hash:bytes{S.length hash = (size_hash a)})
=
  let open FStar.Mul in
  let n = S.length input / (size_block a) in
  let bs, l = S.split input (n * (size_block a)) in
  let hash = update_multi a (init a) bs in
  let hash = update_last a hash (n * (size_block a)) l in
  finish a hash
