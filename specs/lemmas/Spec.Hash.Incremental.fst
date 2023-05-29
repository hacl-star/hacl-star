module Spec.Hash.Incremental

module S = FStar.Seq
module Blake2 = Spec.Blake2

open Spec.Agile.Hash
open Spec.Hash.Definitions

friend Spec.Agile.Hash

open FStar.Mul
module Loops = Lib.LoopCombinators

#set-options "--fuel 0 --ifuel 0 --z3rlimit 50"

/// A declaration whose sole purpose is to force synchronize the .fst and the .fsti
let _sync_decl = unit



let hash_is_hash_incremental' (a: hash_alg) (input: bytes { S.length input `less_than_max_input_length` a }) l =
  if is_blake a then
    Spec.Blake2.Incremental.blake2_is_hash_incremental a input
  else if is_keccak a then
    Spec.SHA3.Incremental.sha3_is_incremental a input l
  else
    Spec.MD.Incremental.md_is_hash_incremental a input (init a)
