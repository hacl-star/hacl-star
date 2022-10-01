module Spec.MD.Incremental

module S = FStar.Seq

open Spec.Agile.Hash
open Spec.Hash.Definitions
open Spec.Hash.PadFinish
open Spec.Hash.Lemmas

friend Spec.Agile.Hash

open FStar.Mul

#set-options "--fuel 0 --ifuel 0 --z3rlimit 50"

#push-options "--z3rlimit 150"
let md_is_hash_incremental
  (a:hash_alg{is_md a})
  (input: bytes { S.length input `less_than_max_input_length` a })
  (s:words_state a)
  : Lemma (
      let blocks, rest = split_blocks a input in
      update_multi a s (input `S.append` (pad a (S.length input))) ==
      update_last a (update_multi a s blocks) (S.length blocks) rest)
   = let blocks, rest = split_blocks a input in
     assert (S.length input == S.length blocks + S.length rest);
     let padding = pad a (S.length input) in
     calc (==) {
       update_last a (update_multi a s blocks) (S.length blocks) rest;
       (==) { }
       update_multi a (update_multi a s blocks) S.(rest @| padding);
       (==) { update_multi_associative a s blocks S.(rest @| padding) }
       update_multi a s S.(blocks @| (rest @| padding));
       (==) { S.append_assoc blocks rest padding }
       update_multi a s S.((blocks @| rest) @| padding);
       (==) { }
       update_multi a s S.(input @| padding);
     }
#pop-options
