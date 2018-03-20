module Spec.Hash

open Spec.SHA2

#reset-options "--max_fuel 0 --z3rlimit 25"

inline_for_extraction
private let parameters a = match a with
  | SHA2_224 -> Spec.SHA2.parameters224
  | SHA2_256 -> Spec.SHA2.parameters256
  | SHA2_384 -> Spec.SHA2.parameters384
  | SHA2_512 -> Spec.SHA2.parameters512

let state a = match a with
  | SHA2_224 -> Spec.SHA2.state (parameters a)
  | SHA2_256 -> Spec.SHA2.state (parameters a)
  | SHA2_384 -> Spec.SHA2.state (parameters a)
  | SHA2_512 -> Spec.SHA2.state (parameters a)

let size_block a = match a with
  | SHA2_224 -> Spec.SHA2.size_block (parameters a)
  | SHA2_256 -> Spec.SHA2.size_block (parameters a)
  | SHA2_384 -> Spec.SHA2.size_block (parameters a)
  | SHA2_512 -> Spec.SHA2.size_block (parameters a)

let size_hash a = match a with
  | SHA2_224 -> Spec.SHA2.size_hash (parameters a)
  | SHA2_256 -> Spec.SHA2.size_hash (parameters a)
  | SHA2_384 -> Spec.SHA2.size_hash (parameters a)
  | SHA2_512 -> Spec.SHA2.size_hash (parameters a)

let max_input a = match a with
  | SHA2_224 -> Spec.SHA2.max_input (parameters a)
  | SHA2_256 -> Spec.SHA2.max_input (parameters a)
  | SHA2_384 -> Spec.SHA2.max_input (parameters a)
  | SHA2_512 -> Spec.SHA2.max_input (parameters a)

let get_st_n #a (st:state a) = match a with
  | SHA2_224 -> Spec.SHA2.get_st_n #(parameters a) st
  | SHA2_256 -> Spec.SHA2.get_st_n #(parameters a) st
  | SHA2_384 -> Spec.SHA2.get_st_n #(parameters a) st
  | SHA2_512 -> Spec.SHA2.get_st_n #(parameters a) st

let get_st_len_block #a (st:state a) = match a with
  | SHA2_224 -> Spec.SHA2.get_st_len_block #(parameters a) st
  | SHA2_256 -> Spec.SHA2.get_st_len_block #(parameters a) st
  | SHA2_384 -> Spec.SHA2.get_st_len_block #(parameters a) st
  | SHA2_512 -> Spec.SHA2.get_st_len_block #(parameters a) st

let number_blocks_padding_single a l = match a with
  | SHA2_224 -> Spec.SHA2.number_blocks_padding_single (parameters a) l
  | SHA2_256 -> Spec.SHA2.number_blocks_padding_single (parameters a) l
  | SHA2_384 -> Spec.SHA2.number_blocks_padding_single (parameters a) l
  | SHA2_512 -> Spec.SHA2.number_blocks_padding_single (parameters a) l

let init a = match a with
  | SHA2_224 -> Spec.SHA2.init (parameters a)
  | SHA2_256 -> Spec.SHA2.init (parameters a)
  | SHA2_384 -> Spec.SHA2.init (parameters a)
  | SHA2_512 -> Spec.SHA2.init (parameters a)

let update_block a b s = match a with
  | SHA2_224 -> Spec.SHA2.update_block (parameters a) b s
  | SHA2_256 -> Spec.SHA2.update_block (parameters a) b s
  | SHA2_384 -> Spec.SHA2.update_block (parameters a) b s
  | SHA2_512 -> Spec.SHA2.update_block (parameters a) b s

let update_multi a n b s = match a with
  | SHA2_224 -> Spec.SHA2.update_multi (parameters a) n b s
  | SHA2_256 -> Spec.SHA2.update_multi (parameters a) n b s
  | SHA2_384 -> Spec.SHA2.update_multi (parameters a) n b s
  | SHA2_512 -> Spec.SHA2.update_multi (parameters a) n b s

let update_last a l b s = match a with
  | SHA2_224 -> Spec.SHA2.update_last (parameters a) l b s
  | SHA2_256 -> Spec.SHA2.update_last (parameters a) l b s
  | SHA2_384 -> Spec.SHA2.update_last (parameters a) l b s
  | SHA2_512 -> Spec.SHA2.update_last (parameters a) l b s

let finish a s = match a with
  | SHA2_224 -> Spec.SHA2.finish (parameters a) s
  | SHA2_256 -> Spec.SHA2.finish (parameters a) s
  | SHA2_384 -> Spec.SHA2.finish (parameters a) s
  | SHA2_512 -> Spec.SHA2.finish (parameters a) s

let update' a l b s = match a with
  | SHA2_224 -> Spec.SHA2.update' (parameters a) l b s
  | SHA2_256 -> Spec.SHA2.update' (parameters a) l b s
  | SHA2_384 -> Spec.SHA2.update' (parameters a) l b s
  | SHA2_512 -> Spec.SHA2.update' (parameters a) l b s

let finish' a s = match a with
  | SHA2_224 -> Spec.SHA2.finish (parameters a) s
  | SHA2_256 -> Spec.SHA2.finish (parameters a) s
  | SHA2_384 -> Spec.SHA2.finish (parameters a) s
  | SHA2_512 -> Spec.SHA2.finish (parameters a) s

let hash a s = match a with
  | SHA2_224 -> Spec.SHA2.hash' (parameters a) s
  | SHA2_256 -> Spec.SHA2.hash' (parameters a) s
  | SHA2_384 -> Spec.SHA2.hash' (parameters a) s
  | SHA2_512 -> Spec.SHA2.hash' (parameters a) s
