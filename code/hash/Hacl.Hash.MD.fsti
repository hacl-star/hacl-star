module Hacl.Hash.MD

open Hacl.Hash.Definitions
open Spec.Hash.Definitions

module U32 = FStar.UInt32

let legacy_alg = a:hash_alg { a == MD5 \/ a == SHA1 }

noextract inline_for_extraction
val len_add32 (a: hash_alg{not (is_keccak a)})
  (prev_len: len_t a)
  (input_len: U32.t { (U32.v input_len + len_v a prev_len) `less_than_max_input_length` a }):
  x:len_t a { len_v a x = len_v a prev_len + U32.v input_len }

noextract inline_for_extraction
val mk_update_multi: a:legacy_alg -> update:update_st (|a, ()|) -> update_multi_st (|a, ()|)

noextract inline_for_extraction
val mk_update_last: a:legacy_alg -> update_multi_st (|a, ()|) -> pad_st a -> update_last_st (|a, ()|)

noextract inline_for_extraction
val mk_hash: a:md_alg ->
  alloca:alloca_st (|a, ()|) ->
  update_multi:update_multi_st (|a, ()|) ->
  update_last:update_last_st (|a, ()|) ->
  finish:finish_st (|a, ()|) ->
  hash_st a
