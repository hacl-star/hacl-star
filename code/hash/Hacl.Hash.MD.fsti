module Hacl.Hash.MD

open Hacl.Hash.Definitions
open Spec.Hash.Definitions

noextract inline_for_extraction
val mk_update_multi: a:hash_alg -> update:update_st a -> update_multi_st a

noextract inline_for_extraction
val mk_update_last: a:hash_alg -> update_multi_st a -> pad_st a -> update_last_st a

noextract inline_for_extraction
val mk_hash: a:hash_alg ->
  alloca:alloca_st a ->
  update_multi:update_multi_st a ->
  update_last:update_last_st a ->
  finish:finish_st a ->
  hash_st a
