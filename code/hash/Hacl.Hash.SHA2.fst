module Hacl.Hash.SHA2

open Hacl.Hash.Definitions
open Spec.Hash.Definitions

include Hacl.Hash.Core.SHA2

friend Hacl.Hash.MD

let update_multi_224: update_multi_st SHA2_224 =
  Hacl.Hash.MD.mk_update_multi SHA2_224 update_224
let update_multi_256: update_multi_st SHA2_256 =
  Hacl.Hash.MD.mk_update_multi SHA2_256 update_256
let update_multi_384: update_multi_st SHA2_384 =
  Hacl.Hash.MD.mk_update_multi SHA2_384 update_384
let update_multi_512: update_multi_st SHA2_512 =
  Hacl.Hash.MD.mk_update_multi SHA2_512 update_512

let update_last_224: update_last_st SHA2_224 =
  Hacl.Hash.MD.mk_update_last SHA2_224 update_multi_224 pad_224
let update_last_256: update_last_st SHA2_256 =
  Hacl.Hash.MD.mk_update_last SHA2_256 update_multi_256 pad_256
let update_last_384: update_last_st SHA2_384 =
  Hacl.Hash.MD.mk_update_last SHA2_384 update_multi_384 pad_384
let update_last_512: update_last_st SHA2_512 =
  Hacl.Hash.MD.mk_update_last SHA2_512 update_multi_512 pad_512

let hash_224: hash_st SHA2_224 =
  Hacl.Hash.MD.mk_hash SHA2_224 alloca_224 update_multi_224 update_last_224 finish_224
let hash_256: hash_st SHA2_256 =
  Hacl.Hash.MD.mk_hash SHA2_256 alloca_256 update_multi_256 update_last_256 finish_256
let hash_384: hash_st SHA2_384 =
  Hacl.Hash.MD.mk_hash SHA2_384 alloca_384 update_multi_384 update_last_384 finish_384
let hash_512: hash_st SHA2_512 =
  Hacl.Hash.MD.mk_hash SHA2_512 alloca_512 update_multi_512 update_last_512 finish_512

// Friend-ing for compatibility with HACL* libs until we unify the secret integers

friend Lib.IntTypes

noextract inline_for_extraction
let hash_512_lib input_len input dst =
  hash_512 input input_len dst
