module Hacl.Hash.SHA2

open Hacl.Hash.Definitions
open Spec.Hash.Definitions

include Hacl.Hash.Core.SHA2

friend Hacl.Hash.MD

let update_multi_224 =
  Hacl.Hash.MD.mk_update_multi SHA2_224 update_224
let update_multi_256 =
  Hacl.Hash.MD.mk_update_multi SHA2_256 update_256
let update_multi_384 =
  Hacl.Hash.MD.mk_update_multi SHA2_384 update_384
let update_multi_512 =
  Hacl.Hash.MD.mk_update_multi SHA2_512 update_512

let update_last_224 =
  Hacl.Hash.MD.mk_update_last SHA2_224 update_multi_224 pad_224
let update_last_256 =
  Hacl.Hash.MD.mk_update_last SHA2_256 update_multi_256 pad_256
let update_last_384 =
  Hacl.Hash.MD.mk_update_last SHA2_384 update_multi_384 pad_384
let update_last_512 =
  Hacl.Hash.MD.mk_update_last SHA2_512 update_multi_512 pad_512

let hash_224 input input_len dst =
  Hacl.Streaming.SHA2.sha224 input input_len dst
let hash_256 input input_len dst =
  Hacl.Streaming.SHA2.sha256 input input_len dst
let hash_384 input input_len dst =
  Hacl.Streaming.SHA2.sha384 input input_len dst
let hash_512 input input_len dst =
  Hacl.Streaming.SHA2.sha512 input input_len dst
