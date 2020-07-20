module Hacl.Hash.Blake2s_128

open Hacl.Impl.Blake2.Core
open Spec.Hash.Definitions
open Hacl.Hash.Definitions
open Hacl.Hash.Blake2

let update_multi_blake2s_128: update_multi_st (|Blake2S, M128|) =
  mk_update_multi Blake2S M128 update_blake2s_128

let update_last_blake2s_128: update_last_st (|Blake2S, M128|) =
  mk_update_last Blake2S M128 update_multi_blake2s_128

let hash_blake2s_128: hash_st Blake2S =
  mk_hash Blake2S M128 Hacl.Blake2s_128.blake2s
