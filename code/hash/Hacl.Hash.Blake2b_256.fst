module Hacl.Hash.Blake2b_256

open Hacl.Impl.Blake2.Core
open Spec.Hash.Definitions
open Hacl.Hash.Definitions
open Hacl.Hash.Blake2

let update_multi_blake2b_256: update_multi_st (|Blake2B, M256|) =
  mk_update_multi Blake2B M256 update_blake2b_256

let update_last_blake2b_256: update_last_st (|Blake2B, M256|) =
  mk_update_last Blake2B M256 update_multi_blake2b_256

let hash_blake2b_256: hash_st Blake2B =
  mk_hash Blake2B M256 Hacl.Blake2b_256.blake2b
