module Hacl.Hash.Blake2b_256

open Hacl.Impl.Blake2.Core
open Spec.Hash.Definitions
open Hacl.Hash.Definitions
open Hacl.Hash.Blake2

let init_blake2b_256: init_st (|Blake2B, M256|) =
  mk_init Blake2B M256

noextract inline_for_extraction
let alloca_blake2b_256: alloca_st (|Blake2B, M256|) =
  mk_alloca Blake2B M256 (mk_init Blake2B M256)

let update_blake2b_256: update_st (|Blake2B, M256|) =
  mk_update Blake2B M256

let finish_blake2b_256: finish_st (|Blake2B, M256|) =
  mk_finish Blake2B M256

let update_multi_blake2b_256: update_multi_st (|Blake2B, M256|) =
  mk_update_multi Blake2B M256 update_blake2b_256

let update_last_blake2b_256: update_last_st (|Blake2B, M256|) =
  mk_update_last Blake2B M256 update_multi_blake2b_256

let hash_blake2b_256: hash_st Blake2B =
  mk_hash Blake2B M256 Hacl.Blake2b_256.blake2b

let malloc_blake2b_256: malloc_st (|Blake2B, M256|) =
  mk_malloc Blake2B M256
