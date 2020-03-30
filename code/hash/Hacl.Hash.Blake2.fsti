module Hacl.Hash.Blake2

open Spec.Hash.Definitions
open Hacl.Hash.Definitions

include Hacl.Hash.Core.Blake2

val update_multi_blake2s: update_multi_st Blake2S
val update_multi_blake2b: update_multi_st Blake2B

val update_last_blake2s: update_last_st Blake2S
val update_last_blake2b: update_last_st Blake2B

val hash_blake2s: hash_st Blake2S
val hash_blake2b: hash_st Blake2B
