module Hacl.Hash.Core.Blake2

open Hacl.Hash.Definitions
open Spec.Hash.Definitions

noextract inline_for_extraction
val alloca_blake2s: alloca_st Blake2S
val init_blake2s: init_st Blake2S
val update_blake2s: update_st Blake2S

noextract inline_for_extraction
val alloca_blake2b: alloca_st Blake2B
val init_blake2b: init_st Blake2B
val update_blake2b: update_st Blake2B
