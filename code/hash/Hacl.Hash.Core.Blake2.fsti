module Hacl.Hash.Core.Blake2

open Hacl.Hash.Definitions
open Spec.Hash.Definitions

noextract inline_for_extraction
val mk_init (a:hash_alg{is_blake a}) : init_st a
val mk_alloca (a:hash_alg{is_blake a}) : init_st a -> alloca_st a
val mk_update (a:hash_alg{is_blake a}) : update_st a

noextract inline_for_extraction
val init_blake2s: init_st Blake2S
val alloca_blake2s: alloca_st Blake2S
val update_blake2s: update_st Blake2S
val pad_blake2s: pad_st Blake2S
val finish_blake2s: finish_st Blake2S

noextract inline_for_extraction
val init_blake2b: init_st Blake2B
val alloca_blake2b: alloca_st Blake2B
val update_blake2b: update_st Blake2B
val pad_blake2b: pad_st Blake2B
val finish_blake2b: finish_st Blake2B
