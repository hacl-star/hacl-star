module Hacl.Hash.Core.Blake2

open Hacl.Hash.Definitions
open Spec.Hash.Definitions
module Core = Hacl.Impl.Blake2.Core

noextract inline_for_extraction
val mk_init (a:hash_alg{is_blake a}) (m:m_spec a) : init_st (|a, m|)
val mk_alloca (a:hash_alg{is_blake a}) (m:m_spec a) : init_st (|a, m|) -> alloca_st (|a, m|)
val mk_update (a:hash_alg{is_blake a}) (m:m_spec a) : update_st (|a, m|)
val mk_finish (a:hash_alg{is_blake a}) (m:m_spec a) : finish_st (|a, m|)

noextract inline_for_extraction
val init_blake2s_32: init_st (|Blake2S, Core.M32|)
val alloca_blake2s_32: alloca_st (|Blake2S, Core.M32|)
val update_blake2s_32: update_st (|Blake2S, Core.M32|)
val finish_blake2s_32: finish_st (|Blake2S, Core.M32|)

noextract inline_for_extraction
val init_blake2s_128: init_st (|Blake2S, Core.M128|)
val alloca_blake2s_128: alloca_st (|Blake2S, Core.M128|)
val update_blake2s_128: update_st (|Blake2S, Core.M128|)
val finish_blake2s_128: finish_st (|Blake2S, Core.M128|)

noextract inline_for_extraction
val pad_blake2s: pad_st Blake2S

noextract inline_for_extraction
val init_blake2b_32: init_st (|Blake2B, Core.M32|)
val alloca_blake2b_32: alloca_st (|Blake2B, Core.M32|)
val update_blake2b_32: update_st (|Blake2B, Core.M32|)
val finish_blake2b_32: finish_st (|Blake2B, Core.M32|)

noextract inline_for_extraction
val init_blake2b_256: init_st (|Blake2B, Core.M256|)
val alloca_blake2b_256: alloca_st (|Blake2B, Core.M256|)
val update_blake2b_256: update_st (|Blake2B, Core.M256|)
val finish_blake2b_256: finish_st (|Blake2B, Core.M256|)

noextract inline_for_extraction
val pad_blake2b: pad_st Blake2B
