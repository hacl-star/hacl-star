module Hacl.Hash.Blake2

module HS = FStar.HyperStack
module ST = FStar.HyperStack.ST

module M = LowStar.Modifies
module B = LowStar.Buffer
module Spec = Spec.Hash.PadFinish
module Impl = Hacl.Impl.Blake2.Generic
module Blake2 = Hacl.Impl.Blake2.Core

open Lib.IntTypes
open Spec.Hash.Definitions
open FStar.Mul

open Spec.Hash.Definitions
open Hacl.Hash.Definitions

include Hacl.Hash.Core.Blake2

// NO VECTORIZED VARIANTS HERE!

noextract inline_for_extraction
val mk_update_multi:
     a:hash_alg{is_blake a}
  -> m:m_spec a{Impl.is_valid_blake2_config (to_blake_alg a) m}
  -> update:update_st (|a, m|) ->
  update_multi_st (|a, m|)

val update_multi_blake2s_32: update_multi_st (|Blake2S, Blake2.M32|)
val update_multi_blake2b_32: update_multi_st (|Blake2B, Blake2.M32|)

noextract inline_for_extraction
val mk_update_last:
     a:hash_alg{is_blake a}
  -> m:m_spec a{Impl.is_valid_blake2_config (to_blake_alg a) m}
  -> update_multi:update_multi_st (|a, m|) ->
  update_last_st (|a, m|)

val update_last_blake2s_32: update_last_st (|Blake2S, Blake2.M32|)
val update_last_blake2b_32: update_last_st (|Blake2B, Blake2.M32|)

noextract inline_for_extraction
val mk_hash:
  a:hash_alg{is_blake a}
  -> m:m_spec a{Impl.is_valid_blake2_config (to_blake_alg a) m}
  -> blake2:Impl.blake2_st (to_blake_alg a) m ->
  hash_st a

val hash_blake2s_32: hash_st Blake2S
val hash_blake2b_32: hash_st Blake2B
