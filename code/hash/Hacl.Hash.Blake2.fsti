module Hacl.Hash.Blake2

module HS = FStar.HyperStack
module ST = FStar.HyperStack.ST

module M = LowStar.Modifies
module B = LowStar.Buffer
module Spec = Spec.Hash.PadFinish
module Blake2 = Hacl.Impl.Blake2.Core

open Lib.IntTypes
open Spec.Hash.Definitions
open FStar.Mul

open Spec.Hash.Definitions
open Hacl.Hash.Definitions

include Hacl.Hash.Core.Blake2

val update_multi_blake2s_32: update_multi_st Blake2S Blake2.M32
val update_multi_blake2s_128: update_multi_st Blake2S Blake2.M128
val update_multi_blake2b_32: update_multi_st Blake2B Blake2.M32
val update_multi_blake2b_256: update_multi_st Blake2B Blake2.M256

val update_last_blake2s_32: update_last_st Blake2S Blake2.M32
val update_last_blake2s_128: update_last_st Blake2S Blake2.M128
val update_last_blake2b_32: update_last_st Blake2B Blake2.M32
val update_last_blake2b_256: update_last_st Blake2B Blake2.M256

val hash_blake2s_32: hash_st Blake2S
val hash_blake2s_128: hash_st Blake2S
val hash_blake2b_32: hash_st Blake2B
val hash_blake2b_256: hash_st Blake2B
