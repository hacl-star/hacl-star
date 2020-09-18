module Hacl.Impl.Blake2.FGeneric

open FStar.Mul
open FStar.HyperStack
open FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer
open Lib.ByteBuffer
open Lib.LoopCombinators

module ST = FStar.HyperStack.ST
module Seq = Lib.Sequence
module Loops = Lib.LoopCombinators
module Spec = Spec.Blake2

open Hacl.Impl.Blake2.Constants
open Hacl.Impl.Blake2.Core
open Hacl.Impl.Blake2.Generic
module Blake2s32 = Hacl.Blake2s_32
module Blake2s128 = Hacl.Blake2s_128
module Blake2b32 = Hacl.Blake2b_32
module Blake2b256 = Hacl.Blake2b_256

#set-options "--z3rlimit 50 --max_ifuel 0 --max_fuel 0"

/// FGeneric: factorized generic.
/// The generic implementation of Blake2, but relying on intermediate definitions.
/// Allows to factorize code between the one-shot hash and the generic hash.

noextract
let is_valid_m_spec (al : Spec.alg) (ms : m_spec) =
  match al, ms with
  | Spec.Blake2S, M32
  | Spec.Blake2S, M128
  | Spec.Blake2B, M32
  | Spec.Blake2B, M256 -> true
  | _ -> false

inline_for_extraction noextract
let valid_m_spec (al : Spec.alg) = ms:m_spec{is_valid_m_spec al ms}

inline_for_extraction noextract
let blake2_init (#al : Spec.alg) (#ms : valid_m_spec al) : blake2_init_st al ms =
  match al, ms with
  | Spec.Blake2S, M32 -> Blake2s32.blake2s_init
  | Spec.Blake2S, M128 -> Blake2s128.blake2s_init
  | Spec.Blake2B, M32 -> Blake2b32.blake2b_init
  | Spec.Blake2B, M256 -> Blake2b256.blake2b_init

inline_for_extraction noextract
let blake2_update_multi (#al : Spec.alg) (#ms : valid_m_spec al) :
  blake2_update_multi_st al ms =
  match al, ms with
  | Spec.Blake2S, M32 -> Blake2s32.blake2s_update_multi
  | Spec.Blake2S, M128 -> Blake2s128.blake2s_update_multi
  | Spec.Blake2B, M32 -> Blake2b32.blake2b_update_multi
  | Spec.Blake2B, M256 -> Blake2b256.blake2b_update_multi

inline_for_extraction noextract
let blake2_update_last (#al : Spec.alg) (#ms : valid_m_spec al) :
  blake2_update_last_st al ms =
  match al, ms with
  | Spec.Blake2S, M32 -> Blake2s32.blake2s_update_last
  | Spec.Blake2S, M128 -> Blake2s128.blake2s_update_last
  | Spec.Blake2B, M32 -> Blake2b32.blake2b_update_last
  | Spec.Blake2B, M256 -> Blake2b256.blake2b_update_last

inline_for_extraction noextract
let blake2_finish (#al : Spec.alg) (#ms : valid_m_spec al) :
  blake2_finish_st al ms =
  match al, ms with
  | Spec.Blake2S, M32 -> Blake2s32.blake2s_finish
  | Spec.Blake2S, M128 -> Blake2s128.blake2s_finish
  | Spec.Blake2B, M32 -> Blake2b32.blake2b_finish
  | Spec.Blake2B, M256 -> Blake2b256.blake2b_finish



