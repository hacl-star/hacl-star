module Hacl.Streaming.MD5

/// WARNING: this file is here for legacy purposes only. You SHOULD NOT use
/// it in new code.

open FStar.HyperStack.ST

/// A streaming version of MD-based hashes

#set-options "--max_fuel 0 --max_ifuel 0 --z3rlimit 100"

module G = FStar.Ghost
module F = Hacl.Streaming.Functor

open Spec.Hash.Definitions
open Hacl.Streaming.Block
open Hacl.Streaming.MD

/// Instantiations of the streaming functor for MD5
///
/// Some remarks:
///
/// - we don't bother with using the abstraction feature since we verified
///   clients like miTLS go through EverCrypt.Hash.Incremental

inline_for_extraction noextract
let hacl_md5 = hacl_md_index MD5

inline_for_extraction noextract
let state_t_md5 = state_t MD5

/// Type abbreviation - for pretty code generation
let state = Hacl.Streaming.MD.state_32

noextract
let legacy_alloca : F.alloca_st hacl_md5 =
  F.mk_alloca #hacl_md5
    (hacl_md_init MD5)
    (Stateful.copy_unused #(word MD5))
    (Stateful.alloca_unused #(word MD5))
    (Stateful.alloca_buffer #(word MD5) #(state_len MD5) #(init_elem MD5))

let legacy_create_in : F.create_in_st hacl_md5 =
  F.mk_create_in #hacl_md5
    (hacl_md_init MD5)
    (Stateful.copy_unused #(word MD5))
    (Stateful.create_in_unused #(word MD5))
    (Stateful.create_in_buffer #(word MD5) #(state_len MD5) #(init_elem MD5))

let legacy_init : F.init_st hacl_md5 =
  F.mk_init #hacl_md5
    (Stateful.copy_unused #(word MD5))
    (hacl_md_init MD5)

[@@ Comment "0 = success, 1 = max length exceeded" ]
let legacy_update : F.update_st hacl_md5 =
  F.mk_update #hacl_md5 (hacl_md_update_multi MD5)

let legacy_finish : F.finish_st hacl_md5 =
  F.mk_finish #hacl_md5
    (hacl_md_finish MD5)
    (hacl_md_update_last MD5)
    (hacl_md_update_multi MD5)
    (Stateful.copy_buffer #(word MD5) #(state_len MD5))
    (Stateful.alloca_buffer #(word MD5) #(state_len MD5) #(init_elem MD5))

let legacy_free : F.free_st hacl_md5 =
  F.mk_free #hacl_md5
    (Stateful.free_buffer #(word MD5) #(state_len MD5))
    (Stateful.free_unused #(word MD5))

let legacy_copy : F.copy_st hacl_md5 =
  F.mk_copy #hacl_md5
    (Stateful.copy_unused #(word MD5))
    (Stateful.create_in_unused #(word MD5))
    (Stateful.copy_buffer #(word MD5) #(state_len MD5))
    (Stateful.create_in_buffer #(word MD5) #(state_len MD5) #(init_elem MD5))

let legacy_hash: Hacl.Hash.Definitions.hash_st MD5 =
  fun input input_len dst -> Hacl.Hash.MD5.legacy_hash input input_len dst
