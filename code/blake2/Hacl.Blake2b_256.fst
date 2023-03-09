module Hacl.Blake2b_256

module Spec = Spec.Blake2
module Impl = Hacl.Impl.Blake2.Generic
module Core = Hacl.Impl.Blake2.Core

(* Some specialized components of blake2 *)
[@CInline]
private
let update_block : Impl.blake2_update_block_st Spec.Blake2B Core.M256 =
  Impl.blake2_update_block #Spec.Blake2B #Core.M256

let init : Impl.blake2_init_st Spec.Blake2B Core.M256 =
  Impl.blake2_init #Spec.Blake2B #Core.M256

let update_key : Impl.blake2_update_key_st Spec.Blake2B Core.M256 =
  Impl.blake2_update_key #Spec.Blake2B #Core.M256 update_block

let update_multi : Impl.blake2_update_multi_st Spec.Blake2B Core.M256 =
  Impl.blake2_update_multi #Spec.Blake2B #Core.M256 update_block

let update_last : Impl.blake2_update_last_st Spec.Blake2B Core.M256 =
  Impl.blake2_update_last #Spec.Blake2B #Core.M256 update_block

[@CInline]
private
let update_blocks : Impl.blake2_update_blocks_st Spec.Blake2B Core.M256 =
  Impl.blake2_update_blocks #Spec.Blake2B #Core.M256 update_multi update_last

[@CInline]
private
let update : Impl.blake2_update_st Spec.Blake2B Core.M256 =
  Impl.blake2_update #Spec.Blake2B #Core.M256 update_key update_blocks

let finish : Impl.blake2_finish_st Spec.Blake2B Core.M256 =
  Impl.blake2_finish #Spec.Blake2B #Core.M256

(* The one-shot hash *)
[@@ Comment "Write the BLAKE2b digest of message `input` using key `key` into `output`.

@param output Pointer to `output_len` bytes of memory where the digest is written to.
@param output_len Length of the to-be-generated digest with 1 <= `output_len` <= 64.
@param input Pointer to `input_len` bytes of memory where the input message is read from.
@param input_len Length of the input message.
@param key Pointer to `key_len` bytes of memory where the key is read from.
@param key_len Length of the key. Can be 0."]
let hash_with_key : Impl.blake2_st Spec.Blake2B Core.M256 =
  Impl.blake2 #Spec.Blake2B #Core.M256 init update finish

let load_state256b_from_state32: Core.load_state_st Spec.Blake2B Core.M256 =
  Core.load_state_from_state32 #Spec.Blake2B #Core.M256
let store_state256b_to_state32: Core.store_state_st Spec.Blake2B Core.M256 =
  Core.store_state_to_state32 #Spec.Blake2B #Core.M256

let malloc_with_key : Impl.blake2_malloc_st Spec.Blake2B Core.M256 =
  Impl.blake2_malloc Spec.Blake2B Core.M256
