module Hacl.Blake2b_32

module Spec = Spec.Blake2
module Impl = Hacl.Impl.Blake2.Generic
module Core = Hacl.Impl.Blake2.Core

(* Some specialized components of blake2 *)
private
let update_block : Impl.blake2_update_block_st Spec.Blake2B Core.M32 =
  Impl.blake2_update_block #Spec.Blake2B #Core.M32

let init : Impl.blake2_init_st Spec.Blake2B Core.M32 =
  Impl.blake2_init #Spec.Blake2B #Core.M32

let update_key : Impl.blake2_update_key_st Spec.Blake2B Core.M32 =
  Impl.blake2_update_key #Spec.Blake2B #Core.M32 update_block

let update_multi : Impl.blake2_update_multi_st Spec.Blake2B Core.M32 =
  Impl.blake2_update_multi #Spec.Blake2B #Core.M32 update_block

let update_last : Impl.blake2_update_last_st Spec.Blake2B Core.M32 =
  Impl.blake2_update_last #Spec.Blake2B #Core.M32 update_block

private
let update_blocks : Impl.blake2_update_blocks_st Spec.Blake2B Core.M32 =
  Impl.blake2_update_blocks #Spec.Blake2B #Core.M32 update_multi update_last

[@CInline]
private
let update : Impl.blake2_update_st Spec.Blake2B Core.M32 =
  Impl.blake2_update #Spec.Blake2B #Core.M32 update_key update_blocks

let finish : Impl.blake2_finish_st Spec.Blake2B Core.M32 =
  Impl.blake2_finish #Spec.Blake2B #Core.M32

(* The one-shot hash *)

[@@ Comment "Write the BLAKE2b digest of message `input` using key `key` into `output`.

@param output Pointer to `output_len` bytes of memory where the digest is written to.
@param output_len Length of the to-be-generated digest with 1 <= `output_len` <= 64.
@param input Pointer to `input_len` bytes of memory where the input message is read from.
@param input_len Length of the input message.
@param key Pointer to `key_len` bytes of memory where the key is read from.
@param key_len Length of the key. Can be 0."]
let hash_with_key : Impl.blake2_st Spec.Blake2B Core.M32 =
  Impl.blake2 #Spec.Blake2B #Core.M32 init update finish

let malloc_with_key : Impl.blake2_malloc_st Spec.Blake2B Core.M32 =
  Impl.blake2_malloc Spec.Blake2B Core.M32
