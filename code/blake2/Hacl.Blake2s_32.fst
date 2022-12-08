module Hacl.Blake2s_32

module Spec = Spec.Blake2
module Impl = Hacl.Impl.Blake2.Generic
module Core = Hacl.Impl.Blake2.Core

(* Some specialized components of blake2 *)
[@CInline]
private
let blake2s_update_block : Impl.blake2_update_block_st Spec.Blake2S Core.M32 =
  Impl.blake2_update_block #Spec.Blake2S #Core.M32

let blake2s_init : Impl.blake2_init_st Spec.Blake2S Core.M32 =
  Impl.blake2_init #Spec.Blake2S #Core.M32

let blake2s_update_key : Impl.blake2_update_key_st Spec.Blake2S Core.M32 =
  Impl.blake2_update_key #Spec.Blake2S #Core.M32 blake2s_update_block

let blake2s_update_multi : Impl.blake2_update_multi_st Spec.Blake2S Core.M32 =
  Impl.blake2_update_multi #Spec.Blake2S #Core.M32 blake2s_update_block

let blake2s_update_last : Impl.blake2_update_last_st Spec.Blake2S Core.M32 =
  Impl.blake2_update_last #Spec.Blake2S #Core.M32 blake2s_update_block

private
let blake2s_update_blocks : Impl.blake2_update_blocks_st Spec.Blake2S Core.M32 =
  Impl.blake2_update_blocks #Spec.Blake2S #Core.M32 blake2s_update_multi blake2s_update_last

[@CInline]
private
let blake2s_update : Impl.blake2_update_st Spec.Blake2S Core.M32 =
  Impl.blake2_update #Spec.Blake2S #Core.M32 blake2s_update_key blake2s_update_blocks

let blake2s_finish : Impl.blake2_finish_st Spec.Blake2S Core.M32 =
  Impl.blake2_finish #Spec.Blake2S #Core.M32

(* The one-shot hash *)
[@@ Comment "Write the BLAKE2s digest of message `d` using key `k` into `output`.

@param nn Length of to-be-generated digest with 1 <= `nn` <= 32.
@param output Pointer to `nn` bytes of memory where the digest is written to.
@param ll Length of the input message.
@param d Pointer to `ll` bytes of memory where the input message is read from.
@param kk Length of the key. Can be 0.
@param k Pointer to `kk` bytes of memory where the key is read from."]
let blake2s : Impl.blake2_st Spec.Blake2S Core.M32 =
  Impl.blake2 #Spec.Blake2S #Core.M32 blake2s_init blake2s_update blake2s_finish

let blake2s_malloc : Impl.blake2_malloc_st Spec.Blake2S Core.M32 =
  Impl.blake2_malloc Spec.Blake2S Core.M32
