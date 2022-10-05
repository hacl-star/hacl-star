module Hacl.Blake2b_256

module Spec = Spec.Blake2
module Impl = Hacl.Impl.Blake2.Generic
module Core = Hacl.Impl.Blake2.Core

(* Some specialized components of blake2 *)
[@CInline]
private
let blake2b_update_block : Impl.blake2_update_block_st Spec.Blake2B Core.M256 =
  Impl.blake2_update_block #Spec.Blake2B #Core.M256

let blake2b_init : Impl.blake2_init_st Spec.Blake2B Core.M256 =
  Impl.blake2_init #Spec.Blake2B #Core.M256

let blake2b_update_key : Impl.blake2_update_key_st Spec.Blake2B Core.M256 =
  Impl.blake2_update_key #Spec.Blake2B #Core.M256 blake2b_update_block

let blake2b_update_multi : Impl.blake2_update_multi_st Spec.Blake2B Core.M256 =
  Impl.blake2_update_multi #Spec.Blake2B #Core.M256 blake2b_update_block

let blake2b_update_last : Impl.blake2_update_last_st Spec.Blake2B Core.M256 =
  Impl.blake2_update_last #Spec.Blake2B #Core.M256 blake2b_update_block

[@CInline]
private
let blake2b_update_blocks : Impl.blake2_update_blocks_st Spec.Blake2B Core.M256 =
  Impl.blake2_update_blocks #Spec.Blake2B #Core.M256 blake2b_update_multi blake2b_update_last

[@CInline]
private
let blake2b_update : Impl.blake2_update_st Spec.Blake2B Core.M256 =
  Impl.blake2_update #Spec.Blake2B #Core.M256 blake2b_update_key blake2b_update_blocks

let blake2b_finish : Impl.blake2_finish_st Spec.Blake2B Core.M256 =
  Impl.blake2_finish #Spec.Blake2B #Core.M256

(* The one-shot hash *)
let blake2b : Impl.blake2_st Spec.Blake2B Core.M256 =
  Impl.blake2 #Spec.Blake2B #Core.M256 blake2b_init blake2b_update blake2b_finish

let load_state256b_from_state32: Core.load_state_st Spec.Blake2B Core.M256 =
  Core.load_state_from_state32 #Spec.Blake2B #Core.M256
let store_state256b_to_state32: Core.store_state_st Spec.Blake2B Core.M256 =
  Core.store_state_to_state32 #Spec.Blake2B #Core.M256
