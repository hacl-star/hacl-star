module Hacl.Blake2b_32

module Spec = Spec.Blake2
module Impl = Hacl.Impl.Blake2.Generic
module Core = Hacl.Impl.Blake2.Core

(* Some specialized components of blake2 *)
[@CInline]
private
let blake2b_update_block : Impl.blake2_update_block_st Spec.Blake2B Core.M32 =
  Impl.blake2_update_block #Spec.Blake2B #Core.M32

let blake2b_init : Impl.blake2_init_st Spec.Blake2B Core.M32 =
  Impl.blake2_init #Spec.Blake2B #Core.M32

[@CInline]
let blake2b_update_key : Impl.blake2_update_key_st Spec.Blake2B Core.M32 =
  Impl.blake2_update_key #Spec.Blake2B #Core.M32 blake2b_update_block

let blake2b_update_multi : Impl.blake2_update_multi_st Spec.Blake2B Core.M32 =
  Impl.blake2_update_multi #Spec.Blake2B #Core.M32 blake2b_update_block

let blake2b_update_last : Impl.blake2_update_last_st Spec.Blake2B Core.M32 =
  Impl.blake2_update_last #Spec.Blake2B #Core.M32 blake2b_update_block

[@CInline]
private
let blake2b_update_blocks : Impl.blake2_update_blocks_st Spec.Blake2B Core.M32 =
  Impl.blake2_update_blocks #Spec.Blake2B #Core.M32 blake2b_update_multi blake2b_update_last

[@CInline]
private
let blake2b_update : Impl.blake2_update_st Spec.Blake2B Core.M32 =
  Impl.blake2_update #Spec.Blake2B #Core.M32 blake2b_update_key blake2b_update_blocks

let blake2b_finish : Impl.blake2_finish_st Spec.Blake2B Core.M32 =
  Impl.blake2_finish #Spec.Blake2B #Core.M32

(* The one-shot hash *)
let blake2b : Impl.blake2_st Spec.Blake2B Core.M32 =
  Impl.blake2 #Spec.Blake2B #Core.M32 blake2b_init blake2b_update blake2b_finish
