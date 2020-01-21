module Hacl.Blake2b_256

module Spec = Spec.Blake2_Vec
module Impl = Hacl.Impl.Blake2.Generic
module Core = Hacl.Impl.Blake2.Core

[@CInline]
private
let blake2b_update_block = Impl.blake2_update_block #Spec.Blake2B #Core.M256

let blake2b = Impl.blake2 #Spec.Blake2B #Core.M256 blake2b_update_block
