module Hacl.Hash.Core.SHA2.Constants

module HS = FStar.HyperStack
module IB = LowStar.ImmutableBuffer

module Constants = Spec.SHA2.Constants

#set-options "--max_fuel 0 --max_ifuel 0"

(** Constants exposed for the sake of Vale. *)

let k224_256 = IB.igcmalloc_of_list HS.root Constants.k224_256_l
let k384_512 = IB.igcmalloc_of_list HS.root Constants.k384_512_l

