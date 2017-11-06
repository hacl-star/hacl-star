module Spec.SHA2_512

#reset-options "--max_fuel 0 --z3rlimit 25"

let parameters = Spec.SHA2.parameters_sha2_512

let hash_w = Spec.SHA2.hash_w parameters
let size_hash = 64
let size_block = 128
let maxInput = pow2 32 - 1

let update_block b h = Spec.SHA2.update_block parameters b h
let update_multi n b h = Spec.SHA2.update_multi parameters n b h
let update_last n l b h = Spec.SHA2.update_last parameters n l b h
let finish h = Spec.SHA2.finish parameters h
let hash s = Spec.SHA2.hash' parameters s
