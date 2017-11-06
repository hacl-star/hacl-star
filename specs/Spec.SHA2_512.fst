module Spec.SHA2_512

#reset-options "--max_fuel 0 --z3rlimit 25"

let algorithm = Spec.Hashing.SHA2_512

let hash_w = Spec.Hashing.hash_w algorithm
let size_hash = Spec.Hashing.size_hash algorithm
let size_block = Spec.Hashing.size_block algorithm
let maxInput = Spec.Hashing.maxInput algorithm

let update_block b h = Spec.Hashing.update_block algorithm b h
let update_multi n b h = Spec.Hashing.update_multi algorithm n b h
let update_last n l b h = Spec.Hashing.update_last algorithm n l b h
let finish h = Spec.Hashing.finish algorithm h
let hash s = Spec.Hashing.hash algorithm s
