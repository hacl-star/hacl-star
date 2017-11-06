module Spec.SHA2_512

open FStar.Mul
open Spec.Types
open Spec.Lib.IntTypes

#reset-options "--max_fuel 0 --z3rlimit 25"

val hash_w: Type0
val size_hash: size_t
val size_block: size_t
val maxInput: size_t

val update_block: block:lbytes size_block -> hash:hash_w -> Tot hash_w
val update_multi: n:size_t{n * size_block <= max_size_t} -> blocks:lbytes (n * size_block) -> hash:hash_w -> Tot hash_w
val update_last: n:size_t -> len:size_t{len < size_block /\ len + n * size_block <= maxInput} -> last:lbytes len -> hash:hash_w -> Tot hash_w
val finish: hash:hash_w -> Tot (lbytes size_hash)
val hash: len:size_t{len < maxInput} -> input:lbytes len -> Tot (lbytes size_hash)
