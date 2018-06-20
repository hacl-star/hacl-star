module EverCrypt.Hash

open EverCrypt.Helpers
open FStar.HyperStack.ST

module HS = FStar.HyperStack
module B = LowStar.Buffer
module M = LowStar.Modifies

open LowStar.BufferOps
open FStar.Integers

let uint32_p = B.buffer uint_32
let uint64_p = B.buffer uint_64

noeq
type state_s =
| SHA256_Hacl: uint32_p -> state_s
| SHA256_Vale: uint32_p -> state_s
| SHA384_Hacl: uint64_p -> state_s

 
