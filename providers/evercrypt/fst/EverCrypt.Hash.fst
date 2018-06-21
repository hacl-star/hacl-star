module EverCrypt.Hash

open EverCrypt.Helpers
open FStar.HyperStack.ST

module HS = FStar.HyperStack
module B = LowStar.Buffer
module M = LowStar.Modifies
module G = FStar.Ghost

open LowStar.BufferOps
open FStar.Integers

#reset-options "--using_facts_from '* -Hacl -Spec'"

let uint32_p = B.buffer uint_32
let uint64_p = B.buffer uint_64

noeq
type state_s: (G.erased alg) -> Type0 =
| SHA256_Hacl: p:uint32_p{ B.length p = 8 } -> state_s (G.hide SHA256)
| SHA256_Vale: p:uint32_p{ B.length p = 8 } -> state_s (G.hide SHA256)
| SHA384_Hacl: p:uint64_p{ B.length p = 8 } -> state_s (G.hide SHA384)

let invariant_s #_ _ _ =
  True

let footprint_s #a (s: state_s a): GTot M.loc =
  match s with
  | SHA256_Hacl p -> M.loc_buffer p
  | SHA256_Vale p -> M.loc_buffer p
  | SHA384_Hacl p -> M.loc_buffer p

let repr #a s h: GTot _ =
  let s = B.get h s 0 in
  match s with
  | SHA256_Hacl p ->
      B.as_seq h p
  | SHA256_Vale p ->
      B.as_seq h p
  | SHA384_Hacl p ->
      B.as_seq h p
