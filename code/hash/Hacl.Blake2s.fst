module Hacl.Blake2s

open FStar.Mul
open FStar.HyperStack
open FStar.HyperStack.ST

open Spec.Lib.IntTypes
open Spec.Lib.IntBuf

module Spec = Spec.Blake2s

val blake2s:
    #vll: size_nat
  -> #vkk: size_nat
  -> #vnn: size_nat
  -> output: lbuffer uint8 vnn
  -> d: lbuffer uint8 vll
  -> ll: size_t{v ll + 2 * Spec.size_block <= max_size_t /\ v ll = vll}
  -> kk: size_t{v kk <= 32 /\ v kk = vkk}
  -> k: lbuffer uint8 vkk
  -> nn:size_t{1 <= v nn /\ v nn <= 32 /\ v nn = v nn} ->
  Stack unit
    (requires (fun h -> True))
    (ensures  (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 output h0 h1))

let blake2s #vll #vkk #vnn output d ll kk k nn = Hacl.Impl.Blake2s.blake2s #vll #vkk #vnn output d ll kk k nn
