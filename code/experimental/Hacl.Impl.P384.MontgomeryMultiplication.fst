module Hacl.Impl.P384.MontgomeryMultiplication

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open FStar.Math.Lemmas
open FStar.Mul

open Lib.IntTypes
open Lib.Buffer

open Hacl.Spec.P384.Definition
open Hacl.Impl.P384.LowLevel

open Hacl.Impl.LowLevel


val add12_without_carry1: t: felem12_buffer -> t1: felem12_buffer -> result: felem12_buffer -> Stack unit
  (requires (fun h -> True))
  (ensures (fun h0 _ h1 -> as_nat12 h1 result = as_nat12 h0 t + as_nat12 h0 t1))


let add12_without_carry1 t t1 result = 
  let t0 = add12 t t1 result in ()



val montgomeryMultiplicationRound: t: felem12_buffer -> round: felem12_buffer -> tempBuffer: lbuffer uint64 (size 24) -> 
  Stack unit
  (requires fun h -> live h t /\ live h round /\ as_nat12 h t < prime384 * prime384)
  (ensures fun h0 _ h1 -> modifies (loc round) h0 h1 /\
    as_nat12 h1 round = (as_nat12 h0 t + prime384 * (as_nat12 h0 t % pow2 64)) / pow2 64
  )


let montgomeryMultiplicationRound t round tempBuffer = 
  let t2 = sub tempBuffer (size 0) (size 12) in 
  let t3 = sub tempBuffer (size 12) (size 12) in 
 
  let t1 = mod64 t in 
  
    recall_contents prime384_buffer (Lib.Sequence.of_list p384_prime_list);
  shortened_mul prime384_buffer t1 t2;
  add12_without_carry1 t t2 t3;
  shift12 t3 round
  
