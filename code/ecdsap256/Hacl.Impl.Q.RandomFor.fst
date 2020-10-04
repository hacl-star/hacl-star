module Hacl.Impl.Q.RandomFor


open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer

open Hacl.Impl.P256.LowLevel

open FStar.Mul
open Lib.Loops


(* Well, for now I invented the way to randomise the flow, it´s not based on any clever research *)


#set-options "--fuel 0 --ifuel 0 --z3rlimit 200"


val swap: shares: size_t -> b: lbuffer size_t shares 
  -> i0: size_t {v i0 < v shares} 
  -> i1: size_t {v i1 < v shares} 
  -> Stack unit 
    (requires fun h -> live h b)
    (ensures fun h0 _ h1 -> True)

let swap shares b i0 i1 = 
  let s0 = index b i0 in 
  let s1 = index b i1 in 
  upd b i0 s1;
  upd b i1 s0


val permutation: shares: size_t
  -> b: lbuffer size_t shares 
  -> lenRandomness: size_t {v lenRandomness % 2 == 0} 
  (* I don´t know the exact number, it was just for testing *) 
  -> randomness: lbuffer uint8 lenRandomness
  -> Stack unit
  (requires fun h -> True)
  (ensures fun h0 _ h1 -> True)


let permutation shares b lenRandomness randomness = 
  let open Lib.RawIntTypes in 
  
  let inv h (i: nat) = True in 
  let halfLen = lenRandomness >>. (size 1) in 
  for 0ul halfLen inv (fun i -> 
    let randomI = index randomness (2ul *. i) in 
    let randomI1 = index randomness (2ul *. i +. 1) in 
    let index0 = u8_to_UInt8 (logand randomI (shares -. 1ul)) in 
    let index1 = u8_to_UInt8 (logand randomI1 (shares -. 1ul)) in 
    swap shares b index0 index1
  )


val makeShareSchedule: 
  shares: size_t -> 
  lbuffer size_t shares -> 
  lenRandomness: size_t ->
  randomness: lbuffer uint8 lenRandomness ->
  Stack unit
  (requires fun h -> True)
  (ensures fun h0 _ h1 -> True)

let makeShareSchedule shares b lenRandomness randomness = 
  let inv h (i: nat) = True in 
  for 0ul shares inv (fun i ->
    upd #_ #shares b i i);
  permutation shares b lenRandomness randomness


(*
inline_for_extraction
val for:
    start:size_t
  -> finish:size_t{v finish >= v start}
  -> inv:(mem -> (i:nat{v start <= i /\ i <= v finish}) -> Type0)
  -> f:(i:size_t{v start <= v i /\ v i < v finish} -> Stack unit
                  (requires fun h -> inv h (v i))
                  (ensures  fun h_1 _ h_2 -> inv h_2 (v i + 1))) ->
  Stack unit
    (requires fun h -> inv h (v start))
    (ensures  fun _ _ h_2 -> inv h_2 (v finish))

*)

val forRandom: 
  finish: size_t
  -> inv: (mem -> i : nat -> Type0) 
  -> f: (i: nat -> Stack unit (requires fun h -> True) (ensures fun h0 _ h1 -> True))
  -> lenRandomness: size_t
  -> randomness: lbuffer uint8 lenRandomness
  ->
  Stack unit 
    (requires fun h -> True)
    (ensures fun h0 _ h1 -> True)


let forRandom finish inv f lenRandomness randomness = 
  push_frame();
    let bufferSchedule = create finish (size 0) in 
    let schedule = makeShareSchedule finish bufferSchedule lenRandomness randomness in 
  pop_frame()
