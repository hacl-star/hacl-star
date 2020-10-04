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
(* https://youtu.be/QFFrkZOYojk *)

#set-options "--fuel 0 --ifuel 0 --z3rlimit 200"

let sizeOfShare = 4ul

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


open Spec.P256.Definitions

inline_for_extraction noextract
val forRandom: 
  lenShares: size_t
  -> sharesFrom0: lbuffer uint64 (sizeOfShare *. lenShares)
  -> sharesFrom1: lbuffer uint64 (sizeOfShare *. lenShares) 
  -> sharesTo: lbuffer uint64 (sizeOfShare *. lenShares)
  
  -> inv: (mem -> Type0)
  -> f: (felem -> felem -> felem -> Stack unit (requires fun h -> inv h) (ensures fun h0 _ h1 -> inv h1))
  
  -> lenRandomness: size_t
  -> randomness: lbuffer uint8 (3ul *. lenRandomness) 
  ->
  Stack unit 
    (requires fun h -> True)
    (ensures fun h0 _ h1 -> True)


let forRandom lenShares sharesFrom0 sharesFrom1 sharesTo inv f lenRandomness randomness = 
  push_frame();
    let bufferSchedule0 = create lenShares (size 0) in 
    let bufferSchedule1 = create lenShares (size 0) in 
    let bufferSchedule2 = create lenShares (size 0) in 
    
    let random0 = sub randomness 0ul lenRandomness in 
    let random1 = sub randomness lenRandomness lenRandomness in 
    let random2 = sub randomness (2ul *. lenRandomness) lenRandomness in 
    
    makeShareSchedule lenShares bufferSchedule0 lenRandomness random0;		      
    makeShareSchedule lenShares bufferSchedule1 lenRandomness random1;
    makeShareSchedule lenShares bufferSchedule2 lenRandomness random2;
    
    let inv h (i: nat) = True in 
    for 0ul lenShares inv (fun i -> 
      let indexFrom0 = index bufferSchedule0 i in 
      let indexFrom1 = index bufferSchedule1 i in 
      let indexTo = index bufferSchedule2 i in 
      
      let shareFrom0 = index sharesFrom0 indexFrom0 in 
      let shareFrom1 = index sharesFrom1 indexFrom1 in 
      let shareTo = index sharesTo indexTo in 

      f shareFrom0 shareFrom1 shareTo
      
      
      );
      
  pop_frame()



(* and less crazy version *)



inline_for_extraction noextract
val forRandom1: 
  lenShares: size_t
  -> sharesFrom0: lbuffer uint64 (sizeOfShare *. lenShares)
  -> sharesFrom1: lbuffer uint64 (sizeOfShare *. lenShares) 
  -> sharesTo: lbuffer uint64 (sizeOfShare *. lenShares)
  
  -> inv: (mem -> Type0)
  -> f: (felem -> felem -> felem -> Stack unit (requires fun h -> inv h) (ensures fun h0 _ h1 -> inv h1))
  
  -> lenRandomness: size_t
  -> randomness: lbuffer uint8 ( lenRandomness) 
  ->
  Stack unit 
    (requires fun h -> True)
    (ensures fun h0 _ h1 -> True)


let forRandom1 lenShares sharesFrom0 sharesFrom1 sharesTo inv f lenRandomness randomness = 
  push_frame();
    let bufferSchedule = create lenShares (size 0) in 
    let random = sub randomness 0ul lenRandomness in 
    makeShareSchedule lenShares bufferSchedule lenRandomness random;
    
    let inv h (i: nat) = True in 
    for 0ul lenShares inv (fun i -> 
      let indexReference = index bufferSchedule i in 
      
      let shareFrom0 = index sharesFrom0 indexReference in 
      let shareFrom1 = index sharesFrom1 indexReference in 
      let shareTo = index sharesTo indexReference in 

      f shareFrom0 shareFrom1 shareTo
      
      
      );
      
  pop_frame()
