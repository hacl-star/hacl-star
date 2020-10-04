module Hacl.Impl.Q.LowLevel


open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer

open Hacl.Impl.P256.LowLevel

open Spec.P256
open Spec.P256.Definitions

open FStar.Mul


open Hacl.Impl.P256.LowLevel.PrimeSpecific
open Lib.Loops

open Lib.IntTypes.Intrinsics


#set-options "--fuel 0 --ifuel 0 --z3rlimit 200"

val add_red: x: felem -> y: felem -> result: felem -> 
  Stack unit 
    (requires fun h -> live h x /\ live h y /\ live h result /\ 
      eq_or_disjoint x result /\ eq_or_disjoint y result /\ 
      as_nat h x < prime256 /\ as_nat h y < prime256)
    (ensures fun h0 _ h1 -> modifies (loc result) h0 h1 /\
      as_nat h1 result == (as_nat h0 x + as_nat h0 y) % prime256)

let add_red x y result = 
  p256_add x y result


val sub_red: x: felem -> y: felem  -> result: felem -> 
  Stack unit
    (requires fun h -> live h x /\ live h y /\ live h result /\ 
      eq_or_disjoint x result /\ eq_or_disjoint y result /\ 
      as_nat h x < prime256 /\ as_nat h y < prime256 )
    (ensures fun h0 _ h1 -> modifies (loc result) h0 h1 /\
      as_nat h1 result = (as_nat h0 x - as_nat h0 y) % prime256)



let sub_red x y result = 
  p256_sub x y result
    

    
val generateRandomShares: 
  x: felem 
  -> shares: size_t 
  -> l: lbuffer uint64 (size 4 *. shares) 
  -> Stack unit 
    (requires fun h -> True)
    (ensures fun h0 _ h1 -> True)


let generateRandomShares x shares l = 
  let last = sub l (size 4 *. (shares -. 1ul)) (size 4) in 
  let inv h (i: nat) = True in 
  for 0ul (shares -. 1ul) inv (fun i -> 
    let ith_share = sub l (size 4 *. i) (size 4) in 
    add_red last ith_share last);
  sub_red x last last

  
 




val rejoinShares: shares: size_t
  -> l: lbuffer uint64 (size 4 *. shares) 
  -> result: felem -> 
  Stack unit 
    (requires fun h -> True)
    (ensures fun h0 _ h1 -> True)


let rejoinShares shares l result = 
  let inv h (i: nat) = True in 
  for 0ul shares inv (fun i ->
    admit();
    let share = sub l (size 4 *. i) (size 4) in 
    p256_add share result result)
    


val add4_secr: x: felem 
  -> y: felem 
  -> result: felem 
  -> n: size_t 
  -> randomness: lbuffer uint64 (size 4 *. (n -. 1)) -> 
  Stack uint64
  (requires fun h -> live h x /\ live h y /\ live h result)
  (ensures fun h0 _ h1 -> True)


let add4_secr x y result n randomness = 
  push_frame();
    let shares = create (size 4 *. n) (u64 0) in
    copy shares randomness;
    generateRandomShares x n shares;
    let inv h (i: nat) = True in 
    

    let shares2 = create (size 4 *. n) (u64 0) in 
    copy shares randomness;
    generateRandomShares y n shares2;
    
  for 0ul n inv (fun i -> 
    let share = sub shares (size 4 *. i) (size 4) in  
    let share2 = sub shares2 (size 4 *. i) (size 4) in 
    p256_add share share2 share);

  rejoinShares n shares result;
  

  pop_frame();
    (u64 0)
  
