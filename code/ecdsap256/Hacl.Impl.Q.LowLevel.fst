module Hacl.Impl.M.LowLevel


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


val _sub_red: x: glbuffer uint64 (size 4) -> y: felem  -> result: felem -> 
  Stack unit
    (requires fun h -> live h x /\ live h y /\ live h result /\ 
      disjoint x result /\ disjoint result y /\
      as_nat_il h x > as_nat h y
    )
    (ensures fun h0 c h1 -> modifies1 result h0 h1 /\ 
      (
	as_nat h1 result == as_nat_il h0 x - as_nat h0 y
      )
    )

let _sub_red x y result = 
  let h0 = ST.get() in 
    let r0 = sub result (size 0) (size 1) in 
    let r1 = sub result (size 1) (size 1) in 
    let r2 = sub result (size 2) (size 1) in 
    let r3 = sub result (size 3) (size 1) in 

    let cc = sub_borrow_u64 (u64 0) x.(size 0) y.(size 0) r0 in
    let cc = sub_borrow_u64 cc x.(size 1) y.(size 1) r1 in 
    let cc = sub_borrow_u64 cc x.(size 2) y.(size 2) r2 in 
    let cc = sub_borrow_u64 cc x.(size 3) y.(size 3) r3 in 


    assert_norm (pow2 64 * pow2 64 = pow2 128);
    assert_norm (pow2 64 * pow2 64 * pow2 64 = pow2 192);
    assert_norm (pow2 64 * pow2 64 * pow2 64 * pow2 64 = pow2 256)


val sub_red: y: felem -> Stack unit
  (requires fun h -> live h y /\ as_nat h y < prime256)
  (ensures fun h0 _ h1 -> modifies (loc y) h0 h1)


let sub_red y = 
  push_frame();
    let tempBuffer = create (size 4) (u64 0) in 
    recall_contents prime256_buffer (Lib.Sequence.of_list p256_prime_list);
    _sub_red prime256_buffer y tempBuffer;
    copy y tempBuffer;
  pop_frame()
    


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
  for 0ul shares inv (fun i -> 
    let ith_share = sub l (size 4 *. i) (size 4) in 
    add_red last ith_share last);
  sub_red last


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

    generateRandomShares x n shares;

  pop_frame();
    (u64 0)
  
