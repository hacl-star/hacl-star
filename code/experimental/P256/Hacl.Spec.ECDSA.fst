module Hacl.Spec.ECDSA

open FStar.Mul 
open Hacl.Spec.ECDSAP256.Definition
open Hacl.Spec.P256.Lemmas

open Lib.ByteSequence
open Lib.IntTypes
open Lib.Sequence


let prime = prime_p256_order 
let nat_prime = (n: nat {n < prime})


let ith_bit (k:lbytes 32) (i:nat{i < 256}) : (t: uint64 {uint_v t == 0 \/ uint_v t == 1}) =
  let q = i / 8 in let r = size (i % 8) in
  admit();
  to_u64 ((index k q >>. r) &. u8 1)

let ( *% ) a b = (a * b) % prime


val _exp_step0: p: nat_prime -> q: nat_prime -> 
  Tot (t: tuple2 nat_prime nat_prime {let t0, t1 = t in t0 == (p * p) % prime_p256_order /\ t1 == (p * q) % prime_p256_order})

let _exp_step0 r0 r1 = 
  let r1 = r0 *% r1 in 
  let r0 = r0 *% r0 in 
  r0, r1

val _exp_step1: p: nat_prime -> q: nat_prime -> 
  Tot (t: tuple2 nat_prime nat_prime {let t0, t1 = t in t0 == (p * q) % prime_p256_order /\ t1 == (q * q) % prime_p256_order})

let _exp_step1 r0 r1 = 
  let r0 = r0 *% r1 in 
  let r1 = r1 *% r1 in 
  (r0, r1)


val swap: p: nat_prime -> q: nat_prime -> Tot (r: tuple2 nat_prime nat_prime{let pNew, qNew = r in 
  pNew == q /\ qNew == p})

let swap p q = (q, p)


val conditional_swap: i: uint64 -> p: nat_prime -> q: nat_prime -> Tot (r: tuple2 nat_prime nat_prime
  {
    let pNew, qNew = r in 
    if uint_v i = 0 then pNew == p /\ qNew == q
    else
      let p1, q1 = swap p q in 
      p1 == pNew /\ q1 == qNew
 }
)

#reset-options "--z3refresh --z3rlimit  100"

let conditional_swap i p q = 
  if uint_v i = 0 then 
    (p, q)
  else
    (q, p)

val lemma_swaped_steps: p: nat_prime -> q: nat_prime -> 
  Lemma (
    let (afterSwapP, afterSwapQ) = swap p q in 
    let p1, q1 = _exp_step0 afterSwapP afterSwapQ in 
    let p2, q2 = swap p1 q1 in 
    let r0, r1 = _exp_step1 p q in 
    p2 == r0 /\ q2 == r1)

let lemma_swaped_steps p q = ()

open Lib.RawIntTypes 

val _exp_step: k:  lseq uint8 32 ->  i: nat{i < 256} -> tuple2 nat_prime nat_prime ->
  Tot (t: tuple2 nat_prime nat_prime)

let _exp_step k i (p, q) = 
  let bit = 255 - i in 
  let bit = ith_bit k bit in 
  if uint_to_nat bit = 0 then 
      _exp_step0 p q 
  else _exp_step1 p q  

#reset-options "--z3refresh --z3rlimit 300"

val _exponent_spec: k: lseq uint8 32  -> tuple2 nat_prime nat_prime -> Tot (tuple2 nat_prime nat_prime)

let _exponent_spec k (p, q) = 
  Lib.LoopCombinators.repeati 256  (_exp_step k) (p, q)


unfold let prime_p256_order_inverse_list: list uint8 = 
   [
     (u8 79); (u8 37); (u8 99); (u8 252); (u8 194); (u8 202); (u8 185); (u8 243); 
     (u8 132); (u8 158); (u8 23); (u8 167); (u8 173); (u8 250); (u8 230); (u8 188); 
     (u8 255); (u8 255); (u8 255); (u8 255); (u8 255); (u8 255); (u8 255); (u8 255);
     (u8 0); (u8 0); (u8 0); (u8 0); (u8 255); (u8 255); (u8 255); (u8 255)
   ]

let prime_p256_order_inverse_seq: lseq uint8 32 = 
  assert_norm (List.Tot.length prime_p256_order_inverse_list == 32);
  of_list prime_p256_order_inverse_list


unfold let prime_p256_order_list: list uint8 = 
   [
     (u8 81); (u8 37); (u8 99); (u8 252); (u8 194); (u8 202); (u8 185); (u8 243); 
     (u8 132); (u8 158); (u8 23); (u8 167); (u8 173); (u8 250); (u8 230); (u8 188); 
     (u8 255); (u8 255); (u8 255); (u8 255); (u8 255); (u8 255); (u8 255); (u8 255);
     (u8 0); (u8 0); (u8 0); (u8 0); (u8 255); (u8 255); (u8 255); (u8 255)
   ]

let prime_p256_order_seq: lseq uint8 32 = 
  assert_norm (List.Tot.length prime_p256_order_list == 32);
  of_list prime_p256_order_list

open Hacl.Spec.P256.Definitions

val exponent_spec: a: nat_prime -> Tot (r: nat_prime {r = pow a (prime_p256_order - 2) % prime_p256_order})

let exponent_spec a = 
    admit();
    let a0, _ = _exponent_spec prime_p256_order_inverse_seq (1, a) in
    a0

val power_distributivity_2: a: nat -> b: nat -> c: pos -> 
  Lemma (pow (a * b) c == pow a c * pow b c)

let rec power_distributivity_2 a b c = 
  match c with 
  |0 -> ()
  |1 -> ()
  | _ ->
    let open FStar.Tactics in 
    let open FStar.Tactics.Canon in
    power_distributivity_2 a b (c - 1);
    assert(pow (a * b) (c - 1) == pow a (c - 1) * pow b (c - 1));
    assert(pow (a * b) (c - 1) * pow (a * b) 1 == pow a (c - 1) * pow b (c - 1) * pow (a * b) 1);
    
    assert(pow (a * b) (c - 1) * pow (a * b) 1 == pow (a * b) c);
    assert(pow (a * b) 1 == a * b);
    assert(pow a (c - 1) * pow b (c - 1) * pow (a * b) 1 == pow a (c - 1) * pow b (c - 1) * a * b);
    assert_by_tactic (pow a (c - 1) * pow b (c - 1) * a * b == (pow a c * pow b c)) canon;
    assert(pow a (c - 1) * pow b (c - 1) * pow (a * b) 1 == (pow a c * pow b c));
    assert(pow a c * pow b c == pow (a * b) c)
