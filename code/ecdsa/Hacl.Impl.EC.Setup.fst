module Hacl.Impl.EC.Setup

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer

open Hacl.Spec.P256.Definition
open Spec.P256
open FStar.Mul

inline_for_extraction
let prime256_buffer: x: glbuffer uint64 4ul {witnessed #uint64 #(size 4) x (Lib.Sequence.of_list p256_prime_list) /\ recallable x /\ felem_seq_as_nat P256 (Lib.Sequence.of_list (p256_prime_list)) == prime256} =
  assert_norm (felem_seq_as_nat P256 (Lib.Sequence.of_list (p256_prime_list)) == prime256);
  createL_global p256_prime_list


inline_for_extraction
let prime384_buffer: x: glbuffer uint64 6ul {witnessed #uint64 #(size 6) x (Lib.Sequence.of_list
p384_prime_list) /\ recallable x /\ felem_seq_as_nat P384 (Lib.Sequence.of_list (p384_prime_list)) == prime384}  = 
  assert_norm (felem_seq_as_nat P384 (Lib.Sequence.of_list (p384_prime_list)) == prime384);
  createL_global p384_prime_list


inline_for_extraction
let prime256order_buffer: x: glbuffer uint64 (size 4)  
  {witnessed #uint64 #(size 4) x 
  (Lib.Sequence.of_list p256_order_list) /\ recallable x /\ 
  felem_seq_as_nat P256 (Lib.Sequence.of_list (p256_order_list)) == getOrder #P256} = 
  createL_global p256_order_list


inline_for_extraction
let prime384order_buffer: x: glbuffer uint64 (size 6)  
  {witnessed #uint64 #(size 6) x 
  (Lib.Sequence.of_list p384_order_list) /\ recallable x /\ 
  felem_seq_as_nat P384 (Lib.Sequence.of_list (p384_order_list)) == getOrder #P384} = 
  createL_global p384_order_list


inline_for_extraction
let order_buffer (#c: curve): (x: glbuffer uint64 (getCoordinateLenU64 c) 
    {witnessed #uint64 #(getCoordinateLenU64 c) x (Lib.Sequence.of_list (prime_list c)) 
    /\ recallable x /\ felem_seq_as_nat c (Lib.Sequence.of_list (order_list c)) == getOrder #c}) = 
  match c with
  | P256 -> prime256order_buffer
  | P384 -> prime384order_buffer


let primep256_inverse_seq: s: Lib.Sequence.lseq uint8 32 {Lib.ByteSequence.nat_from_intseq_le s == getPrime P256 - 2} = 
  let prime = prime_inverse_list P256 in 
  assert_norm (List.Tot.length prime == 32);
  assert_norm (Spec.ECDSA.Lemmas.nat_from_intlist_le prime == getPrime P256 - 2);
  Spec.ECDSA.Lemmas.nat_from_intlist_seq_le 32 prime;
  Lib.Sequence.of_list prime


let primep384_inverse_seq: s: Lib.Sequence.lseq uint8 48 {Lib.ByteSequence.nat_from_intseq_le s == getPrime P384 - 2} = 
  let prime = prime_inverse_list P384 in 
  assert_norm (List.Tot.length prime == 48);
  assert_norm (Spec.ECDSA.Lemmas.nat_from_intlist_le prime == getPrime P384 - 2);
  Spec.ECDSA.Lemmas.nat_from_intlist_seq_le 48 prime;
  Lib.Sequence.of_list prime


let prime_inverse_seq (#c: curve) : s: Lib.Sequence.lseq uint8 (v (getCoordinateLenU c)) {Lib.ByteSequence.nat_from_intseq_le s == getPrime c - 2} = 
    let prime = prime_inverse_list c in 
    assert_norm (List.Tot.length (prime_inverse_list P256) == 32);
    assert_norm (List.Tot.length (prime_inverse_list P384) == 48);
    assert_norm (Spec.ECDSA.Lemmas.nat_from_intlist_le (prime_inverse_list P256) == getPrime P256 - 2);
    assert_norm (Spec.ECDSA.Lemmas.nat_from_intlist_le (prime_inverse_list P384) == getPrime P384 - 2);
    Spec.ECDSA.Lemmas.nat_from_intlist_seq_le (v (getCoordinateLenU c)) prime;
    
    Lib.Sequence.of_list (prime_inverse_list c)
  
  

inline_for_extraction
let prime256_inverse_buffer: x: glbuffer uint8 32ul
  {witnessed #uint8 #(size 32) x primep256_inverse_seq /\ recallable x} = 
  createL_global p256_inverse_list

inline_for_extraction
let prime384_inverse_buffer: x: glbuffer uint8 48ul
  {witnessed #uint8 #(size 48) x primep384_inverse_seq /\ recallable x} = 
  createL_global p384_inverse_list


inline_for_extraction
let prime_inverse_buffer (#c: curve): (x: glbuffer uint8 (getCoordinateLenU c)
  {witnessed #uint8 #(getCoordinateLenU c) x (prime_inverse_seq #c) /\ recallable x}) = 
    match c with
  | P256 -> prime256_inverse_buffer
  | P384 -> prime384_inverse_buffer
