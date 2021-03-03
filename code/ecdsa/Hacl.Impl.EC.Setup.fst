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
let prime_buffer (#c: curve): (x: glbuffer uint64 (getCoordinateLenU64 c) {witnessed #uint64 #(getCoordinateLenU64 c) x (Lib.Sequence.of_list (prime_list c)) /\ recallable x /\ felem_seq_as_nat c (Lib.Sequence.of_list (prime_list c)) == getPrime c}) = 
  match c with
  | P256 -> prime256_buffer
  | P384 -> prime384_buffer
  

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


val getK0: c: curve -> Stack (r: uint64)
  (requires fun h -> True)
  (ensures fun h0 _ h1 -> True)

(* let getKo (c: curve) : Stack (r: uint64 {v r = min_one_prime (pow2 64) (- getPrime c)}) =  *)
let getK0 c = 
  match c with 
  |P256 -> 
    assert_norm (min_one_prime (pow2 64) (- getPrime P256) == 1);
    (u64 1)
  |P384 -> 
    assert_norm (min_one_prime (pow2 64) (- getPrime P384) == 4294967297);
    (u64 4294967297)
  |Default -> 
    let i0 = index (prime_buffer #c) (size 0) in 
    let negI0 = (u64 0) -. i0 in 
    Hacl.Bignum.ModInv64.mod_inv_u64 negI0
  (* |_ -> (u64 1) *)



(* TODO: Move it away *)
inline_for_extraction noextract
let sqPower_list_p256 : list uint8 =
  [
      u8 0;  u8 0;  u8 0;  u8 0;   u8 0;   u8 0;   u8 0;   u8 0;
      u8 0;  u8 0;  u8 0;  u8 64;  u8 0;   u8 0;   u8 0;   u8 0;
      u8 0;  u8 0;  u8 0;  u8 0;   u8 0;   u8 0;   u8 0;   u8 64;
      u8 0;  u8 0;  u8 0;  u8 192; u8 255; u8 255; u8 255; u8 63
  ]


inline_for_extraction noextract
let sqPower_list_p384 : list uint8 =
    [ 
      u8 0;   u8 0;   u8 0;   u8 64;  u8 0;   u8 0;   u8 0;   u8 0; 
      u8 0;   u8 0;   u8 0;   u8 192; u8 255; u8 255; u8 255; u8 191;
      u8 255; u8 255; u8 255; u8 255; u8 255; u8 255; u8 255; u8 255; 
      u8 255; u8 255; u8 255; u8 255; u8 255; u8 255; u8 255; u8 255; 
      u8 255; u8 255; u8 255; u8 255; u8 255; u8 255; u8 255; u8 255;
      u8 255; u8 255; u8 255; u8 255; u8 255; u8 255; u8 255; u8 63
   ]



inline_for_extraction noextract
let sqPower_list (#c: curve) : list uint8 = 
  match c with 
  |P256 -> sqPower_list_p256
  |P384 -> sqPower_list_p384



let sqPower_seq (#c: curve) : s: Lib.Sequence.lseq uint8 (getScalarLenNat c)
  { 
  True
    (* Lib.ByteSequence.nat_from_intseq_le s == (getPrime c + 1) / 4 /\ *)
    (* Lib.ByteSequence.nat_from_intseq_le s < getPrime c *)
  } =
  let open Lib.ByteSequence in 
  assert_norm (List.Tot.length (sqPower_list #P256) == 32);
  assert_norm (List.Tot.length (sqPower_list #P384) == 48);
  
  (* nat_from_intlist_seq_le 32 (sqPower_list #P256); *)
  (* nat_from_intlist_seq_le 48 (sqPower_list #P384);  *)
  
  (* assert_norm (nat_from_intlist_le (sqPower_list #P256)  == (getPrime P256 + 1) / 4); *)
  (* assert_norm (nat_from_intlist_le (sqPower_list #P384)  == (getPrime P384 + 1) / 4); *)
  
  Lib.Sequence.of_list (sqPower_list #c)
  


inline_for_extraction
let sqPower_buffer_p256 : x: glbuffer uint8 (getScalarLen P256) {witnessed x sqPower_seq /\ recallable x} = 
  createL_global sqPower_list_p256


inline_for_extraction
let sqPower_buffer_p384 : x: glbuffer uint8 (getScalarLen P384) {witnessed x sqPower_seq /\ recallable x} = 
  createL_global sqPower_list_p384



