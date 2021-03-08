module Hacl.Impl.EC.Setup

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer

open Hacl.Spec.P256.Definition
open Spec.P256
open FStar.Mul

noextract 
val lst_as_nat_: a: list uint64 -> i: nat {i <= List.Tot.Base.length a} ->  
  Tot nat (decreases List.Tot.Base.length a - i)

let rec lst_as_nat_ a i = 
  if i = List.Tot.Base.length a then 0 else
  let a_i = List.Tot.Base.index a i in
  lst_as_nat_ a (i + 1) + pow2 (64 * i) * v a_i

val lst_as_nat: a: list uint64 -> Tot nat 

let lst_as_nat a = lst_as_nat_ a 0


val lst_as_nat_0: a: list uint64 -> Lemma (lst_as_nat_ a (List.Tot.Base.length a) = 0)

let lst_as_nat_0 a = ()

val lst_as_nat_definiton: a: list uint64 -> i: nat {i < List.Tot.Base.length a} ->
  Lemma (lst_as_nat_  a i == lst_as_nat_ a (i + 1) + pow2 (64 * i) * v (List.Tot.Base.index a i))

let lst_as_nat_definiton b i = ()

#set-options "--z3rlimit 100"

val lemma_lst_1: a: list uint64 {List.Tot.Base.length a > 1} 
  -> i: nat {i > 0 /\ i < List.Tot.Base.length a} ->
  Lemma (lst_as_nat_ a (List.Tot.Base.length a - i) % pow2 64 == 0)

open FStar.Math.Lemmas 

let rec lemma_lst_1 a i = 
  match i with 
  |1 -> assert(i == 1);
    lst_as_nat_definiton a (List.Tot.Base.length a - 1);
    let index = List.Tot.Base.length a - 1 in
    lst_as_nat_0 a;
    lemma_mod_mul_distr_l (pow2 64 * index) (v (List.Tot.Base.index a index)) (pow2 64);
    pow2_multiplication_modulo_lemma_1 (v (List.Tot.Base.index a index)) 64 (64 * index)
  |_ -> 
    let z = List.Tot.Base.length a - i in 
    lst_as_nat_definiton a z;
    lemma_lst_1 a (i - 1); 
	
    lemma_mod_add_distr (pow2 (64 * z) * v (List.Tot.Base.index a z)) (lst_as_nat_ a (z + 1)) (pow2 64);
    pow2_multiplication_modulo_lemma_1 (v (List.Tot.Base.index a z)) 64 (64 * z)


val lemmaLstLastWord: a: list uint64 {List.Tot.Base.length a > 1} -> Lemma
  (v (List.Tot.Base.index a 0) == lst_as_nat a % pow2 64)

let lemmaLstLastWord a = 
  lst_as_nat_definiton a 0;
  lst_as_nat_definiton a 1;
  lemma_lst_1 a (List.Tot.Base.length a - 1)



(* This code contains the prime code *)
inline_for_extraction noextract
let p256_prime_list : x:list uint64{List.Tot.length x == 4 (*/\ (
    let l0 = uint_v (List.Tot.index x 0) in 
    let l1 = uint_v (List.Tot.index x 1) in 
    let l2 = uint_v (List.Tot.index x 2) in 
    let l3 = uint_v (List.Tot.index x 3) in 
    l0 + l1 * pow2 64 + l2 * pow2 128 + l3 * pow2 192 == prime256) *) /\ 
    lst_as_nat x == prime256
  } =
  [@inline_let]
  let x = [ (u64 0xffffffffffffffff);  (u64 0xffffffff); (u64 0);  (u64 0xffffffff00000001);] in
  assert_norm(0xffffffffffffffff + 0xffffffff * pow2 64 + 0xffffffff00000001 * pow2 192 == prime256);
  x


inline_for_extraction noextract
let p384_prime_list : x:list uint64{List.Tot.length x == 6 /\ 
  (
    let l0 = uint_v (List.Tot.index x 0) in 
    let l1 = uint_v (List.Tot.index x 1) in 
    let l2 = uint_v (List.Tot.index x 2) in 
    let l3 = uint_v (List.Tot.index x 3) in 
    let l4 = uint_v (List.Tot.index x 4) in 
    let l5 = uint_v (List.Tot.index x 5) in 
    l0 + l1 * pow2 64 + l2 * pow2 128 + l3 * pow2 192 + l4 * pow2 256 + l5 * pow2 320 == prime384 /\
    lst_as_nat x == prime384
    
    )
  } =
  let open FStar.Mul in 
  [@inline_let]
  let x =
    [ (u64 0xffffffff);  (u64 0xffffffff00000000); (u64 0xfffffffffffffffe);  (u64 0xffffffffffffffff); (u64 0xffffffffffffffff); (u64 0xffffffffffffffff);] in
    assert_norm(0xffffffff + 0xffffffff00000000 * pow2 64 + 0xfffffffffffffffe * pow2 128 + 
    0xffffffffffffffff * pow2 192 +  0xffffffffffffffff * pow2 256 +  0xffffffffffffffff * pow2 320 == prime384);
  x


inline_for_extraction noextract
let prime_list (c: curve) :  (x: list uint64 {List.Tot.length x == uint_v (getCoordinateLenU64 c) /\ (
  match c with
  |P256 -> 
    let open FStar.Mul in 
    let l0 = uint_v (List.Tot.index x 0) in 
    let l1 = uint_v (List.Tot.index x 1) in 
    let l2 = uint_v (List.Tot.index x 2) in 
    let l3 = uint_v (List.Tot.index x 3) in 
    l0 + l1 * pow2 64 + l2 * pow2 128 + l3 * pow2 192 == prime256
  |P384 -> 
    let open FStar.Mul in 
    let l0 = uint_v (List.Tot.index x 0) in 
    let l1 = uint_v (List.Tot.index x 1) in 
    let l2 = uint_v (List.Tot.index x 2) in 
    let l3 = uint_v (List.Tot.index x 3) in 
    let l4 = uint_v (List.Tot.index x 4) in 
    let l5 = uint_v (List.Tot.index x 5) in 
    l0 + l1 * pow2 64 + l2 * pow2 128 + l3 * pow2 192 + l4 * pow2 256 + l5 * pow2 320 == prime384
)}) = 
  let open FStar.Mul in 
  match c with 
  |P256 -> 
    p256_prime_list
  |P384 -> 
    p384_prime_list


inline_for_extraction
let prime256_buffer: x: glbuffer uint64 4ul {witnessed #uint64 #(size 4) x (Lib.Sequence.of_list p256_prime_list) /\ recallable x /\ felem_seq_as_nat P256 (Lib.Sequence.of_list (p256_prime_list)) == prime256} =
  assert_norm (felem_seq_as_nat P256 (Lib.Sequence.of_list (p256_prime_list)) == prime256);
  (* [@inline_let] *)
  (* let l = List.Tot.Base.tail p256_prime_list in *)
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
let getLastWord (#c: curve) : (r: uint64 {uint_v r == getPrime c % pow2 64}) = 
  match c with 
  |P256 -> 
    lemmaLstLastWord p256_prime_list;
    normalize_term (List.Tot.Base.index p256_prime_list 0)
  |P384 -> 
    lemmaLstLastWord p384_prime_list;
    normalize_term (List.Tot.Base.index p384_prime_list 0)
  |_ -> admit()
  





inline_for_extraction noextract
let basePointP256 : x:list uint64{List.Tot.length x == 12 (*/\ 
  (
    let open FStar.Mul in 
    let l0 = uint_v (List.Tot.index x 0) in 
    let l1 = uint_v (List.Tot.index x 1) in 
    let l2 = uint_v (List.Tot.index x 2) in 
    let l3 = uint_v (List.Tot.index x 3) in 
    l0 + l1 * pow2 64 + l2 * pow2 128 + l3 * pow2 192 == prime256) *)
  } =
  let open FStar.Mul in 
  [@inline_let]
  let x =
    [
      u64 0x79e730d418a9143c; u64 0x75ba95fc5fedb601; u64 0x79fb732b77622510; u64 0x18905f76a53755c6;
      u64 0xddf25357ce95560a; u64 0x8b4ab8e4ba19e45c; u64 0xd2e88688dd21f325; u64 0x8571ff1825885d85;
      u64 0x1;                u64 0xffffffff00000000; u64 0xffffffffffffffff; u64 0xfffffffe;
  ] in
    (* assert_norm(0xffffffffffffffff + 0xffffffff * pow2 64 + 0xffffffff00000001 * pow2 192 == prime256); *)
  x









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

(*
val get_prime_inverse_buffer: #c: curve -> 
*)





val getK0: c: curve -> Stack (r: uint64 {v r = min_one_prime (pow2 64) (- getPrime c)})
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



