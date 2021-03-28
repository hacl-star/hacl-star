module Hacl.Impl.EC.Setup

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer

open Hacl.Spec.EC.Definition
open Spec.ECC
open Spec.ECC.Curves
open FStar.Mul

noextract 
val lst_as_nat_: #t:inttype{unsigned t} -> a: list (uint_t t SEC) -> i: nat {i <= List.Tot.Base.length a} ->  
  Tot nat (decreases List.Tot.Base.length a - i)

let rec lst_as_nat_ #t a i = 
  if i = List.Tot.Base.length a then 0 else
  let a_i = List.Tot.Base.index a i in
  lst_as_nat_ a (i + 1) + pow2 (bits t * i) * v a_i

val lst_as_nat: #t:inttype{unsigned t} -> a: list (uint_t t SEC) -> Tot nat 

let lst_as_nat a = lst_as_nat_ a 0


val lst_as_nat_0: #t:inttype{unsigned t} -> a: list (uint_t t SEC) -> Lemma (lst_as_nat_ a (List.Tot.Base.length a) = 0)

let lst_as_nat_0 a = ()


val lst_as_nat_definiton: #t:inttype{unsigned t} -> a: list (uint_t t SEC) -> i: nat {i < List.Tot.Base.length a} ->
  Lemma (lst_as_nat_  a i == lst_as_nat_ a (i + 1) + pow2 (bits t * i) * v (List.Tot.Base.index a i))

let lst_as_nat_definiton b i = ()

#set-options "--z3rlimit 100"

val lemma_lst_1: #t:inttype{unsigned t} -> a: list (uint_t t SEC) -> i: nat {i > 0 /\ i < List.Tot.Base.length a} ->
  Lemma (lst_as_nat_ a (List.Tot.Base.length a - i) % pow2 (bits t) == 0)

open FStar.Math.Lemmas 

let rec lemma_lst_1 #t a i = 
  match i with 
  |1 -> assert(i == 1);
    lst_as_nat_definiton a (List.Tot.Base.length a - 1);
    let index = List.Tot.Base.length a - 1 in
    lst_as_nat_0 a;
    lemma_mod_mul_distr_l (pow2 (bits t) * index) (v (List.Tot.Base.index a index)) (pow2 (bits t));
    pow2_multiplication_modulo_lemma_1 (v (List.Tot.Base.index a index)) (bits t) ((bits t) * index)
  |_ -> 
    let z = List.Tot.Base.length a - i in 
    lst_as_nat_definiton a z;
    lemma_lst_1 a (i - 1); 
	
    lemma_mod_add_distr (pow2 ((bits t) * z) * v (List.Tot.Base.index a z)) (lst_as_nat_ a (z + 1)) (pow2 (bits t));
    pow2_multiplication_modulo_lemma_1 (v (List.Tot.Base.index a z)) (bits t) ((bits t) * z)


val lemmaLstLastWord: a: list uint64 {List.Tot.Base.length a > 1} -> Lemma
  (v (List.Tot.Base.index a 0) == lst_as_nat a % pow2 64)

let lemmaLstLastWord a = lemma_lst_1 a (List.Tot.Base.length a - 1)


val lemma_lst_nat_instant_4: a: list uint64 {List.Tot.length a == 4} -> Lemma (
  lst_as_nat a == 
    v (List.Tot.index a 0) * pow2 (64 * 0) + 
    v (List.Tot.index a 1) * pow2 (64 * 1) + 
    v (List.Tot.index a 2) * pow2 (64 * 2) +
    v (List.Tot.index a 3) * pow2 (64 * 3))

let lemma_lst_nat_instant_4 a = 
  lst_as_nat_definiton a 3;
  lst_as_nat_definiton a 2;
  lst_as_nat_definiton a 1;
  lst_as_nat_definiton a 0


val lemma_lst_nat_instant_6: a: list uint64 {List.Tot.length a == 6} -> Lemma (
  lst_as_nat a == 
    v (List.Tot.index a 0) * pow2 (64 * 0) + 
    v (List.Tot.index a 1) * pow2 (64 * 1) + 
    v (List.Tot.index a 2) * pow2 (64 * 2) +
    v (List.Tot.index a 3) * pow2 (64 * 3) +
    v (List.Tot.index a 4) * pow2 (64 * 4) +
    v (List.Tot.index a 5) * pow2 (64 * 5))

let lemma_lst_nat_instant_6 a = 
  lst_as_nat_definiton a 5;
  lst_as_nat_definiton a 4;
  lst_as_nat_definiton a 3;
  lst_as_nat_definiton a 2;
  lst_as_nat_definiton a 1;
  lst_as_nat_definiton a 0


(* This code contains the prime code *)
inline_for_extraction noextract
let p256_prime_list : x:list uint64{List.Tot.length x == 4 /\ lst_as_nat x == prime256} =
  [@inline_let]
  let x = [ (u64 0xffffffffffffffff);  (u64 0xffffffff); (u64 0);  (u64 0xffffffff00000001);] in
  lemma_lst_nat_instant_4 x;
  assert_norm(0xffffffffffffffff + 0xffffffff * pow2 64 + 0xffffffff00000001 * pow2 192 == prime256);
  x


inline_for_extraction noextract
let p384_prime_list : x:list uint64{List.Tot.length x == 6 /\ lst_as_nat x == prime384} =
  [@inline_let]
  let x = [ (u64 0xffffffff);  (u64 0xffffffff00000000); (u64 0xfffffffffffffffe);  (u64 0xffffffffffffffff); (u64 0xffffffffffffffff); (u64 0xffffffffffffffff);] in
  lemma_lst_nat_instant_6 x;
  assert_norm(0xffffffff + 0xffffffff00000000 * pow2 64 + 0xfffffffffffffffe * pow2 (64 * 2) + 
  0xffffffffffffffff * pow2 (64 * 3) +  0xffffffffffffffff * pow2 (64 * 4) +  0xffffffffffffffff * pow2 (64 * 5) == prime384);
  x


inline_for_extraction noextract
let prime_list (c: curve) : (x: list uint64 {List.Tot.length x == uint_v (getCoordinateLenU64 c) /\ 
  lst_as_nat x == getPrime c}) = 
  let open FStar.Mul in 
  match c with 
  |P256 -> p256_prime_list
  |P384 -> p384_prime_list
  |_ -> admit(); []


inline_for_extraction
let prime256_buffer: x: glbuffer uint64 4ul {witnessed #uint64 #(size 4) x (Lib.Sequence.of_list p256_prime_list) /\ 
  recallable x /\ lseq_as_nat (Lib.Sequence.of_list (p256_prime_list)) == prime256} =
  assert_norm (lseq_as_nat (Lib.Sequence.of_list (p256_prime_list)) == prime256);
  createL_global p256_prime_list


inline_for_extraction
let prime384_buffer: x: glbuffer uint64 6ul {witnessed #uint64 #(size 6) x (Lib.Sequence.of_list p384_prime_list) /\ 
  recallable x /\ lseq_as_nat (Lib.Sequence.of_list (p384_prime_list)) == prime384} = 
  assert_norm (lseq_as_nat (Lib.Sequence.of_list (p384_prime_list)) == prime384);
  createL_global p384_prime_list


inline_for_extraction
let prime_buffer (#c: curve): (x: glbuffer uint64 (getCoordinateLenU64 c) 
  {witnessed #uint64 #(getCoordinateLenU64 c) x (Lib.Sequence.of_list (prime_list c)) /\ recallable x /\
  lseq_as_nat (Lib.Sequence.of_list (prime_list c)) == getPrime c}) = 
  match c with
  | P256 -> prime256_buffer
  | P384 -> prime384_buffer
  

inline_for_extraction
let getLastWordPrime (#c: curve) : (r: uint64 {uint_v r == getPrime c % pow2 64}) = 
  match c with 
  |P256 -> 
    lemmaLstLastWord p256_prime_list;
    normalize_term (List.Tot.Base.index p256_prime_list 0)
  |P384 -> 
    lemmaLstLastWord p384_prime_list;
    normalize_term (List.Tot.Base.index p384_prime_list 0)
  |_ -> admit()
  

inline_for_extraction noextract
let basePointP256: x: list uint64{List.Tot.length x == 12 /\ (
  let pX = v (List.Tot.index x 0) + v (List.Tot.index x 1) * pow2 (64 * 1) + v (List.Tot.index x 2) * pow2 (64 * 2) + v (List.Tot.index x 3) * pow2 (64 * 3) in 
  let pY = v (List.Tot.index x 4) + v (List.Tot.index x 5) * pow2 (64 * 1) + v (List.Tot.index x 6) * pow2 (64 * 2) + v (List.Tot.index x 7) * pow2 (64 * 3) in 
  let pZ = v (List.Tot.index x 8) + v (List.Tot.index x 9) * pow2 (64 * 1) + v (List.Tot.index x 10) * pow2 (64 * 2) + v (List.Tot.index x 11) * pow2 (64 * 3) in 
  let (bpX, bpY, bpZ) = basePoint #P256 in  pX == bpX /\ pY == bpY /\ pZ == bpZ)} =
  [@inline_let]
  let x = [
    u64 0x79e730d418a9143c; u64 0x75ba95fc5fedb601; u64 0x79fb732b77622510; u64 0x18905f76a53755c6;
    u64 0xddf25357ce95560a; u64 0x8b4ab8e4ba19e45c; u64 0xd2e88688dd21f325; u64 0x8571ff1825885d85;
    u64 0x1;                u64 0xffffffff00000000; u64 0xffffffffffffffff; u64 0xfffffffe] in
  admit();
  x


inline_for_extraction noextract
let p256_order_list: x:list uint64 {List.Tot.length x == 4 /\ lst_as_nat x == getOrder #P256} =
  [@inline_let]
  let x = [ 
    u64 17562291160714782033; u64 13611842547513532036; u64 18446744073709551615; u64 18446744069414584320] in
  assert_norm(17562291160714782033 + 13611842547513532036 * pow2 64 + 18446744073709551615 * pow2 128 + 18446744069414584320 * pow2 192 == getOrder #P256);
  x  


inline_for_extraction noextract
let p384_order_list : x:list uint64 {List.Tot.length x == 6 /\ lst_as_nat x == getOrder #P384} =
  [@inline_let]
  let x = [ 
    u64 17072048233947408755; u64 6348401684107011962; u64 14367412456785391071; u64 18446744073709551615; u64 18446744073709551615; u64 18446744073709551615] in
  assert_norm(17072048233947408755 + 6348401684107011962 * pow2 64 + 14367412456785391071 * pow2 128 + 18446744073709551615 * pow2 192 + 18446744073709551615 * pow2 256 + 18446744073709551615 * pow2 320 == getOrder #P384);
  x  


inline_for_extraction noextract
let order_list (c: curve) : (x: list uint64 {List.Tot.length x == uint_v (getCoordinateLenU64 c) /\ lst_as_nat x == getOrder #c}) = 
  match c with 
  |P256 -> p256_order_list
  |P384 -> p384_order_list
  |_ -> admit(); []


inline_for_extraction
let getLastWordOrder (#c: curve) : (r: uint64 {uint_v r == getOrder #c % pow2 64}) = 
  match c with 
  |P256 -> 
    lemmaLstLastWord p256_prime_list;
    normalize_term (List.Tot.Base.index p256_order_list 0)
  |P384 -> 
    lemmaLstLastWord p384_prime_list;
    normalize_term (List.Tot.Base.index p384_order_list 0)
  |_ -> admit()


inline_for_extraction
let prime256order_buffer: x: glbuffer uint64 (getCoordinateLenU64 P256) {witnessed #uint64 #(getCoordinateLenU64 P256) x (Lib.Sequence.of_list p256_order_list) /\
  recallable x /\ lseq_as_nat (Lib.Sequence.of_list (order_list P256)) == getOrder #P256} = 
  createL_global p256_order_list


inline_for_extraction
let prime384order_buffer: x: glbuffer uint64 (size 6) {witnessed #uint64 #(size 6) x (Lib.Sequence.of_list p384_order_list) /\
  recallable x /\ lseq_as_nat (Lib.Sequence.of_list (order_list P384)) == getOrder #P384} = 
  createL_global p384_order_list


inline_for_extraction
let order_buffer (#c: curve): (x: glbuffer uint64 (getCoordinateLenU64 c) {
  witnessed #uint64 #(getCoordinateLenU64 c) x (Lib.Sequence.of_list (order_list c)) /\ recallable x /\ 
  lseq_as_nat (Lib.Sequence.of_list (order_list c)) == getOrder #c }) = 
  match c with
  | P256 -> prime256order_buffer
  | P384 -> prime384order_buffer
  | _ -> admit(); prime256order_buffer

(* Unfold? *)
inline_for_extraction noextract
let p256_inverse_list: x: list uint8 {List.Tot.length x == v (getScalarLenBytes P256) /\ lst_as_nat x == getPrime P256 - 2} = 
  [@inline_let]
  let x = [
    u8 253; u8 255; u8 255; u8 255; u8 255; u8 255; u8 255; u8 255;
    u8 255; u8 255; u8 255; u8 255; u8 0;   u8 0;   u8 0;   u8 0;
    u8 0;   u8 0;   u8 0;   u8 0;   u8 0;   u8 0;   u8 0;   u8 0;
    u8 1;   u8 0;   u8 0;   u8 0;   u8 255; u8 255; u8 255;  u8 255] in
  assert_norm (List.Tot.Base.length x == v (getScalarLenBytes P256));
  admit();
  x


inline_for_extraction noextract
let p384_inverse_list: x: list uint8 {List.Tot.length x == v (getScalarLenBytes P384) /\ lst_as_nat x == getPrime P384 - 2} = 
  [@inline_let]
  let x = [ 
    u8 253; u8 255; u8 255; u8 255; u8 0;   u8 0;   u8 0;   u8 0;
    u8 0;   u8 0  ; u8 0  ; u8 0  ; u8 255; u8 255; u8 255; u8 255;
    u8 254; u8 255; u8 255; u8 255; u8 255; u8 255; u8 255; u8 255;
    u8 255; u8 255; u8 255; u8 255; u8 255; u8 255; u8 255; u8 255;
    u8 255; u8 255; u8 255; u8 255; u8 255; u8 255; u8 255; u8 255;
    u8 255; u8 255; u8 255; u8 255; u8 255; u8 255; u8 255; u8 255] in 
  assert_norm (List.Tot.Base.length x == v (getScalarLenBytes P384));
  admit();
  x


inline_for_extraction noextract
let prime_inverse_list (c: curve) : x: list uint8 {List.Tot.length x == v (getScalarLenBytes c) /\ 
  lst_as_nat x == getPrime c - 2} = 
  match c with 
  |P256 -> p256_inverse_list
  |P384 -> p384_inverse_list
  |_ -> admit()


inline_for_extraction
let prime256_inverse_buffer: x: glbuffer uint8 32ul {
  witnessed #uint8 #(size 32) x (Lib.Sequence.of_list p256_inverse_list) /\ recallable x} = 
  createL_global p256_inverse_list

inline_for_extraction
let prime384_inverse_buffer: x: glbuffer uint8 48ul
  {witnessed #uint8 #(size 48) x (Lib.Sequence.of_list p384_inverse_list) /\ recallable x} = 
  createL_global p384_inverse_list


inline_for_extraction
let prime_inverse_buffer (#c: curve): (x: glbuffer uint8 (getCoordinateLenU c)
  {witnessed #uint8 #(getCoordinateLenU c) x (Lib.Sequence.of_list (prime_inverse_list c)) /\ recallable x}) = 
    match c with
  | P256 -> prime256_inverse_buffer
  | P384 -> prime384_inverse_buffer
  | _ -> admit(); prime256_inverse_buffer
  

val getK0: c: curve -> Stack (r: uint64 {v r = min_one_prime (pow2 64) (- getPrime c)})
  (requires fun h -> True)
  (ensures fun h0 r h1 -> modifies0 h0 h1 /\
    r == Hacl.Spec.Bignum.ModInv64.mod_inv_u64 (getLastWordPrime #c))

let getK0 c = 
  match c with 
  |P256 -> Hacl.Spec.Bignum.ModInv64.mod_inv_u64_lemma (getLastWordPrime #P256); (u64 1)
  |P384 -> Hacl.Spec.Bignum.ModInv64.mod_inv_u64_lemma (getLastWordPrime #P384); (u64 4294967297)
  |Default -> Hacl.Bignum.ModInv64.mod_inv_u64 (getLastWordPrime #c)


inline_for_extraction noextract
let sqPower_list_p256: x: list uint8 {List.Tot.length x == v (getScalarLenBytes P256) /\ 
  lst_as_nat x == (getPrime P256 - 1) / 4}  =
  [@inline_let]
  let x = [
    u8 0;  u8 0;  u8 0;  u8 0;   u8 0;   u8 0;   u8 0;   u8 0;
    u8 0;  u8 0;  u8 0;  u8 64;  u8 0;   u8 0;   u8 0;   u8 0;
    u8 0;  u8 0;  u8 0;  u8 0;   u8 0;   u8 0;   u8 0;   u8 64;
    u8 0;  u8 0;  u8 0;  u8 192; u8 255; u8 255; u8 255; u8 63] in 
  assert_norm (List.Tot.length x == v (getScalarLenBytes P256));
  admit();
  x


inline_for_extraction noextract
let sqPower_list_p384: x: list uint8 {List.Tot.length x == v (getScalarLenBytes P384) /\ 
  lst_as_nat x == (getPrime P384 - 1) / 4} =
  [@inline_let]
  let x = [
    u8 0;   u8 0;   u8 0;   u8 64;  u8 0;   u8 0;   u8 0;   u8 0; 
    u8 0;   u8 0;   u8 0;   u8 192; u8 255; u8 255; u8 255; u8 191;
    u8 255; u8 255; u8 255; u8 255; u8 255; u8 255; u8 255; u8 255; 
    u8 255; u8 255; u8 255; u8 255; u8 255; u8 255; u8 255; u8 255; 
    u8 255; u8 255; u8 255; u8 255; u8 255; u8 255; u8 255; u8 255;
    u8 255; u8 255; u8 255; u8 255; u8 255; u8 255; u8 255; u8 63] in 
  assert_norm (List.Tot.length x == v (getScalarLenBytes P384));
  admit();
  x


inline_for_extraction noextract
let sqPower_list (#c: curve) : x: list uint8 {List.Tot.length x == v (getScalarLenBytes c) /\ 
  lst_as_nat x == (getPrime c - 1) / 4} = 
  match c with 
  |P256 -> sqPower_list_p256
  |P384 -> sqPower_list_p384
  |_ -> admit(); []


inline_for_extraction
let sqPower_buffer_p256 : x: glbuffer uint8 (getScalarLenBytes P256) {witnessed x (Lib.Sequence.of_list (sqPower_list #P256))
  /\ recallable x} = 
  createL_global sqPower_list_p256


inline_for_extraction
let sqPower_buffer_p384 : x: glbuffer uint8 (getScalarLenBytes P384) {witnessed x (Lib.Sequence.of_list (sqPower_list #P384)) /\ recallable x} = 
  createL_global sqPower_list_p384

(* https://www.rieselprime.de/ziki/Modular_square_root *)
inline_for_extraction
let sqPower_buffer (#c: curve): x: glbuffer uint8 (getScalarLenBytes c) {witnessed x (Lib.Sequence.of_list (sqPower_list #c)) /\
  recallable x} = 
  match c with 
  |P256 -> sqPower_buffer_p256
  |P384 -> sqPower_buffer_p384
  |_ -> admit(); sqPower_buffer_p256

