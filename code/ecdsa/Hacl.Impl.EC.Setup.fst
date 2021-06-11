module Hacl.Impl.EC.Setup

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer

open Hacl.Spec.EC.Definition
open Hacl.Spec.MontgomeryMultiplication
open Spec.ECC
open Spec.ECC.Curves
open FStar.Mul

noextract 
val lst_as_nat_: #t:inttype{unsigned t} -> a: list (uint_t t SEC) -> i: nat {i <= List.Tot.Base.length a} -> Tot nat

let rec lst_as_nat_ #t a i = 
  if i = 0 then 0 else
  let a_i_1 = List.Tot.Base.index a (i - 1) in
  lst_as_nat_ a (i - 1) + pow2 (bits t * (i - 1)) * v a_i_1


val lst_as_nat: #t:inttype{unsigned t} -> a: list (uint_t t SEC) -> Tot nat 

let lst_as_nat a = lst_as_nat_ a (List.Tot.Base.length a)


val lst_as_nat_0: #t:inttype{unsigned t} -> a: list (uint_t t SEC) -> Lemma (lst_as_nat_ a 0 = 0)

let lst_as_nat_0 a = ()


val lst_as_nat_definiton: #t:inttype{unsigned t} -> a: list (uint_t t SEC) -> i: nat {i > 0 /\ i <= List.Tot.Base.length a} ->
  Lemma (lst_as_nat_ a i == lst_as_nat_ a (i - 1) + pow2 (bits t * (i - 1)) * v (List.Tot.Base.index a (i - 1)))

let lst_as_nat_definiton b i = ()


val lst_as_nat_first: #t:inttype{unsigned t} -> a: list (uint_t t SEC)  {List.Tot.Base.length a > 0} -> Lemma (lst_as_nat_ a 1 == v (List.Tot.Base.index a 0))

let lseq_as_nat_first a = ()


#set-options "--z3rlimit 100"

val lemma_lst_1: a: list uint64 -> i: nat {i > 0 /\ i <= List.Tot.Base.length a} ->
  Lemma (lst_as_nat_ a i % pow2 64 == v (List.Tot.Base.index a 0))

let rec lemma_lst_1 a i = 
  match i with 
  |1 -> ()
  |_ -> lemma_lst_1 a (i - 1);
    lst_as_nat_definiton a i;
    FStar.Math.Lemmas.lemma_mod_add_distr (lst_as_nat_ a (i - 1)) (pow2 (64 * (i - 1)) * v (List.Tot.Base.index a (i - 1))) (pow2 64);
    FStar.Math.Lemmas.pow2_multiplication_modulo_lemma_1 (v (List.Tot.Base.index a (i - 1))) 64 (64 * (i - 1))  
val lemmaLstLastWord: a: list uint64 {List.Tot.Base.length a > 1} -> Lemma
  (v (List.Tot.Base.index a 0) == lst_as_nat a % pow2 64)

let lemmaLstLastWord a = lemma_lst_1 a (List.Tot.Base.length a)


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
  lst_as_nat_0 a


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
  lst_as_nat_0 a


(* This code contains the prime *)
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
  

open FStar.Math.Lemmas

inline_for_extraction
let getLastWordPrime (#c: curve) : (r: uint64 {uint_v r == getPrime c % pow2 64 /\ v r % 2 == 1}) = 
  assert(FStar.Math.Euclid.is_prime (getPrime c));
  assert(~(FStar.Math.Euclid.divides (getPrime c) 2));
  if (getPrime c) % 2 = 0 then 
    begin 
      FStar.Math.Euclid.mod_divides (getPrime c) 2;
      assert(False)
    end;
  assert_norm (pow2 1 == 2); 
  pow2_modulo_modulo_lemma_1 (getPrime c) 1 64; 

  match c with 
  |P256 -> 
    lemmaLstLastWord p256_prime_list;
    normalize_term (List.Tot.Base.index p256_prime_list 0)
  |P384 -> 
    lemmaLstLastWord p384_prime_list;
    normalize_term (List.Tot.Base.index p384_prime_list 0)
  |_ -> 1ul
  

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
let getLastWordOrder (#c: curve) : (r: uint64 {uint_v r == getOrder #c % pow2 64 /\ v r % 2 == 1}) = 
  match c with 
  |P256 -> 
    lemmaLstLastWord p256_prime_list;
    normalize_term (List.Tot.Base.index p256_order_list 0)
  |P384 -> 
    lemmaLstLastWord p384_prime_list;
    normalize_term (List.Tot.Base.index p384_order_list 0)
  |_ -> admit()


inline_for_extraction
let prime256order_buffer: x: glbuffer uint64 (getScalarLenWords P256) {witnessed #uint64 #(getScalarLenWords P256) x (Lib.Sequence.of_list p256_order_list) /\
  recallable x /\ lseq_as_nat (Lib.Sequence.of_list (order_list P256)) == getOrder #P256} = 
  createL_global p256_order_list


inline_for_extraction
let prime384order_buffer: x: glbuffer uint64 (size 6) {witnessed #uint64 #(size 6) x (Lib.Sequence.of_list p384_order_list) /\
  recallable x /\ lseq_as_nat (Lib.Sequence.of_list (order_list P384)) == getOrder #P384} = 
  createL_global p384_order_list


inline_for_extraction
let order_buffer (#c: curve): (x: glbuffer uint64 (getScalarLenWords c) {
  witnessed #uint64 #(getScalarLenWords c) x (Lib.Sequence.of_list (order_list c)) /\ recallable x /\ 
  lseq_as_nat (Lib.Sequence.of_list (order_list c)) == getOrder #c }) = 
  match c with
  | P256 -> prime256order_buffer
  | P384 -> prime384order_buffer
  | _ -> admit(); prime256order_buffer





(* Unfold? *)
inline_for_extraction noextract
let p256_inverse_list: x: list uint8 {List.Tot.length x == v (getCoordinateLenU P256) /\ lst_as_nat x == getPrime P256 - 2} = 
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
let p384_inverse_list: x: list uint8 {List.Tot.length x == v (getCoordinateLenU P384) /\ lst_as_nat x == getPrime P384 - 2} = 
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
let prime_inverse_list (c: curve) : x: list uint8 {List.Tot.length x == v (getCoordinateLenU c) /\ 
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
  

inline_for_extraction noextract
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
  lst_as_nat x == (getPrime P256 + 1) / 4} =
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
  lst_as_nat x == (getPrime P384 + 1) / 4} =
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


inline_for_extraction noextract
val upload_b_constant: #c: curve -> x: felem c -> Stack unit
  (requires fun h -> live h x)
  (ensures fun h0 _ h1 -> modifies (loc x) h0 h1 /\ as_nat c h1 x == toDomain_ #c #DH (bCoordinate #c) /\
    as_nat c h1 x < getPrime c)


let upload_b_constant #c x = 
  match c with 
  |P256 -> 
    upd x (size 0) (u64 15608596021259845087);
    upd x (size 1) (u64 12461466548982526096);
    upd x (size 2) (u64 16546823903870267094);
    upd x (size 3) (u64 15866188208926050356);
      let h1 = ST.get() in 
    Hacl.Impl.P256.LowLevel.lemma_lseq_nat_instant_4 (as_seq h1 x);
    Hacl.Spec.MontgomeryMultiplication.lemmaToDomain #P256 #DH (bCoordinate #P256);
    assert_norm (
      15608596021259845087 * pow2 (64 * 0) + 
      12461466548982526096 * pow2 64 + 
      16546823903870267094 * pow2 (64 * 2) + 
      15866188208926050356 * pow2 (64 * 3)  ==
      bCoordinate #P256 * pow2 256 % getPrime P256)
  |P384 -> 
    upd x (size 0) (u64 581395848458481100);
    upd x (size 1) (u64 17809957346689692396);
    upd x (size 2) (u64 8643006485390950958);
    upd x (size 3) (u64 16372638458395724514);
    upd x (size 4) (u64 13126622871277412500);
    upd x (size 5) (u64 14774077593024970745);
      let h1 = ST.get() in 
      Hacl.Impl.P384.LowLevel.lemma_lseq_nat_instant_6 (as_seq h1 x);
      Hacl.Spec.MontgomeryMultiplication.lemmaToDomain #P384 #DH (bCoordinate #P384);
    assert_norm (
      581395848458481100   * pow2 (64 * 0) + 
      17809957346689692396 * pow2 64 + 
      8643006485390950958  * pow2 (64 * 2) + 
      16372638458395724514 * pow2 (64 * 3) + 
      13126622871277412500 * pow2 (64 * 4) +
      14774077593024970745 * pow2 (64 * 5)
      == bCoordinate #P384 * pow2 384 % getPrime P384)
  | _ -> admit()

inline_for_extraction noextract
val uploadBasePoint: #c: curve -> p: point c -> Stack unit 
  (requires fun h -> live h p)
  (ensures fun h0 _ h1 -> 
    modifies (loc p) h0 h1 /\ point_eval c h1 p /\ 
    ~ (isPointAtInfinity (point_as_nat c h1 p)) /\ 
    basePoint #c == fromDomainPoint #c #DH (point_as_nat c h1 p))

let uploadBasePoint #c p = 
  match c with
  |P384 -> 
    let h0 = ST.get() in
    upd p (size 0) (u64 0x3dd0756649c0b528);
    upd p (size 1) (u64 0x20e378e2a0d6ce38);
    upd p (size 2) (u64 0x879c3afc541b4d6e);
    upd p (size 3) (u64 0x6454868459a30eff);
    upd p (size 4) (u64 0x812ff723614ede2b);
    upd p (size 5) (u64 0x4d3aadc2299e1513);


    upd p (size 6) (u64 0x23043dad4b03a4fe);
    upd p (size 7) (u64 0xa1bfa8bf7bb4a9ac);
    upd p (size 8) (u64 0x8bade7562e83b050);
    upd p (size 9) (u64 0xc6c3521968f4ffd9);
    upd p (size 10) (u64 0xdd8002263969a840);
    upd p (size 11) (u64 0x2b78abc25a15c5e9);

    upd p (size 12) (u64 0xffffffff00000001);
    upd p (size 13) (u64 0xffffffff);
    upd p (size 14) (u64 0x1);
    upd p (size 15) (u64 0);
    upd p (size 16) (u64 0);
    upd p (size 17) (u64 0);
    admit()



  |P256 -> 
    let h0 = ST.get() in 
  upd p (size 0) (u64 0x79e730d418a9143c);
  upd p (size 1) (u64 0x75ba95fc5fedb601);
  upd p (size 2) (u64 0x79fb732b77622510);
  upd p (size 3) (u64 0x18905f76a53755c6);
  
  upd p (size 4) (u64 0xddf25357ce95560a);
  upd p (size 5) (u64 0x8b4ab8e4ba19e45c);
  upd p (size 6) (u64 0xd2e88688dd21f325);
  upd p (size 7) (u64 0x8571ff1825885d85);
  
  upd p (size 8) (u64 0x1);
  upd p (size 9) (u64 0xffffffff00000000);
  upd p (size 10) (u64 0xffffffffffffffff);
  upd p (size 11) (u64 0xfffffffe);

  let h1 = ST.get() in 

  let x = gsub p (size 0) (size 4) in 
  let y = gsub p (size 4) (size 4) in 
  let z = gsub p (size 8) (size 4) in 
  
  Hacl.Impl.P256.LowLevel.lemma_lseq_nat_instant_4 (as_seq h1 x);
  Hacl.Impl.P256.LowLevel.lemma_lseq_nat_instant_4 (as_seq h1 y);
  Hacl.Impl.P256.LowLevel.lemma_lseq_nat_instant_4 (as_seq h1 z);
  lemmaFromDomain #c #DH (as_nat c h1 x); 
  lemmaFromDomain #c #DH (as_nat c h1 y); 
  lemmaFromDomain #c #DH (as_nat c h1 z); 

  let bX, bY, bZ = basePoint #c in 

  assert_norm (8784043285714375740 + pow2 64 * 8483257759279461889 + 
    pow2 (64 * 2) * 8789745728267363600 + 
    pow2 (64 * 3) * 1770019616739251654 = 11110593207902424140321080247206512405358633331993495164878354046817554469948); 
  assert_norm(bX == 11110593207902424140321080247206512405358633331993495164878354046817554469948 * modp_inv2_prime (pow2 256) prime256 % prime256);

  assert_norm(15992936863339206154 + pow2 64 * 10037038012062884956 + 
    pow2 (64 * 2) * 15197544864945402661 + 
    pow2 (64 * 3) * 9615747158586711429 = 60359023176204190920225817201443260813112970217682417638161152432929735267850);
  assert_norm(bY == 60359023176204190920225817201443260813112970217682417638161152432929735267850 * modp_inv2_prime (pow2 256) prime256 % prime256);

  
  assert_norm (1 + pow2 64 * 18446744069414584320 + 
    pow2 (64 * 2) * 18446744073709551615 + 
    pow2 (64 * 3) * 4294967294 == 26959946660873538059280334323183841250350249843923952699046031785985);
  assert_norm (bZ = 26959946660873538059280334323183841250350249843923952699046031785985 * modp_inv2_prime (pow2 256) prime256 % prime256);

  assert(fromDomain_ #c #DH (as_nat P256 h1 x) == bX); 
  assert(fromDomain_ #c #DH (as_nat P256 h1 y) == bY);
  assert(fromDomain_ #c #DH (as_nat P256 h1 z) == bZ);

  admit()
  |_ -> admit()


inline_for_extraction noextract
let order_u8_list (c: curve) : x: list uint8 {List.Tot.length x == v (getCoordinateLenU P256) /\ lst_as_nat x == getPrime P256 - 2} = 
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
let order_list_ (c: curve) : x: list uint8 {List.Tot.length x == v (getCoordinateLenU c) /\ 
  lst_as_nat x == getPrime c - 2} = 
  match c with 
  |P256 -> order_u8_list c
  |_ -> admit()


inline_for_extraction
let prime256_order_: x: glbuffer uint8 32ul {
  witnessed #uint8 #(size 32) x (Lib.Sequence.of_list p256_inverse_list) /\ recallable x} = 
  createL_global (order_u8_list P256)


inline_for_extraction
let order_u8_buffer (#c: curve): (x: glbuffer uint8 (getCoordinateLenU c)
  {witnessed #uint8 #(getCoordinateLenU c) x (Lib.Sequence.of_list (prime_inverse_list c)) /\ recallable x}) = 
  prime256_order_



inline_for_extraction noextract
val uploadA: #c: curve -> a: felem c -> Stack unit
  (requires fun h -> live h a)
  (ensures fun h0 _ h1 ->
    let prime = getPrime c in 
    modifies (loc a) h0 h1 /\ 
    as_nat c h1 a == toDomain_ #c #DH (aCoordinate #c % prime) /\
    as_nat c h1 a < prime
  )

let uploadA #c a = 
  match c with 
    |P256 -> 
      upd a (size 0) (u64 18446744073709551612);
      upd a (size 1) (u64 17179869183);
      upd a (size 2) (u64 0);
      upd a (size 3) (u64 18446744056529682436);
      
      let prime = getPrime c in 
      lemmaToDomain #c #DH (aCoordinate #c % prime);
      assert_norm(18446744073709551612 + 17179869183 * pow2 64 + 18446744056529682436 * pow2 64 * pow2 64 * pow2 64 = (aCoordinate #P256 % prime256) * pow2 256 % prime256)

    |P384 -> 
            upd a (size 0) (u64 18446744073709551612);
      upd a (size 1) (u64 17179869183);
      upd a (size 2) (u64 0);
      upd a (size 3) (u64 18446744056529682436);
      
      let prime = getPrime c in 
      lemmaToDomain #c #DH (aCoordinate #c % prime);
      assert_norm(18446744073709551612 + 17179869183 * pow2 64 + 18446744056529682436 * pow2 64 * pow2 64 * pow2 64 = (aCoordinate #P256 % prime256) * pow2 256 % prime256)
    |Default ->
      upd a (size 0) (u64 18446744073709551612);
      upd a (size 1) (u64 17179869183);
      upd a (size 2) (u64 0);
      upd a (size 3) (u64 18446744056529682436);
      
      let prime = getPrime c in 
      lemmaToDomain #c #DH (aCoordinate #c % prime);
      assert_norm(18446744073709551612 + 17179869183 * pow2 64 + 18446744056529682436 * pow2 64 * pow2 64 * pow2 64 = (aCoordinate #P256 % prime256) * pow2 256 % prime256)

