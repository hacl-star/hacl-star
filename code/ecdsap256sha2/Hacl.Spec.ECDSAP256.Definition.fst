module Hacl.Spec.ECDSAP256.Definition

open Lib.IntTypes
open FStar.Math.Lemmas
open FStar.Math.Lib

open FStar.HyperStack
open FStar.HyperStack.All
open Lib.Sequence
open Lib.Buffer
open FStar.Mul

noextract
let prime_p256_order: (a: pos{a < pow2 256}) =
  assert_norm (115792089210356248762697446949407573529996955224135760342422259061068512044369> 0);
  assert_norm (115792089210356248762697446949407573529996955224135760342422259061068512044369 < pow2 256);
  115792089210356248762697446949407573529996955224135760342422259061068512044369

inline_for_extraction noextract
let p256_order_prime_list : x:list uint64{List.Tot.length x == 4 /\ 
  (
    let open FStar.Mul in 
    let l0 = uint_v (List.Tot.index x 0) in 
    let l1 = uint_v (List.Tot.index x 1) in 
    let l2 = uint_v (List.Tot.index x 2) in 
    let l3 = uint_v (List.Tot.index x 3) in 
    l0 + l1 * pow2 64 + l2 * pow2 128 + l3 * pow2 192 == prime_p256_order)
  } =
  let open FStar.Mul in 
  [@inline_let]
  let x =
    [ (u64 17562291160714782033);  (u64 13611842547513532036); (u64 18446744073709551615);  (u64 18446744069414584320);] in
    assert_norm(17562291160714782033 + 13611842547513532036 * pow2 64 + 18446744073709551615* pow2 128 + 18446744069414584320 * pow2 192 == prime_p256_order);
  x  

inline_for_extraction
let felem = lbuffer uint64 (size 4)
inline_for_extraction 
let widefelem = lbuffer uint64 (size 8)


inline_for_extraction noextract
let felem4 = tuple4 uint64 uint64 uint64 uint64
inline_for_extraction noextract
let felem8 = tuple8 uint64 uint64 uint64 uint64 uint64 uint64 uint64 uint64

noextract
val as_nat4: f:felem4 -> GTot nat
let as_nat4 f =
  let (s0, s1, s2, s3) = f in
  v s0 + v s1 * pow2 64 + v s2 * pow2 64 * pow2 64 +
  v s3 * pow2 64 * pow2 64 * pow2 64


noextract
val wide_as_nat4: f:felem8 -> GTot nat
let wide_as_nat4 f =
  let (s0, s1, s2, s3, s4, s5, s6, s7) = f in
  v s0 + v s1 * pow2 64 + v s2 * pow2 64 * pow2 64 +
  v s3 * pow2 64 * pow2 64 * pow2 64 +
  v s4 * pow2 64 * pow2 64 * pow2 64 * pow2 64 +
  v s5 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 +
  v s6 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 +
  v s7 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64



noextract
let as_nat (h:mem) (e:felem) : GTot nat =
  let s = as_seq h e in
  let s0 = s.[0] in
  let s1 = s.[1] in
  let s2 = s.[2] in
  let s3 = s.[3] in
  as_nat4 (s0, s1, s2, s3)


noextract
let wide_as_nat (h:mem) (e:widefelem) : GTot nat =
  let s = as_seq h e in
  let s0 = s.[0] in
  let s1 = s.[1] in
  let s2 = s.[2] in
  let s3 = s.[3] in
  let s4 = s.[4] in
  let s5 = s.[5] in
  let s6 = s.[6] in
  let s7 = s.[7] in
  wide_as_nat4 (s0, s1, s2, s3, s4, s5, s6, s7)

noextract
let felem_seq_as_nat_8 (a: lseq uint64 8) : Tot nat = 
  let open FStar.Mul in 
  let a0 = Lib.Sequence.index a 0 in 
  let a1 = Lib.Sequence.index a 1 in 
  let a2 = Lib.Sequence.index a 2 in 
  let a3 = Lib.Sequence.index a 3 in 
  let a4 = Lib.Sequence.index a 4 in 
  let a5 = Lib.Sequence.index a 5 in 
  let a6 = Lib.Sequence.index a 6 in 
  let a7 = Lib.Sequence.index a 7 in
  uint_v a0 + 
  uint_v a1 * pow2 64 + 
  uint_v a2 * pow2 64 * pow2 64 + 
  uint_v a3 * pow2 64 * pow2 64 * pow2 64 + 
  uint_v a4 * pow2 64 * pow2 64 * pow2 64 * pow2 64 + 
  uint_v a5 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 + 
  uint_v a6 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 + 
  uint_v a7 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64

noextract
let felem_seq = lseq uint64 4

noextract
let felem_seq_as_nat (a: felem_seq) : Tot (n: nat {n < pow2 256})  = 
  let open FStar.Mul in 
  let a0 = Lib.Sequence.index a 0 in 
  let a1 =  Lib.Sequence.index a 1 in 
  let a2 =  Lib.Sequence.index  a 2 in 
  let a3 =  Lib.Sequence.index a 3 in 
  assert_norm( uint_v a0 + uint_v a1 * pow2 64 + uint_v a2 * pow2 64 * pow2 64 + uint_v a3 * pow2 64 * pow2 64 * pow2 64 < pow2 256);
  uint_v a0 + uint_v a1 * pow2 64 + uint_v a2 * pow2 64 * pow2 64 + uint_v a3 * pow2 64 * pow2 64 * pow2 64

noextract 
let nat_as_seq (a: nat { a < pow2 256}) : lseq uint64 4 = 
  let a0 = a % pow2 64 in 
  let a1 = (arithmetic_shift_right a 64) % pow2 64 in 
  let a2 = (arithmetic_shift_right a 128) % pow2 64 in 
  let a3 = (arithmetic_shift_right a 192) % pow2 64 in 
  let s = Lib.Sequence.create 4 (u64 0) in 
  let s = Lib.Sequence.upd s 0 (u64 a0) in 
  let s = Lib.Sequence.upd s 1 (u64 a1) in 
  let s = Lib.Sequence.upd s 2 (u64 a2) in 
  Lib.Sequence.upd s 3 (u64 a3)

#reset-options "--z3refresh --z3rlimit 200"

val lemma1: a0: uint64 -> a1: uint64 -> a2: uint64 -> a3: uint64 -> Lemma (arithmetic_shift_right (uint_v a0 + uint_v a1 * pow2 64 + uint_v a2 * pow2 64 * pow2 64 + uint_v a3 * pow2 64 * pow2 64 * pow2 64) 192 ==  uint_v a3)

let lemma1 a0 a1 a2 a3 = 
  assert_norm (pow2 64 * pow2 64 * pow2 64 = pow2 192)


val lemma2: a0: uint64 -> a1: uint64 -> a2: uint64 -> a3: uint64 -> Lemma
    (
      let k_s = uint_v a0 + uint_v a1 * pow2 64 + uint_v a2 * pow2 64 * pow2 64 + uint_v a3 * pow2 64 * pow2 64 * pow2 64 in
      let k0 = k_s % pow2 64 in
      let k1 = (arithmetic_shift_right k_s 64) % pow2 64 in 
      let k2 = (arithmetic_shift_right k_s 128) % pow2 64 in 
      let k3 = (arithmetic_shift_right k_s 192) % pow2 64 in
      k0 == uint_v a0 /\ k1 == uint_v a1 /\ k2 == uint_v a2 /\k3 == uint_v a3)

let lemma2 a0 a1 a2 a3 = 
  let k_s = uint_v a0 + uint_v a1 * pow2 64 + uint_v a2 * pow2 64 * pow2 64 + uint_v a3 * pow2 64 * pow2 64 * pow2 64 in

  let k0 = k_s % pow2 64 in
  let k1 = (arithmetic_shift_right k_s 64) % pow2 64 in 
  let k2 = (arithmetic_shift_right k_s 128) % pow2 64 in 
  let k3 = (arithmetic_shift_right k_s 192) % pow2 64 in 

  assert(k1 == (arithmetic_shift_right (uint_v a0 + uint_v a1 * pow2 64 + uint_v a2 * pow2 64 * pow2 64 + uint_v a3 * pow2 64 * pow2 64 * pow2 64) 64) % pow2 64);
  assert(arithmetic_shift_right (uint_v a0 + uint_v a1 * pow2 64 + uint_v a2 * pow2 64 * pow2 64 + uint_v a3 * pow2 64 * pow2 64 * pow2 64) 64 = uint_v a1 + uint_v a2 * pow2 64 + uint_v a3 * pow2 64 * pow2 64);
  assert((arithmetic_shift_right (uint_v a0 + uint_v a1 * pow2 64 + uint_v a2 * pow2 64 * pow2 64 + uint_v a3 * pow2 64 * pow2 64 * pow2 64) 64) % pow2 64 = uint_v a1); 

  assert(k1 == uint_v a1);

  assert(arithmetic_shift_right (uint_v a0 + uint_v a1 * pow2 64 + uint_v a2 * pow2 64 * pow2 64 + uint_v a3 * pow2 64 * pow2 64 * pow2 64) 128 = uint_v a2  + uint_v a3 * pow2 64 );

  assert(k2 == uint_v a2); 

  lemma1 a0 a1 a2 a3;
    assert(arithmetic_shift_right (uint_v a0 + uint_v a1 * pow2 64 + uint_v a2 * pow2 64 * pow2 64 + uint_v a3 * pow2 64 * pow2 64 * pow2 64) 192 ==  uint_v a3);
    assert(k3 == uint_v a3);
    assert(k0 == uint_v a0)


val lemmaSeq2Nat: k: felem_seq -> Lemma(nat_as_seq(felem_seq_as_nat k) == k)

let lemmaSeq2Nat k =  
  let a0 = Lib.Sequence.index k 0 in 
  let a1 = Lib.Sequence.index k 1 in 
  let a2 = Lib.Sequence.index k 2 in 
  let a3 = Lib.Sequence.index k 3 in 
  let k_s = uint_v a0 + uint_v a1 * pow2 64 + uint_v a2 * pow2 64 * pow2 64 + uint_v a3 * pow2 64 * pow2 64 * pow2 64 in

  let k0 = k_s % pow2 64 in
  let k1 = (arithmetic_shift_right k_s 64) % pow2 64 in 
  let k2 = (arithmetic_shift_right k_s 128) % pow2 64 in 
  let k3 = (arithmetic_shift_right k_s 192) % pow2 64 in 

  lemma2 a0 a1 a2 a3;

  let s = Lib.Sequence.create 4 (u64 0) in 
  let s = Lib.Sequence.upd s 0 (u64 k0) in 
  let s = Lib.Sequence.upd s 1 (u64 k1) in 
  let s = Lib.Sequence.upd s 2 (u64 k2) in 
  let s = Lib.Sequence.upd s 3 (u64 k3) in 

  assert(Lib.Sequence.index s 0 ==  a0);
  assert(Lib.Sequence.index s 1 ==  a1);
  assert(Lib.Sequence.index s 2 ==  a2);
  assert(Lib.Sequence.index s 3 ==  a3);

  assert(Lib.Sequence.equal s k)


