module Spec.ECDSAP256.Definition

open FStar.Mul
open FStar.Math.Lemmas
open FStar.Math.Lib

open Lib.IntTypes
open Lib.Sequence

#set-options "--z3rlimit 30"

let prime_p256_order: (a: pos{a < pow2 256}) =
  assert_norm (115792089210356248762697446949407573529996955224135760342422259061068512044369 < pow2 256);
  115792089210356248762697446949407573529996955224135760342422259061068512044369


inline_for_extraction
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


let felem_seq = lseq uint64 4


let felem_seq_as_nat (a: felem_seq) : Tot (n: nat {n < pow2 256})  =
  let open FStar.Mul in
  let a0 = Lib.Sequence.index a 0 in
  let a1 =  Lib.Sequence.index a 1 in
  let a2 =  Lib.Sequence.index  a 2 in
  let a3 =  Lib.Sequence.index a 3 in
  assert_norm( uint_v a0 + uint_v a1 * pow2 64 + uint_v a2 * pow2 64 * pow2 64 + uint_v a3 * pow2 64 * pow2 64 * pow2 64 < pow2 256);
  uint_v a0 + uint_v a1 * pow2 64 + uint_v a2 * pow2 64 * pow2 64 + uint_v a3 * pow2 64 * pow2 64 * pow2 64
