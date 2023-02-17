module Spec.P256.Constants

open FStar.Mul

open Lib.IntTypes
open Lib.Sequence


#set-options "--z3rlimit 30 --fuel 0 --ifuel 0"

let prime256: (a: pos {a > 3 && a < pow2 256}) =
  assert_norm (pow2 256 - pow2 224 + pow2 192 + pow2 96 -1 > 3);
  assert_norm (pow2 256 - pow2 224 + pow2 192 + pow2 96 -1 < pow2 256);
  pow2 256 - pow2 224 + pow2 192 + pow2 96 -1

let point_nat = tuple3 nat nat nat
let point_nat_prime = (p:point_nat{let (a, b, c) = p in a < prime256 /\ b < prime256 /\ c < prime256})
let nat_prime = n:nat{n < prime256}


let prime_p256_order: (a: pos{a < pow2 256}) =
  assert_norm (115792089210356248762697446949407573529996955224135760342422259061068512044369 < pow2 256);
  115792089210356248762697446949407573529996955224135760342422259061068512044369


// TODO: fix me; mv to code/
let felem_seq = lseq uint64 4

#push-options "--fuel 5 --ifuel 5"
inline_for_extraction
let p256_prime_list : x:list uint64{List.Tot.length x == 4 /\
  (
    let l0 = uint_v (List.Tot.index x 0) in
    let l1 = uint_v (List.Tot.index x 1) in
    let l2 = uint_v (List.Tot.index x 2) in
    let l3 = uint_v (List.Tot.index x 3) in
    l0 + l1 * pow2 64 + l2 * pow2 128 + l3 * pow2 192 == prime256)
  } =
  [@inline_let]
  let x =
    [ u64 0xffffffffffffffff; u64 0xffffffff; u64 0; u64 0xffffffff00000001] in
    assert_norm (0xffffffffffffffff + 0xffffffff * pow2 64 + 0xffffffff00000001 * pow2 192 == prime256);
  x


inline_for_extraction
let p256_order_prime_list : x:list uint64{List.Tot.length x == 4 /\
  (
    let l0 = uint_v (List.Tot.index x 0) in
    let l1 = uint_v (List.Tot.index x 1) in
    let l2 = uint_v (List.Tot.index x 2) in
    let l3 = uint_v (List.Tot.index x 3) in
    l0 + l1 * pow2 64 + l2 * pow2 128 + l3 * pow2 192 == prime_p256_order)
  } =
  [@inline_let]
  let x =
    [ u64 17562291160714782033; u64 13611842547513532036; u64 18446744073709551615; u64 18446744069414584320 ] in
    assert_norm (17562291160714782033 + 13611842547513532036 * pow2 64 + 18446744073709551615* pow2 128 + 18446744069414584320 * pow2 192 == prime_p256_order);
  x
#pop-options
