module Spec.P256.Definitions

open FStar.Mul
open FStar.Math.Lemmas
open FStar.Math.Lib

open Lib.IntTypes
open Lib.Sequence

#set-options "--z3rlimit 30"

let prime256: (a: pos {a > 3 && a < pow2 256}) =
  assert_norm (pow2 256 - pow2 224 + pow2 192 + pow2 96 -1 > 3);
  assert_norm (pow2 256 - pow2 224 + pow2 192 + pow2 96 -1 < pow2 256);
  pow2 256 - pow2 224 + pow2 192 + pow2 96 -1


inline_for_extraction
let p256_prime_list : x:list uint64{List.Tot.length x == 4 /\
  (
    let open FStar.Mul in
    let l0 = uint_v (List.Tot.index x 0) in
    let l1 = uint_v (List.Tot.index x 1) in
    let l2 = uint_v (List.Tot.index x 2) in
    let l3 = uint_v (List.Tot.index x 3) in
    l0 + l1 * pow2 64 + l2 * pow2 128 + l3 * pow2 192 == prime256)
  } =
  let open FStar.Mul in
  [@inline_let]
  let x =
    [ (u64 0xffffffffffffffff);  (u64 0xffffffff); (u64 0);  (u64 0xffffffff00000001);] in
    assert_norm(0xffffffffffffffff + 0xffffffff * pow2 64 + 0xffffffff00000001 * pow2 192 == prime256);
  x


let point_nat = tuple3 nat nat nat

let point_nat_prime = (p:point_nat{let (a, b, c) = p in a < prime256 /\ b < prime256 /\ c < prime256})

let nat_prime = n:nat{n < prime256}
