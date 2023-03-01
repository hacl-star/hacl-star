module Hacl.Impl.P256.Constants

open FStar.Mul
open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer

open Hacl.Spec.P256.Felem
open Hacl.Impl.P256.Bignum

module S = Spec.P256
module LSeq = Lib.Sequence
module SM = Hacl.Spec.P256.MontgomeryMultiplication

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

inline_for_extraction noextract
val make_prime: n:felem -> Stack unit
  (requires fun h -> live h n)
  (ensures  fun h0 _ h1 -> modifies (loc n) h0 h1 /\
    as_nat h1 n == S.prime)

let make_prime n =
  // 0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff
  [@inline_let] let n0 = u64 0xffffffffffffffff in
  [@inline_let] let n1 = u64 0xffffffff in
  [@inline_let] let n2 = u64 0x0 in
  [@inline_let] let n3 = u64 0xffffffff00000001 in
  assert_norm (v n0 + v n1 * pow2 64 + v n2 * pow2 128 + v n3 * pow2 192 = S.prime);
  bn_make_u64_4 n0 n1 n2 n3 n


inline_for_extraction noextract
val make_order: n:felem -> Stack unit
  (requires fun h -> live h n)
  (ensures  fun h0 _ h1 -> modifies (loc n) h0 h1 /\
    as_nat h1 n == S.order)

let make_order n =
  // 0xffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551
  [@inline_let] let n0 = u64 0xf3b9cac2fc632551 in
  [@inline_let] let n1 = u64 0xbce6faada7179e84 in
  [@inline_let] let n2 = u64 0xffffffffffffffff in
  [@inline_let] let n3 = u64 0xffffffff00000000 in
  assert_norm (v n0 + v n1 * pow2 64 + v n2 * pow2 128 + v n3 * pow2 192 = S.order);
  bn_make_u64_4 n0 n1 n2 n3 n


inline_for_extraction noextract
val make_a_coeff: a:felem -> Stack unit
  (requires fun h -> live h a)
  (ensures fun h0 _ h1 -> modifies (loc a) h0 h1 /\
    as_nat h1 a == SM.toDomain_ S.a_coeff /\
    SM.fromDomain_ (as_nat h1 a) == S.a_coeff /\
    as_nat h1 a < S.prime)

let make_a_coeff a =
  // a_coeff      = 0xffffffff00000001000000000000000000000000fffffffffffffffffffffffc
  // a_coeff_mont = 0xfffffffc00000004000000000000000000000003fffffffffffffffffffffffc
  [@inline_let] let n0 = u64 0xfffffffffffffffc in
  [@inline_let] let n1 = u64 0x3ffffffff in
  [@inline_let] let n2 = u64 0x0 in
  [@inline_let] let n3 = u64 0xfffffffc00000004 in
  assert_norm (
    v n0 + v n1 * pow2 64 + v n2 * pow2 128 + v n3 * pow2 192 == SM.toDomain_ S.a_coeff);
  assert_norm (
    SM.fromDomain_ (v n0 + v n1 * pow2 64 + v n2 * pow2 128 + v n3 * pow2 192) == S.a_coeff);
  bn_make_u64_4 n0 n1 n2 n3 a


inline_for_extraction noextract
val make_b_coeff: b:felem -> Stack unit
  (requires fun h -> live h b)
  (ensures fun h0 _ h1 -> modifies (loc b) h0 h1 /\
    as_nat h1 b == SM.toDomain_ S.b_coeff /\
    SM.fromDomain_ (as_nat h1 b) == S.b_coeff /\
    as_nat h1 b < S.prime)

let make_b_coeff b =
  // b_coeff      = 0x5ac635d8aa3a93e7b3ebbd55769886bc651d06b0cc53b0f63bce3c3e27d2604b
  // b_coeff_mont = 0xdc30061d04874834e5a220abf7212ed6acf005cd78843090d89cdf6229c4bddf
  [@inline_let] let n0 = u64 0xd89cdf6229c4bddf in
  [@inline_let] let n1 = u64 0xacf005cd78843090 in
  [@inline_let] let n2 = u64 0xe5a220abf7212ed6 in
  [@inline_let] let n3 = u64 0xdc30061d04874834 in
  assert_norm (
    v n0 + v n1 * pow2 64 + v n2 * pow2 128 + v n3 * pow2 192 == SM.toDomain_ S.b_coeff);
  assert_norm (
    SM.fromDomain_ (v n0 + v n1 * pow2 64 + v n2 * pow2 128 + v n3 * pow2 192) == S.b_coeff);
  bn_make_u64_4 n0 n1 n2 n3 b


//----------------

inline_for_extraction noextract
let p256_prime_list : x:list uint64{List.Tot.length x == 4 /\
  (
    let l0 = uint_v (List.Tot.index x 0) in
    let l1 = uint_v (List.Tot.index x 1) in
    let l2 = uint_v (List.Tot.index x 2) in
    let l3 = uint_v (List.Tot.index x 3) in
    l0 + l1 * pow2 64 + l2 * pow2 128 + l3 * pow2 192 == S.prime)
  } =
  [@inline_let]
  let x =
    [ u64 0xffffffffffffffff; u64 0xffffffff; u64 0; u64 0xffffffff00000001] in
    assert_norm (0xffffffffffffffff + 0xffffffff * pow2 64 + 0xffffffff00000001 * pow2 192 == S.prime);
  x


inline_for_extraction noextract
let p256_order_prime_list : x:list uint64{List.Tot.length x == 4 /\
  (
    let l0 = uint_v (List.Tot.index x 0) in
    let l1 = uint_v (List.Tot.index x 1) in
    let l2 = uint_v (List.Tot.index x 2) in
    let l3 = uint_v (List.Tot.index x 3) in
    l0 + l1 * pow2 64 + l2 * pow2 128 + l3 * pow2 192 == S.order)
  } =
  [@inline_let]
  let x =
    [ u64 17562291160714782033; u64 13611842547513532036; u64 18446744073709551615; u64 18446744069414584320 ] in
    assert_norm (17562291160714782033 + 13611842547513532036 * pow2 64 + 18446744073709551615* pow2 128 + 18446744069414584320 * pow2 192 == S.order);
  x


let prime_buffer: x: glbuffer uint64 4ul {
  witnessed #uint64 #(size 4) x (LSeq.of_list p256_prime_list) /\
  recallable x /\
  felem_seq_as_nat (LSeq.of_list (p256_prime_list)) == S.prime} =

  assert_norm (felem_seq_as_nat (LSeq.of_list (p256_prime_list)) == S.prime);
  createL_global p256_prime_list


let primeorder_buffer: x: glbuffer uint64 (size 4) {
  witnessed #uint64 #(size 4) x (LSeq.of_list p256_order_prime_list) /\
  recallable x /\
  felem_seq_as_nat (LSeq.of_list (p256_order_prime_list)) == S.order} =
  createL_global p256_order_prime_list
