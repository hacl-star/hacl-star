module Hacl.Spec.P256.Bignum

open FStar.Mul

open Lib.IntTypes
open Lib.Sequence

module BD = Hacl.Spec.Bignum.Definitions

#set-options "--z3rlimit 30 --fuel 0 --ifuel 0"

inline_for_extraction
let felem4 = tuple4 uint64 uint64 uint64 uint64
inline_for_extraction
let felem8 = tuple8 uint64 uint64 uint64 uint64 uint64 uint64 uint64 uint64

val as_nat4: f:felem4 -> Tot nat
let as_nat4 f =
  let (s0, s1, s2, s3) = f in
  v s0 + v s1 * pow2 64 + v s2 * pow2 64 * pow2 64 +
  v s3 * pow2 64 * pow2 64 * pow2 64

val wide_as_nat4: f:felem8 -> Tot nat
let wide_as_nat4 f =
  let (s0, s1, s2, s3, s4, s5, s6, s7) = f in
  v s0 + v s1 * pow2 64 + v s2 * pow2 64 * pow2 64 +
  v s3 * pow2 64 * pow2 64 * pow2 64 +
  v s4 * pow2 64 * pow2 64 * pow2 64 * pow2 64 +
  v s5 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 +
  v s6 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 +
  v s7 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64


inline_for_extraction
let felem_seq = lseq uint64 4
inline_for_extraction
let widefelem_seq = lseq uint64 8

let as_felem4 (a:felem_seq) : felem4 = 
  (a.[0], a.[1], a.[2], a.[3])

let as_felem8 (a:widefelem_seq) : felem8 = 
  (a.[0], a.[1], a.[2], a.[3], a.[4], a.[5], a.[6], a.[7])

unfold
let felem_seq_as_nat (a:lseq uint64 4) : nat = as_nat4 (as_felem4 a)
unfold
let widefelem_seq_as_nat (a:lseq uint64 8) : nat = wide_as_nat4 (as_felem8 a)


val bn_v_is_as_nat: a:felem_seq -> Lemma (BD.bn_v a == felem_seq_as_nat a)
let bn_v_is_as_nat a =
  let open Hacl.Spec.Bignum.Definitions in
  assert_norm (pow2 64 * pow2 64 = pow2 128);
  assert_norm (pow2 64 * pow2 64 * pow2 64 = pow2 192);

  calc (==) {
    bn_v a;
  (==) {bn_eval1 (slice a 0 1); bn_eval_split_i #U64 a 1}
    v a.[0] + pow2 64 * bn_v (slice a 1 4);
  (==) {bn_eval_split_i #U64 (slice a 1 4) 1; bn_eval1 (slice a 1 2)}
    v a.[0] + pow2 64 * v a.[1] + pow2 64 * pow2 64 * bn_v (slice a 2 4);
  (==) {bn_eval_split_i #U64 (slice a 2 4) 1; bn_eval1 (slice a 2 3)}
    v a.[0] + pow2 64 * v a.[1] + pow2 64 * pow2 64 * v a.[2]
    + pow2 64 * pow2 64 * pow2 64 * bn_v (slice a 3 4);
  (==) {bn_eval1 (slice a 3 4)}
    v a.[0] + pow2 64 * v a.[1] + pow2 64 * pow2 64 * v a.[2]
    + pow2 64 * pow2 64 * pow2 64 * v a.[3];
  }


// local function
val lemma_powers: unit -> Lemma (
  pow2 64 * pow2 64 * pow2 64 = pow2 (3 * 64) /\
  pow2 64 * pow2 64 * pow2 64 * pow2 64 = pow2 (4 * 64) /\
  pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 = pow2 (5 * 64) /\
  pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 = pow2 (6 * 64) /\
  pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 = pow2 (7 * 64) /\
  pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 = pow2 (8 * 64))

let lemma_powers () =
  assert_norm (pow2 64 * pow2 64 * pow2 64 = pow2 (3 * 64));
  assert_norm (pow2 64 * pow2 64 * pow2 64 * pow2 64 = pow2 (4 * 64));
  assert_norm (pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 = pow2 (5 * 64));
  assert_norm (pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 = pow2 (6 * 64));
  assert_norm (pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 = pow2 (7 * 64));
  assert_norm (pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 = pow2 (8 * 64))


// local function
val wide_as_nat_is_as_nat: a:widefelem_seq ->
  Lemma (widefelem_seq_as_nat a ==
    felem_seq_as_nat (sub a 0 4) + pow2 (64 * 4) * felem_seq_as_nat (sub a 4 4))

let wide_as_nat_is_as_nat a =
  lemma_powers ()


val bn_v_is_wide_as_nat: a:widefelem_seq -> Lemma (BD.bn_v a == widefelem_seq_as_nat a)
let bn_v_is_wide_as_nat a =
  wide_as_nat_is_as_nat a;
  bn_v_is_as_nat (sub a 0 4);
  bn_v_is_as_nat (sub a 4 4);
  BD.bn_eval_split_i a 4


val as_nat_bound: f:felem_seq -> Lemma (felem_seq_as_nat f < pow2 256)
let as_nat_bound f =
  bn_v_is_as_nat f;
  BD.bn_eval_bound f 4
