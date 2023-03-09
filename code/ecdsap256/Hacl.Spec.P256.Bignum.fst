module Hacl.Spec.P256.Bignum

open FStar.Mul
open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer
open Lib.Sequence

module BSeq = Lib.ByteSequence
module LSeq = Lib.Sequence
module BD = Hacl.Spec.Bignum.Definitions

#set-options "--z3rlimit 30 --fuel 0 --ifuel 0"

// TODO: rm `h:mem` from lemmas

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


let felem_seq_as_nat (a:lseq uint64 4) : Tot nat =
  as_nat4 (a.[0], a.[1], a.[2], a.[3])

let felem_wide_seq_as_nat (a:lseq uint64 8) : Tot nat =
  wide_as_nat4 (a.[0], a.[1], a.[2], a.[3], a.[4], a.[5], a.[6], a.[7])


inline_for_extraction
let felem = lbuffer uint64 (size 4)
inline_for_extraction
let widefelem = lbuffer uint64 (size 8)

let as_nat (h:mem) (e:felem) : GTot nat =
  let s = as_seq h e in
  as_nat4 (s.[0], s.[1], s.[2], s.[3])


let as_nat_il (h:mem) (e:glbuffer uint64 (size 4)) : GTot nat =
  let s = as_seq h e in
  as_nat4 (s.[0], s.[1], s.[2], s.[3])


let wide_as_nat (h:mem) (e:widefelem) : GTot nat =
  let s = as_seq h e in
  wide_as_nat4 (s.[0], s.[1], s.[2], s.[3], s.[4], s.[5], s.[6], s.[7])


// TODO: rename
val lemma_core_0: a:lbuffer uint64 (size 4) -> h:mem ->
  Lemma (BSeq.nat_from_intseq_le (as_seq h a) == as_nat h a)

let lemma_core_0 a h =
  let k = as_seq h a in
  let z = BSeq.nat_from_intseq_le k in
    BSeq.nat_from_intseq_le_slice_lemma k 1;
    BSeq.nat_from_intseq_le_lemma0 (Seq.slice k 0 1);
  let k1 = Seq.slice k 1 4 in
    BSeq.nat_from_intseq_le_slice_lemma #_ #_ #3 k1 1;
    BSeq.nat_from_intseq_le_lemma0 (Seq.slice k1 0 1);
  let k2 = Seq.slice k1 1 3 in
    BSeq.nat_from_intseq_le_slice_lemma #_ #_ #2 k2 1;
    BSeq.nat_from_intseq_le_lemma0 (Seq.slice k2 0 1);
    BSeq.nat_from_intseq_le_lemma0 (Seq.slice k2 1 2)


val bignum_bn_v_is_as_nat: h:mem -> a:felem ->
  Lemma (BD.bn_v (as_seq h a) == as_nat h a)

let bignum_bn_v_is_as_nat h a =
  let a = as_seq h a in
  let open Hacl.Spec.Bignum.Definitions in
  assert_norm (pow2 64 * pow2 64 = pow2 128);
  assert_norm (pow2 64 * pow2 64 * pow2 64 = pow2 192);

  calc (==) {
    bn_v a;
  (==) {bn_eval1 (LSeq.slice a 0 1); bn_eval_split_i #U64 a 1}
     v (LSeq.index a 0) + pow2 64 * bn_v (LSeq.slice a 1 4);
  (==) {bn_eval_split_i #U64 (LSeq.slice a 1 4) 1; bn_eval1 (LSeq.slice a 1 2)}
    v (LSeq.index a 0)
    + pow2 64 * v (LSeq.index a 1)
    + pow2 64 * pow2 64 * bn_v (LSeq.slice a 2 4);
  (==) {bn_eval_split_i #U64 (LSeq.slice a 2 4) 1; bn_eval1 (LSeq.slice a 2 3)}
      v (LSeq.index a 0)
    + pow2 64 * v (LSeq.index a 1)
    + pow2 64 * pow2 64 * v (LSeq.index a 2)
    + pow2 64 * pow2 64 * pow2 64 * bn_v (LSeq.slice a 3 4);
  (==) {bn_eval1 (LSeq.slice a 3 4)}
       v (LSeq.index a 0)
    + pow2 64 * v (LSeq.index a 1)
    + pow2 64 * pow2 64 * v (LSeq.index a 2)
    + pow2 64 * pow2 64 * pow2 64 * v (LSeq.index a 3);
  }


// local function
val lemma_powers: unit -> Lemma (
  pow2 64 * pow2 64 * pow2 64 = pow2 (3 * 64) /\
  pow2 64 * pow2 64 * pow2 64 * pow2 64 = pow2 (4 * 64) /\
  pow2 64 * pow2 64 * pow2 64  * pow2 64 * pow2 64 = pow2 (5 * 64) /\
  pow2 64 * pow2 64 * pow2 64  * pow2 64 * pow2 64 * pow2 64 = pow2 (6 * 64) /\
  pow2 64 * pow2 64 * pow2 64  * pow2 64 * pow2 64* pow2 64 * pow2 64 = pow2 (7 * 64) /\
  pow2 64 * pow2 64 * pow2 64  * pow2 64 * pow2 64* pow2 64 * pow2 64 * pow2 64 = pow2 (8 * 64))

let lemma_powers () =
   assert_norm(pow2 64 * pow2 64 * pow2 64 = pow2 (3 * 64));
   assert_norm(pow2 64 * pow2 64 * pow2 64 * pow2 64 = pow2 (4 * 64));
   assert_norm(pow2 64 * pow2 64 * pow2 64  * pow2 64 * pow2 64 = pow2 (5 * 64));
   assert_norm(pow2 64 * pow2 64 * pow2 64  * pow2 64 * pow2 64 * pow2 64 = pow2 (6 * 64));
   assert_norm(pow2 64 * pow2 64 * pow2 64  * pow2 64 * pow2 64* pow2 64 * pow2 64 = pow2 (7 * 64));
   assert_norm(pow2 64 * pow2 64 * pow2 64  * pow2 64 * pow2 64* pow2 64 * pow2 64 * pow2 64 = pow2 (8 * 64))


// local function
val wide_as_nat_is_as_nat: h:mem -> a:widefelem ->
  Lemma (wide_as_nat h a == as_nat h (gsub a (size 0) (size 4)) + pow2 (64 * 4) * as_nat h (gsub a (size 4) (size 4)))

let wide_as_nat_is_as_nat h a =
  lemma_powers ()


val bignum_bn_v_is_wide_as_nat: h:mem -> a:widefelem ->
  Lemma (BD.bn_v (as_seq h a) == wide_as_nat h a)

let bignum_bn_v_is_wide_as_nat h a =
  wide_as_nat_is_as_nat h a;
  bignum_bn_v_is_as_nat h (gsub a (size 0) (size 4));
  bignum_bn_v_is_as_nat h (gsub a (size 4) (size 4));
  BD.bn_eval_split_i (as_seq h a) 4


val as_nat_bound: h:mem -> f:felem -> Lemma (as_nat h f < pow2 256)
let as_nat_bound h f =
  bignum_bn_v_is_as_nat h f;
  BD.bn_eval_bound (as_seq h f) 4
