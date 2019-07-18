module Hacl.Impl.Ed25519.Field56

open FStar.HyperStack

open Lib.Sequence
open Lib.IntTypes
open Lib.Buffer

open FStar.Mul

module S = Hacl.Spec.Ed25519.Field56.Definition
module P = Spec.Curve25519

open FStar.Calc

let felem = lbuffer uint64 5ul

let point = lbuffer uint64 20ul

let paren_mul4 (a b c d:nat) : Lemma (a * b * c * d == a * (b * c * d))
  = ()

let paren_mul5 (a b c d e:nat) : Lemma (a * b * c * d * e == a * (b * c * d * e))
  = ()


#set-options "--z3rlimit 20 --max_fuel 0 --max_ifuel 0"

let lemma_fits_as_nat5 (f:S.felem5) : Lemma (S.as_nat5 f < pow2 256) =
  let (s0, s1, s2, s3, s4) = f in
  let max0 = pow2 56 - 1 in
  let max1 = (pow2 56 - 1) * pow2 56 in
  let max2 = (pow2 56 - 1) * pow2 56 * pow2 56 in
  let max3 = (pow2 56 - 1) * pow2 56 * pow2 56 * pow2 56 in
  let max4 = (pow2 32 - 1) * pow2 56 * pow2 56 * pow2 56 * pow2 56 in
  let x0 = uint_v s0 % S.pow56 in
  let x1 = (uint_v s1 % S.pow56) * S.pow56 in
  let x2 = (uint_v s2 % S.pow56) * S.pow56 * S.pow56 in
  let x3 = (uint_v s3 % S.pow56) * S.pow56 * S.pow56 * S.pow56 in
  let x4 = (uint_v s4 % S.pow32) * S.pow56 * S.pow56 * S.pow56 * S.pow56 in

  calc ( <= ) {
    x1;
    ( <= ) { FStar.Math.Lemmas.lemma_mult_le_right S.pow56 (uint_v s1 % S.pow56) (pow2 56 - 1) }
    max1;
  };

  calc ( <= ) {
    x2;
    (==) { FStar.Math.Lemmas.paren_mul_right (uint_v s2 % S.pow56) S.pow56 S.pow56 }
    (uint_v s2 % S.pow56)  * (S.pow56 * S.pow56);
    ( <= ) { FStar.Math.Lemmas.lemma_mult_le_right (S.pow56 * S.pow56) (uint_v s2 % S.pow56) (pow2 56 - 1) }
    max2;
  };
  calc ( <= ) {
    x3;
    (==) { paren_mul4 (uint_v s3 % S.pow56) S.pow56 S.pow56 S.pow56 }
    (uint_v s3 % S.pow56) * (S.pow56 * S.pow56 * S.pow56);
    ( <= ) { FStar.Math.Lemmas.lemma_mult_le_right
            (S.pow56 * S.pow56 * S.pow56)
            (uint_v s3 % S.pow56)
            (pow2 56 - 1) }
    (pow2 56 - 1) * (S.pow56 * S.pow56 * S.pow56);
    (==) { paren_mul4 (pow2 56 - 1)  S.pow56 S.pow56 S.pow56 }
    max3;
  };
  calc ( <= ) {
    x4;
    (==) { paren_mul5 (uint_v s4 % S.pow32) S.pow56 S.pow56 S.pow56 S.pow56 }
    (uint_v s4 % S.pow32)  * (S.pow56 * S.pow56 * S.pow56 * S.pow56);
    ( <= ) { FStar.Math.Lemmas.lemma_mult_le_right
            (S.pow56 * S.pow56 * S.pow56 * S.pow56)
            (uint_v s4 % S.pow32)
            (pow2 32 - 1) }
    (pow2 32 - 1) * (S.pow56 * S.pow56 * S.pow56 * S.pow56);
    (==) { paren_mul5 (pow2 32 - 1) S.pow56 S.pow56 S.pow56 S.pow56 }
    max4;
  };

  let max = max0 + max1 + max2 + max3 + max4 in
  assert_norm (max < pow2 256)

noextract
val as_nat: h:mem -> e:felem -> GTot (n:nat{n < pow2 256})
let as_nat h e =
  let s = as_seq h e in
  let s0 = s.[0] in
  let s1 = s.[1] in
  let s2 = s.[2] in
  let s3 = s.[3] in
  let s4 = s.[4] in
  lemma_fits_as_nat5 (s0, s1, s2, s3, s4);
  S.as_nat5 (s0, s1, s2, s3, s4)

noextract
val fevalh: h:mem -> f:felem -> GTot P.elem
let fevalh h f = (as_nat h f) % P.prime

noextract
val point_eval:h:mem -> p:point -> GTot Spec.Ed25519.ext_point
let point_eval h p =
  let x = gsub p 0ul 5ul in
  let y = gsub p 5ul 5ul in
  let z = gsub p 10ul 5ul in
  let t = gsub p 15ul 5ul in
  (fevalh h x, fevalh h y, fevalh h z, fevalh h t)
