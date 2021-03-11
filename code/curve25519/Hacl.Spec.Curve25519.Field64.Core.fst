module Hacl.Spec.Curve25519.Field64.Core

open FStar.Mul

open Lib.IntTypes
open Lib.Sequence

open Hacl.Spec.Curve25519.Field64.Definition

module P = Spec.Curve25519
module CL = Hacl.Spec.Curve25519.Field64.Lemmas

module SD = Hacl.Spec.Bignum.Definitions
module SB = Hacl.Spec.Bignum

#reset-options "--z3rlimit 50 --fuel 0 --ifuel 0"

unfold
let felem = SD.lbignum U64 4
unfold
let felem_wide = SD.lbignum U64 8

// let as_felem4 (e:felem) : felem4 =
//   (e.[0], e.[1], e.[2], e.[3])

// let as_nat (e:felem) = as_nat4 (as_felem4 e)


val add1: f:felem -> cin:uint64 ->
  Pure (uint64 & felem)
  (requires True)
  (ensures fun (c, r) -> v c <= 1 /\
    SD.bn_v r + v c * pow2 256 == SD.bn_v f + v cin)

let add1 f cin =
  let (c, out) = SB.bn_add1 f cin in
  SB.bn_add1_lemma f cin;
  (c, out)


val sub1: f:felem -> cin:uint64 ->
  Pure (uint64 & felem)
  (requires True)
  (ensures fun (c, r) -> v c <= 1 /\
    SD.bn_v r - v c * pow2 256 == SD.bn_v f - v cin)

let sub1 f cin =
  let c, out = SB.bn_sub1 f cin in
  SB.bn_sub1_lemma f cin;
  c, out


val mul1: f:felem -> u:uint64 ->
  Pure (uint64 & felem)
  (requires True)
  (ensures fun (c, r) ->
    SD.bn_v r + v c * pow2 256 == SD.bn_v f * v u)

let mul1 f u =
  let c, out = SB.bn_mul1 f u in
  SB.bn_mul1_lemma f u;
  c, out


val mul1_add: f1:felem -> u2:uint64 -> f3:felem ->
  Pure (uint64 & felem)
  (requires True)
  (ensures fun (c, r) ->
    SD.bn_v r + v c * pow2 256 == SD.bn_v f3 + SD.bn_v f1 * v u2)

let mul1_add f1 u2 f3 =
  let c, out = SB.bn_mul1_lshift_add f1 u2 0 f3 in
  SB.bn_mul1_lshift_add_lemma f1 u2 0 f3;
  c, out


val carry_pass: f:felem -> cin:uint64 -> felem
let carry_pass f cin =
  let c, r = add1 f (cin *. u64 38) in
  let b1 = r.[0] +. c *. u64 38 in
  let out = r.[0] <- b1 in
  out


val lemma_add1_carry: f:felem -> cin:uint64{v cin * 38 < pow2 63} ->
  Lemma (let c, r = add1 f (cin *! u64 38) in
    let b1 = r.[0] +. c *. u64 38 in
    v b1 == v r.[0] + v c * 38)

let lemma_add1_carry f cin =
  let c, r = add1 f (cin *! u64 38) in
  let b1 = r.[0] +. c *. u64 38 in
  assert (SD.bn_v r + v c * pow2 256 == SD.bn_v f + v cin * 38);
  SD.bn_eval_split_i f 1;
  SD.bn_eval1 (slice f 0 1);
  //assert (SD.bn_v f == v f.[0] + pow2 64 * SD.bn_v (slice f 1 4));
  SD.bn_eval_split_i r 1;
  SD.bn_eval1 (slice r 0 1);
  assert (v r.[0] + pow2 64 * SD.bn_v (slice r 1 4) + v c * pow2 256 == v f.[0] + pow2 64 * SD.bn_v (slice f 1 4) + v cin * 38);
  SD.bn_eval_bound (slice f 1 4) 3;
  SD.bn_eval_bound (slice r 1 4) 3;
  Math.Lemmas.pow2_plus 64 192;
  assert (v r.[0] == (v f.[0] + v cin * 38) % pow2 64)


val carry_pass_lemma: f:felem -> cin:uint64{v cin * 38 < pow2 63} ->
  Lemma (SD.bn_v (carry_pass f cin) % P.prime == (SD.bn_v f + v cin * pow2 256) % P.prime)

let carry_pass_lemma f cin =
  let c, r = add1 f (cin *! u64 38) in
  let b1 = r.[0] +. c *. u64 38 in

  let out = r.[0] <- b1 in
  SD.bn_upd_eval r b1 0;
  calc (==) {
    SD.bn_v out % P.prime;
    (==) { assert_norm (pow2 0 = 1) }
    (SD.bn_v r - v r.[0] + v b1) % P.prime;
    (==) { lemma_add1_carry f cin }
    (SD.bn_v r - v r.[0] + (v r.[0] + v c * 38)) % P.prime;
    (==) { }
    (SD.bn_v r + v c * 38) % P.prime;
    (==) { Lemmas.lemma_mul_pow256_add (SD.bn_v r) (v c) }
    (SD.bn_v r + v c * pow2 256) % P.prime;
    (==) { }
    (SD.bn_v f + v cin * 38) % P.prime;
    (==) { Lemmas.lemma_mul_pow256_add (SD.bn_v f) (v cin) }
    (SD.bn_v f + v cin * pow2 256) % P.prime;
    }


val carry_wide: f:felem_wide ->
  Pure felem
  (requires True)
  (ensures  fun out ->
    SD.bn_v out % P.prime == SD.bn_v f % P.prime)

let carry_wide f =
  let c, r0 = mul1_add (sub f 4 4) (u64 38) (sub f 0 4) in
  assert (SD.bn_v r0 + v c * pow2 256 == SD.bn_v (sub f 0 4) + SD.bn_v (sub f 4 4) * 38);
  SD.bn_eval_bound (sub f 0 4) 4;
  SD.bn_eval_bound (sub f 4 4) 4;
  SD.bn_eval_bound r0 4;
  Lemmas.carry_wide_bound (SD.bn_v r0) (v c) (SD.bn_v (sub f 0 4)) (SD.bn_v (sub f 4 4));

  let out = carry_pass r0 c in
  calc (==) {
    SD.bn_v out % P.prime;
    (==) { carry_pass_lemma r0 c }
    (SD.bn_v r0 + v c * pow2 256) % P.prime;
    (==) { }
    (SD.bn_v (sub f 0 4) + SD.bn_v (sub f 4 4) * 38) % P.prime;
    (==) { Lemmas.lemma_mul_pow256_add (SD.bn_v (sub f 0 4)) (SD.bn_v (sub f 4 4)) }
    (SD.bn_v (sub f 0 4) + SD.bn_v (sub f 4 4) * pow2 256) % P.prime;
    (==) { SD.bn_concat_lemma (sub f 0 4) (sub f 4 4) }
    SD.bn_v (concat (sub f 0 4) (sub f 4 4)) % P.prime;
    (==) { eq_intro f (concat (sub f 0 4) (sub f 4 4)) }
    SD.bn_v f % P.prime;
  };
  out


val add4: f1:felem -> f2:felem ->
  Pure (uint64 & felem)
  (requires True)
  (ensures fun (c, r) -> v c <= 1 /\
    SD.bn_v r + v c * pow2 256 == SD.bn_v f1 + SD.bn_v f2)

let add4 f1 f2 =
  let c, out = SB.bn_add f1 f2 in
  SB.bn_add_lemma f1 f2;
  c, out


val fadd4: f1:felem -> f2:felem ->
  Pure felem
  (requires True)
  (ensures  fun out ->
    SD.bn_v out % P.prime == P.fadd (SD.bn_v f1 % P.prime) (SD.bn_v f2 % P.prime))

let fadd4 f1 f2 =
  let c0, out0 = add4 f1 f2 in
  let out = carry_pass out0 c0 in
  carry_pass_lemma out0 c0;
  assert (SD.bn_v out % P.prime == (SD.bn_v f1 + SD.bn_v f2) % P.prime);
  Math.Lemmas.lemma_mod_plus_distr_l (SD.bn_v f1) (SD.bn_v f2) P.prime;
  Math.Lemmas.lemma_mod_plus_distr_r (SD.bn_v f1 % P.prime) (SD.bn_v f2) P.prime;
  out


val sub4: f1:felem -> f2:felem ->
  Pure (uint64 & felem)
  (requires True)
  (ensures fun (c, r) -> v c <= 1 /\
    SD.bn_v r - v c * pow2 256 == SD.bn_v f1 - SD.bn_v f2)

let sub4 f1 f2 =
  let c, out = SB.bn_sub f1 f2 in
  SB.bn_sub_lemma f1 f2;
  c, out


val lemma_sub1_carry: f:felem -> cin:uint64{v cin * 38 < pow2 63} ->
  Lemma (let c, r = sub1 f (cin *! u64 38) in
    let b1 = r.[0] -. c *. u64 38 in
    v b1 == v r.[0] - v c * 38)

let lemma_sub1_carry f cin =
  let c, r = sub1 f (cin *! u64 38) in
  let b1 = r.[0] -. c *. u64 38 in
  assert (SD.bn_v r - v c * pow2 256 == SD.bn_v f - v cin * 38);

  SD.bn_eval_split_i f 1;
  SD.bn_eval1 (slice f 0 1);
  //assert (SD.bn_v f == v f.[0] + pow2 64 * SD.bn_v (slice f 1 4));
  SD.bn_eval_split_i r 1;
  SD.bn_eval1 (slice r 0 1);
  assert (v r.[0] + pow2 64 * SD.bn_v (slice r 1 4) - v c * pow2 256 == v f.[0] + pow2 64 * SD.bn_v (slice f 1 4) - v cin * 38);
  SD.bn_eval_bound (slice f 1 4) 3;
  SD.bn_eval_bound (slice r 1 4) 3;
  Math.Lemmas.pow2_plus 64 192;
  assert (v r.[0] == (v f.[0] - v cin * 38) % pow2 64)


val fsub4: f1:felem -> f2:felem ->
  Pure felem
  (requires True)
  (ensures  fun out ->
    SD.bn_v out % P.prime == P.fsub (SD.bn_v f1 % P.prime) (SD.bn_v f2 % P.prime))

let fsub4 f1 f2 =
  let c0, r0 = sub4 f1 f2 in
  let c1, r1 = sub1 r0 (c0 *! u64 38) in
  let b1 = r1.[0] -. c1 *. u64 38 in

  let out = r1.[0] <- b1 in
  SD.bn_upd_eval r1 b1 0;
  calc (==) {
    SD.bn_v out % P.prime;
    (==) { assert_norm (pow2 0 = 1) }
    (SD.bn_v r1 - v r1.[0] + v b1) % P.prime;
    (==) { lemma_sub1_carry r0 c0 }
    (SD.bn_v r1 - v r1.[0] + (v r1.[0] - v c1 * 38)) % P.prime;
    (==) { }
    (SD.bn_v f1 - SD.bn_v f2 + v c0 * pow2 256 - v c0 * 38 + v c1 * pow2 256 - v c1 * 38) % P.prime;
    (==) { Lemmas.lemma_fsub4 (SD.bn_v f1) (SD.bn_v f2) (v c0) (v c1) }
    (SD.bn_v f1 % P.prime - SD.bn_v f2 % P.prime) % P.prime;
    };
  out


val mul4: f:felem -> r:felem ->
  Pure felem_wide
  (requires True)
  (ensures  fun out ->
    SD.bn_v out == SD.bn_v f * SD.bn_v r)

let mul4 f r =
  let out = SB.bn_mul f r in
  SB.bn_mul_lemma f r;
  out


val fmul4: f1:felem -> r:felem ->
  Pure felem
  (requires True)
  (ensures  fun out ->
    SD.bn_v out % P.prime == P.fmul (SD.bn_v f1 % P.prime) (SD.bn_v r % P.prime))

let fmul4 f1 r =
  let tmp = mul4 f1 r in
  let out = carry_wide tmp in
  Math.Lemmas.lemma_mod_mul_distr_l (SD.bn_v f1) (SD.bn_v r) P.prime;
  Math.Lemmas.lemma_mod_mul_distr_r (SD.bn_v f1 % P.prime) (SD.bn_v r) P.prime;
  out


//121665 < pow2 17
val fmul14: f1:felem -> f2:uint64 ->
  Pure felem
  (requires v f2 < pow2 17)
  (ensures  fun out ->
    SD.bn_v out % P.prime == SD.bn_v f1 % P.prime * v f2 % P.prime)

let fmul14 f1 f2 =
  let c0, r0 = mul1 f1 f2 in
  assert (SD.bn_v r0 + v c0 * pow2 256 == SD.bn_v f1 * v f2);
  SD.bn_eval_bound f1 4;
  SD.bn_eval_bound r0 4;
  Lemmas.fmul14_bound (SD.bn_v r0) (v c0) (SD.bn_v f1) (v f2);

  let out = carry_pass r0 c0 in
  calc (==) {
    SD.bn_v out % P.prime;
    (==) { carry_pass_lemma r0 c0 }
    (SD.bn_v r0 + v c0 * pow2 256) % P.prime;
    (==) { }
    (SD.bn_v f1 * v f2) % P.prime;
    (==) {Math.Lemmas.lemma_mod_mul_distr_l (SD.bn_v f1) (v f2) P.prime }
    (SD.bn_v f1 % P.prime * v f2) % P.prime;
    };
  out


val sqr4: f:felem ->
  Pure felem_wide
  (requires True)
  (ensures  fun out ->
    SD.bn_v out == SD.bn_v f * SD.bn_v f)

let sqr4 f =
  let out = SB.bn_sqr f in
  SB.bn_sqr_lemma f;
  out


val fsqr4: f:felem ->
  Pure felem
  (requires True)
  (ensures  fun out ->
    SD.bn_v out % P.prime == P.fmul (SD.bn_v f % P.prime) (SD.bn_v f % P.prime))

let fsqr4 f =
  let tmp = sqr4 f in
  let out = carry_wide tmp in
  Math.Lemmas.lemma_mod_mul_distr_l (SD.bn_v f) (SD.bn_v f) P.prime;
  Math.Lemmas.lemma_mod_mul_distr_r (SD.bn_v f % P.prime) (SD.bn_v f) P.prime;
  out
