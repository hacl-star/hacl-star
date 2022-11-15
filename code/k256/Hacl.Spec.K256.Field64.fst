module Hacl.Spec.K256.Field64

open FStar.Mul

open Lib.IntTypes
open Lib.Sequence

module S = Spec.K256

module SD = Hacl.Spec.Bignum.Definitions
module SB = Hacl.Spec.Bignum

#reset-options "--z3rlimit 50 --fuel 0 --ifuel 0"

(**
  The code is exactly the same as in `Hacl.Spec.Curve25519.Field64.Core`
  except for `carry_wide`.
  TODO: share the code between curve25519_64 and secp256k1_64
*)

unfold
let felem = SD.lbignum U64 4
unfold
let felem_wide = SD.lbignum U64 8
inline_for_extraction noextract
let prime_c = 0x1000003D1


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


// prime = 2^256 - prime_c
// prime_c = 2^32 + 977 = 4294968273; ~33 bits
val carry_pass_small: f:felem -> cin:uint64 -> felem
let carry_pass_small f cin =
  let c, r = add1 f (cin *. u64 prime_c) in
  let b1 = r.[0] +. c *. u64 prime_c in
  let out = r.[0] <- b1 in
  out


val carry_pass: f:felem -> cin:uint64 -> felem
let carry_pass f cin =
  let x = mul64_wide cin (u64 prime_c) in
  let x_lo = to_u64 x in
  let x_hi = to_u64 (x >>. 64ul) in
  let x_bn = create2 x_lo x_hi in

  let (c, out) = SB.bn_add f x_bn in
  carry_pass_small out c


val carry_wide: f:felem_wide -> felem
let carry_wide f =
  let c, r0 = mul1_add (sub f 4 4) (u64 prime_c) (sub f 0 4) in
  carry_pass r0 c


val add4: f1:felem -> f2:felem ->
  Pure (uint64 & felem)
  (requires True)
  (ensures fun (c, r) -> v c <= 1 /\
    SD.bn_v r + v c * pow2 256 == SD.bn_v f1 + SD.bn_v f2)

let add4 f1 f2 =
  let c, out = SB.bn_add f1 f2 in
  SB.bn_add_lemma f1 f2;
  c, out


val fadd4: f1:felem -> f2:felem -> felem
let fadd4 f1 f2 =
  let c0, out0 = add4 f1 f2 in
  carry_pass_small out0 c0


val sub4: f1:felem -> f2:felem ->
  Pure (uint64 & felem)
  (requires True)
  (ensures fun (c, r) -> v c <= 1 /\
    SD.bn_v r - v c * pow2 256 == SD.bn_v f1 - SD.bn_v f2)

let sub4 f1 f2 =
  let c, out = SB.bn_sub f1 f2 in
  SB.bn_sub_lemma f1 f2;
  c, out


val fsub4: f1:felem -> f2:felem -> felem
let fsub4 f1 f2 =
  let c0, r0 = sub4 f1 f2 in
  let c1, r1 = sub1 r0 (c0 *! u64 prime_c) in
  let b1 = r1.[0] -. c1 *. u64 prime_c in
  let out = r1.[0] <- b1 in
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


val fmul4: f1:felem -> r:felem -> felem
let fmul4 f1 r =
  let tmp = mul4 f1 r in
  carry_wide tmp


val fmul14: f1:felem -> f2:uint64 -> felem
let fmul14 f1 f2 =
  let c0, r0 = mul1 f1 f2 in
  carry_pass_small r0 c0


val sqr4: f:felem ->
  Pure felem_wide
  (requires True)
  (ensures  fun out ->
    SD.bn_v out == SD.bn_v f * SD.bn_v f)

let sqr4 f =
  let out = SB.bn_sqr f in
  SB.bn_sqr_lemma f;
  out


val fsqr4: f:felem -> felem
let fsqr4 f =
  let tmp = sqr4 f in
  carry_wide tmp
