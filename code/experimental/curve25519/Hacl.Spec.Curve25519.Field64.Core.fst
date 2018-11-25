module Hacl.Spec.Curve25519.Field64.Core

open Lib.Sequence
open Lib.IntTypes

#reset-options "--z3rlimit 50  --using_facts_from '* -FStar.Seq'"

let felem4 = (uint64 * uint64 * uint64 * uint64)
let felem_wide4 = (uint64 * uint64 * uint64 * uint64 * uint64 * uint64 * uint64 * uint64)

open FStar.Mul

let prime:pos =
  assert_norm (pow2 255 - 19 > 0);
  pow2 255 - 19

noextract
val as_nat4: f:felem4 -> GTot nat
let as_nat4 f =
  let (s0, s1, s2, s3) = f in
  v s0 + v s1 * pow2 64 + v s2 * pow2 64 * pow2 64 +
  v s3 * pow2 64 * pow2 64 * pow2 64

noextract
val wide_as_nat4: f:felem_wide4 -> GTot nat
let wide_as_nat4 f =
  let (s0, s1, s2, s3, s4, s5, s6, s7) = f in
  v s0 + v s1 * pow2 64 + v s2 * pow2 64 * pow2 64 +
  v s3 * pow2 64 * pow2 64 * pow2 64 +
  v s4 * pow2 64 * pow2 64 * pow2 64 * pow2 64 +
  v s5 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 +
  v s6 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 +
  v s7 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64

let felem = x:nat{x < prime}
let feval (f:felem4) : GTot felem = (as_nat4 f) % prime
let feval_wide (f:felem_wide4) : GTot felem = (wide_as_nat4 f) % prime

val fadd: felem -> felem -> felem
let fadd f1 f2 = (f1 + f2) % prime

val fsub: felem -> felem -> felem
let fsub f1 f2 = (f1 - f2) % prime

val fmul: felem -> felem -> felem
let fmul f1 f2 = (f1 * f2) % prime

inline_for_extraction noextract
val lt_u64:a:uint64 -> b:uint64 -> Tot bool
let lt_u64 a b =
  let open Lib.RawIntTypes in
  FStar.UInt64.(u64_to_UInt64 a <^ u64_to_UInt64 b)

inline_for_extraction noextract
val le_u64:a:uint64 -> b:uint64 -> Tot bool
let le_u64 a b =
  let open Lib.RawIntTypes in
  FStar.UInt64.(u64_to_UInt64 a <=^ u64_to_UInt64 b)

inline_for_extraction noextract
val eq_u64:a:uint64 -> b:uint64 -> Tot bool
let eq_u64 a b =
  let open Lib.RawIntTypes in
  FStar.UInt64.(u64_to_UInt64 a =^ u64_to_UInt64 b)

val addcarry:
    x:uint64
  -> y:uint64
  -> cin:uint64
  -> Pure (uint64 & uint64)
    (requires True)
    (ensures fun (r, c) ->
      v c <= 2 /\
      v r + v c * pow2 64 == v x + v y + v cin)
[@CInline]
let addcarry x y cin =
  let res1 = x +. cin in
  let c = if lt_u64 res1 cin then u64 1 else u64 0 in
  let res = res1 +. y in
  let c = if lt_u64 res res1 then c +. u64 1 else c in
  res, c

val subborrow:
    x:uint64
  -> y:uint64
  -> cin:uint64{v cin <= 1}
  -> Pure (uint64 & uint64)
    (requires True)
    (ensures fun (r, c) ->
      v r - v c * pow2 64 == v x - v y - v cin)
[@CInline]
let subborrow x y cin =
  let res = x -. y -. cin in
  let c =
    if eq_u64 cin (u64 1) then
      (if le_u64 x y then u64 1 else u64 0)
    else
      (if lt_u64 x y then u64 1 else u64 0) in
  res, c

val mul64:
    x:uint64
  -> y:uint64
  -> Pure (uint64 & uint64)
    (requires True)
    (ensures fun (l0, l1) ->
      v l0 + v l1 * pow2 64 = v x * v y)
[@CInline]
let mul64 x y =
  let res = mul64_wide x y in
  (to_u64 res, to_u64 (res >>. 64ul))

val add0carry:
    x:uint64
  -> y:uint64
  -> Pure (uint64 & uint64)
    (requires True)
    (ensures fun (r, c) ->
      v r + v c * pow2 64 == v x + v y)
[@CInline]
let add0carry x y =
  let res = x +. y in
  let c = if lt_u64 res x then u64 1 else u64 0 in
  res, c

val lemma_prime: unit ->
  Lemma (pow2 256 % prime == 38)
let lemma_prime () =
  assert_norm (pow2 256 = 2 * pow2 255);
  FStar.Math.Lemmas.lemma_mod_mul_distr_r 2 (pow2 255) prime;
  //assert (pow2 256 % prime == (2 * (pow2 255 % prime)) % prime);
  assert_norm (pow2 255 % prime = 19 % prime);
  assert_norm (19 < prime);
  FStar.Math.Lemmas.modulo_lemma 19 prime;
  //assert (pow2 256 % prime == (2 * 19) % prime);
  assert_norm (38 < prime);
  FStar.Math.Lemmas.modulo_lemma 38 prime

val lemma_mul_assos_5:
  a:nat -> b:nat -> c:nat -> d:nat -> e:nat ->
  Lemma (a * b * c * d * e == a * (b * c * d * e))
let lemma_mul_assos_5 a b c d e = ()

val add1:
    f:felem4
  -> cin:uint64
  -> Pure (uint64 & felem4)
    (requires True)
    (ensures fun (c, r) ->
      as_nat4 r + v c * pow2 256 == as_nat4 f + v cin)
let add1 f cin =
  let (f0, f1, f2, f3) = f in
  assert (as_nat4 f + v cin ==
    v f0 + v f1 * pow2 64 + v f2 * pow2 64 * pow2 64 +
    v f3 * pow2 64 * pow2 64 * pow2 64 + v cin);
  let o0, c0 = add0carry f0 cin in
  //assert (v o0 + v c0 * pow2 64 == v f0 + v cin);
  let o1, c1 = add0carry f1 c0 in
  //assert (v o1 + v c1 * pow2 64 == v f1 + v c0);
  let o2, c2 = add0carry f2 c1 in
  //assert (v o2 + v c2 * pow2 64 == v f2 + v c1);
  let o3, c3 = add0carry f3 c2 in
  //assert (v o3 + v c3 * pow2 64 == v f3 + v c2);
  assert (as_nat4 f + v cin ==
    v o0 + v c0 * pow2 64 +
    (v o1 + v c1 * pow2 64 - v c0) * pow2 64 +
    (v o2 + v c2 * pow2 64 - v c1) * pow2 64 * pow2 64 +
    (v o3 + v c3 * pow2 64 - v c2) * pow2 64 * pow2 64 * pow2 64);

  let out = (o0, o1, o2, o3) in
  assert (as_nat4 f + v cin ==
    v o0 + v o1 * pow2 64 + v o2 * pow2 64 * pow2 64 +
    v o3 * pow2 64 * pow2 64 * pow2 64 +
    v c3 * pow2 64 * pow2 64 * pow2 64 * pow2 64);
  assert (as_nat4 f + v cin ==
    as_nat4 out + v c3 * pow2 64 * pow2 64 * pow2 64 * pow2 64);
  lemma_mul_assos_5 (v c3) (pow2 64) (pow2 64) (pow2 64) (pow2 64);
  assert_norm (pow2 64 * pow2 64 * pow2 64 * pow2 64 = pow2 256);
  c3, out

val lemma_mul_pow256_add: f:felem4 -> c:uint64
  -> Lemma ((as_nat4 f + v c * pow2 256) % prime == (as_nat4 f + v c * 38) % prime)
let lemma_mul_pow256_add f c =
  FStar.Math.Lemmas.lemma_mod_plus_distr_r (as_nat4 f) (v c * pow2 256) prime;
  FStar.Math.Lemmas.lemma_mod_mul_distr_r (v c) (pow2 256) prime;
  lemma_prime ();
  assert ((v c * pow2 256) % prime == (v c * 38) % prime);
  FStar.Math.Lemmas.lemma_mod_plus_distr_r (as_nat4 f) (v c * 38) prime

val carry_pass:
    f:felem4
  -> cin:uint64{v cin * 38 < pow2 63}
  -> out:felem4{feval out == (as_nat4 f + v cin * pow2 256) % prime}
let carry_pass f cin =
  lemma_mul_pow256_add f cin;
  let carry, out0 = add1 f (cin *! u64 38) in
  let (o0, o1, o2, o3) = out0 in
  lemma_mul_pow256_add out0 carry;
  let o0' = o0 +! carry *! u64 38 in
  (o0', o1, o2, o3)

val sub1:
    f:felem4
  -> cin:uint64
  -> Pure (uint64 & felem4)
    (requires True)
    (ensures fun (c, r) ->
      as_nat4 r - v c * pow2 256 == as_nat4 f - v cin)
let sub1 f cin =
  let (f0, f1, f2, f3) = f in
  assert (as_nat4 f - v cin ==
    v f0 + v f1 * pow2 64 + v f2 * pow2 64 * pow2 64 +
    v f3 * pow2 64 * pow2 64 * pow2 64 - v cin);
  let o0, c0 = subborrow f0 cin (u64 0) in
  //assert (v o0 - v c0 * pow2 64 == v f0 - v cin);
  let o1, c1 = subborrow f1 (u64 0) c0 in
  //assert (v o1 - v c1 * pow2 64 == v f1 - v c0);
  let o2, c2 = subborrow f2 (u64 0) c1 in
  //assert (v o2 - v c2 * pow2 64 == v f2 - v c1);
  let o3, c3 = subborrow f3 (u64 0) c2 in
  //assert (v o3 - v c3 * pow2 64 == v f3 - v c2);
  let out = (o0, o1, o2, o3) in
  assert (as_nat4 f - v cin ==
    v o0 - v c0 * pow2 64 +
    (v o1 - v c1 * pow2 64 + v c0) * pow2 64 +
    (v o2 - v c2 * pow2 64 + v c1) * pow2 64 * pow2 64 +
    (v o3 - v c3 * pow2 64 + v c2) * pow2 64 * pow2 64 * pow2 64);
  assert (as_nat4 f - v cin ==
    v o0 + v o1 * pow2 64 +
    v o2 * pow2 64 * pow2 64 +
    v o3 * pow2 64 * pow2 64 * pow2 64 -
    v c3 * pow2 64 * pow2 64 * pow2 64 * pow2 64);
  assert (as_nat4 f - v cin ==
    as_nat4 out - v c3 * pow2 64 * pow2 64 * pow2 64 * pow2 64);
  lemma_mul_assos_5 (v c3) (pow2 64) (pow2 64) (pow2 64) (pow2 64);
  assert_norm (pow2 64 * pow2 64 * pow2 64 * pow2 64 = pow2 256);
  c3, out

val add4:
    f1:felem4
  -> f2:felem4
  -> Pure (uint64 & felem4)
    (requires True)
    (ensures fun (c, r) ->
      v c <= 1 /\
      as_nat4 r + v c * pow2 256 == as_nat4 f1 + as_nat4 f2)
let add4 f1 f2 =
  let (f10, f11, f12, f13) = f1 in
  let (f20, f21, f22, f23) = f2 in
  let o0, c0 = addcarry f10 f20 (u64 0) in
  //assert (v o0 + v c0 * pow2 64 == v f10 + v f20);
  let o1, c1 = addcarry f11 f21 c0 in
  //assert (v o1 + v c1 * pow2 64 == v f11 + v f21 + v c0);
  let o2, c2 = addcarry f12 f22 c1 in
  //assert (v o2 + v c2 * pow2 64 == v f12 + v f22 + v c1);
  let o3, c3 = addcarry f13 f23 c2 in
  //assert (v o3 + v c3 * pow2 64 == v f13 + v f23 + v c2);
  let out = (o0, o1, o2, o3) in
  assert (as_nat4 out + v c3 * pow2 256 ==
    v o0 + v o1 * pow2 64 + v o2 * pow2 64 * pow2 64 +
    v o3 * pow2 64 * pow2 64 * pow2 64 + v c3 * pow2 256);
  assert (as_nat4 out + v c3 * pow2 256 ==
    v f10 + v f20 - v c0 * pow2 64 +
    (v f11 + v f21 + v c0 - v c1 * pow2 64) * pow2 64 +
    (v f12 + v f22 + v c1 - v c2 * pow2 64) * pow2 64 * pow2 64 +
    (v f13 + v f23 + v c2 - v c3 * pow2 64) * pow2 64 * pow2 64 * pow2 64 +
    v c3 * pow2 256);
  assert (as_nat4 out + v c3 * pow2 256 ==
    v f10 + v f20 +
    v f11 * pow2 64 + v f21 * pow2 64 +
    v f12 * pow2 64 * pow2 64 + v f22 * pow2 64 * pow2 64 +
    v f13 * pow2 64 * pow2 64 * pow2 64 + v f23 * pow2 64 * pow2 64 * pow2 64 -
    v c3 * pow2 64 * pow2 64 * pow2 64 * pow2 64 +
    v c3 * pow2 256);
  lemma_mul_assos_5 (v c3) (pow2 64) (pow2 64) (pow2 64) (pow2 64);
  assert_norm (pow2 64 * pow2 64 * pow2 64 * pow2 64 = pow2 256);
  c3, out

val fadd4:
    f1:felem4
  -> f2:felem4
  -> out:felem4{feval out == fadd (feval f1) (feval f2)}
let fadd4 f1 f2 =
  let c0, out0 = add4 f1 f2 in
  assert (as_nat4 out0 + v c0 * pow2 256 == as_nat4 f1 + as_nat4 f2);
  let out = carry_pass out0 c0 in
  assert (feval out == (as_nat4 out0 + v c0 * pow2 256) % prime);
  assert (feval out == (as_nat4 f1 + as_nat4 f2) % prime);
  FStar.Math.Lemmas.lemma_mod_plus_distr_l (as_nat4 f1) (as_nat4 f2) prime;
  FStar.Math.Lemmas.lemma_mod_plus_distr_r ((as_nat4 f1) % prime) (as_nat4 f2) prime;
  out

val sub4:
    f1:felem4
  -> f2:felem4
  -> Pure (uint64 & felem4)
    (requires True)
    (ensures fun (c, r) ->
      v c <= 1 /\
      as_nat4 r - v c * pow2 256 == as_nat4 f1 - as_nat4 f2)
let sub4 f1 f2 =
  let (f10, f11, f12, f13) = f1 in
  let (f20, f21, f22, f23) = f2 in
  let o0, c0 = subborrow f10 f20 (u64 0) in
  assert (v o0 - v c0 * pow2 64 == v f10 - v f20);
  let o1, c1 = subborrow f11 f21 c0 in
  assert (v o1 - v c1 * pow2 64 == v f11 - v f21 - v c0);
  let o2, c2 = subborrow f12 f22 c1 in
  assert (v o2 - v c2 * pow2 64 == v f12 - v f22 - v c1);
  let o3, c3 = subborrow f13 f23 c2 in
  assert (v o3 - v c3 * pow2 64 == v f13 - v f23 - v c2);
  let out = (o0, o1, o2, o3) in
  assert (as_nat4 out - v c3 * pow2 256 ==
    v o0 + v o1 * pow2 64 + v o2 * pow2 64 * pow2 64 +
    v o3 * pow2 64 * pow2 64 * pow2 64 - v c3 * pow2 256);
  assert (as_nat4 out - v c3 * pow2 256 ==
    v f10 - v f20 + v c0 * pow2 64 +
    (v f11 - v f21 - v c0 + v c1 * pow2 64) * pow2 64 +
    (v f12 - v f22 - v c1 + v c2 * pow2 64) * pow2 64 * pow2 64 +
    (v f13 - v f23 - v c2 + v c3 * pow2 64) * pow2 64 * pow2 64 * pow2 64 -
    v c3 * pow2 256);

  assert (as_nat4 out - v c3 * pow2 256 ==
    v f10 - v f20 +
    v f11 * pow2 64 - v f21 * pow2 64 +
    v f12 * pow2 64 * pow2 64 - v f22 * pow2 64 * pow2 64 +
    v f13 * pow2 64 * pow2 64 * pow2 64 - v f23 * pow2 64 * pow2 64 * pow2 64 +
    v c3 * pow2 64 * pow2 64 * pow2 64 * pow2 64 - v c3 * pow2 256);
  lemma_mul_assos_5 (v c3) (pow2 64) (pow2 64) (pow2 64) (pow2 64);
  assert_norm (pow2 64 * pow2 64 * pow2 64 * pow2 64 = pow2 256);
  c3, out

val lemma_mod_sub_distr: a:int -> b:int -> n:pos ->
  Lemma ((a - b % n) % n = (a - b) % n)
let lemma_mod_sub_distr a b n =
  FStar.Math.Lemmas.lemma_div_mod b n;
  FStar.Math.Lemmas.distributivity_sub_left 0 (b / n) n;
  // (a - b) % n == (a - (b % n) - (b / n) * n) % n
  FStar.Math.Lemmas.lemma_mod_plus (a - (b % n)) (-(b / n)) n

val fsub4:
    f1:felem4
  -> f2:felem4
  -> out:felem4{feval out == fsub (feval f1) (feval f2)}
let fsub4 f1 f2 =
  let c0, out0 = sub4 f1 f2 in
  assert (as_nat4 out0 - v c0 * pow2 256 == as_nat4 f1 - as_nat4 f2);
  let c1, out1 = sub1 out0 (c0 *! u64 38) in
  assert (as_nat4 out1 - v c1 * pow2 256 == as_nat4 out0 - v c0 * 38);
  assert (as_nat4 out1 - v c1 * pow2 256 ==
    as_nat4 f1 - as_nat4 f2 + v c0 * pow2 256 - v c0 * 38);
  let (o0, o1, o2, o3) = out1 in
  let o0' = o0 -! c1 *! u64 38 in
  assert (v o0' == v o0 - v c1 * 38);
  let out2 = (o0', o1, o2, o3) in
  assert (as_nat4 out2 ==
    v o0 - v c1 * 38 +
    v o1 * pow2 64 +
    v o2 * pow2 64 * pow2 64 +
    v o3 * pow2 64 * pow2 64 * pow2 64);
  assert (as_nat4 out2 == as_nat4 out1 - v c1 * 38);
  assert (as_nat4 out2 == as_nat4 f1 - as_nat4 f2 + v c0 * pow2 256 -
    v c0 * 38 + v c1 * pow2 256 - v c1 * 38);
  assert (feval out2 == (as_nat4 f1 - as_nat4 f2 + v c0 * pow2 256 -
    v c0 * 38 + v c1 * pow2 256 - v c1 * 38) % prime);
  FStar.Math.Lemmas.lemma_mod_plus_distr_r (as_nat4 f1 - as_nat4 f2 + v c0 * pow2 256 -
    v c0 * 38 - v c1 * 38) (v c1 * pow2 256) prime;
  FStar.Math.Lemmas.lemma_mod_mul_distr_r (v c1) (pow2 256) prime;
  lemma_prime ();
  assert ((v c1 * pow2 256) % prime == (v c1 * 38) % prime);
  FStar.Math.Lemmas.lemma_mod_plus_distr_r (as_nat4 f1 - as_nat4 f2 + v c0 * pow2 256 -
    v c0 * 38 - v c1 * 38) (v c1 * 38) prime;
  assert (feval out2 == (as_nat4 f1 - as_nat4 f2 + v c0 * pow2 256 - v c0 * 38) % prime);

  FStar.Math.Lemmas.lemma_mod_plus_distr_r (as_nat4 f1 - as_nat4 f2 - v c0 * 38) (v c0 * pow2 256) prime;
  FStar.Math.Lemmas.lemma_mod_mul_distr_r (v c0) (pow2 256) prime;
  lemma_prime ();
  assert ((v c0 * pow2 256) % prime == (v c0 * 38) % prime);
  FStar.Math.Lemmas.lemma_mod_plus_distr_r (as_nat4 f1 - as_nat4 f2 - v c0 * 38) (v c0 * 38) prime;
  assert (feval out2 == (as_nat4 f1 - as_nat4 f2) % prime);
  FStar.Math.Lemmas.lemma_mod_plus_distr_l (as_nat4 f1) (- as_nat4 f2) prime;
  lemma_mod_sub_distr ((as_nat4 f1) % prime) (as_nat4 f2) prime;
  out2

val lemma_as_nat4:
    f:felem4
  -> Lemma (as_nat4 f < pow2 256)
let lemma_as_nat4 f =
  let (f0, f1, f2, f3) = f in
  assert (as_nat4 f == v f0 + v f1 * pow2 64 +
    v f2 * pow2 64 * pow2 64 + v f3 * pow2 64 * pow2 64 * pow2 64);
  assert (as_nat4 f <= pow2 64 - 1 + (pow2 64 - 1) * pow2 64 +
    (pow2 64 - 1) * pow2 64 * pow2 64 + (pow2 64 - 1) * pow2 64 * pow2 64 * pow2 64);
  assert (as_nat4 f <= pow2 64 - 1 + pow2 64 * pow2 64 - pow2 64 +
    pow2 64 * pow2 64 * pow2 64 - pow2 64 * pow2 64 +
    pow2 64 * pow2 64 * pow2 64 * pow2 64 - pow2 64 * pow2 64 * pow2 64);
  assert (as_nat4 f <= pow2 64 * pow2 64 * pow2 64 * pow2 64 - 1);
  assert_norm (pow2 64 * pow2 64 * pow2 64 * pow2 64 = pow2 256);
  assert (as_nat4 f <= pow2 256 - 1)

val lemma_mul1:
    f:felem4
  -> u:uint64
  -> Lemma (as_nat4 f * v u < pow2 320)
let lemma_mul1 f u =
  lemma_as_nat4 f;
  assert (as_nat4 f * v u <= (pow2 256 - 1) * v u);
  assert_spinoff (v u < pow2 64);
  assert_spinoff (as_nat4 f * v u < (pow2 256 - 1) * pow2 64);
  assert_norm (pow2 256 * pow2 64 = pow2 320)

val lemma_mul1_no_carry:
    a:nat{a < pow2 256}
  -> b:nat{b < pow2 320}
  -> c:nat
  -> Lemma
    (requires a + c * pow2 256 == b)
    (ensures c < pow2 64)
let lemma_mul1_no_carry a b c =
  assert (a + c * pow2 256 < pow2 320);
  assert_norm (pow2 64 * pow2 256 = pow2 320)

val mul1:
    f:felem4
  -> u:uint64
  -> Pure (uint64 & felem4)
    (requires True)
    (ensures fun (c, r) ->
      as_nat4 r + v c * pow2 256 == as_nat4 f * v u)
let mul1 f u =
  let (f0, f1, f2, f3) = f in
  let l0, h0 = mul64 f0 u in
  assert (v l0 + v h0 * pow2 64 = v f0 * v u);
  let l1, h1 = mul64 f1 u in
  assert (v l1 + v h1 * pow2 64 = v f1 * v u);
  let l2, h2 = mul64 f2 u in
  assert (v l2 + v h2 * pow2 64 = v f2 * v u);
  let l3, h3 = mul64 f3 u in
  assert (v l3 + v h3 * pow2 64 = v f3 * v u);
  let o0 = l0 in
  let o1, c0 = addcarry l1 h0 (u64 0) in
  assert (v o1 + v c0 * pow2 64 == v l1 + v h0);
  let o2, c1 = addcarry l2 h1 c0 in
  assert (v o2 + v c1 * pow2 64 == v l2 + v h1 + v c0);
  let o3, c2 = addcarry l3 h2 c1 in
  assert (v o3 + v c2 * pow2 64 == v l3 + v h2 + v c1);
  let out = (o0, o1, o2, o3) in

  assert (as_nat4 out  ==
    v o0 + v o1 * pow2 64 + v o2 * pow2 64 * pow2 64 + v o3 * pow2 64 * pow2 64 * pow2 64);
  assert (as_nat4 out  ==
    v l0 +
    (v l1 + v h0 - v c0 * pow2 64) * pow2 64 +
    (v l2 + v h1 + v c0 - v c1 * pow2 64) * pow2 64 * pow2 64 +
    (v l3 + v h2 + v c1 - v c2 * pow2 64) * pow2 64 * pow2 64 * pow2 64);
  assert (as_nat4 out  ==
    v f0 * v u - v h0 * pow2 64 +
    (v f1 * v u - v h1 * pow2 64 + v h0 - v c0 * pow2 64) * pow2 64 +
    (v f2 * v u - v h2 * pow2 64 + v h1 + v c0 - v c1 * pow2 64) * pow2 64 * pow2 64 +
    (v f3 * v u - v h3 * pow2 64 + v h2 + v c1 - v c2 * pow2 64) * pow2 64 * pow2 64 * pow2 64);
  assert (as_nat4 out  ==
    v f0 * v u - v h0 * pow2 64 +
    v f1 * v u * pow2 64 - v h1 * pow2 64 * pow2 64 +
      v h0 * pow2 64 - v c0 * pow2 64 * pow2 64 +
    v f2 * v u * pow2 64 * pow2 64 - v h2 * pow2 64 * pow2 64 * pow2 64 +
      v h1 * pow2 64 * pow2 64 + v c0 * pow2 64 * pow2 64 - v c1 * pow2 64 * pow2 64 * pow2 64 +
    v f3 * v u * pow2 64 * pow2 64 * pow2 64 - v h3 * pow2 64 * pow2 64 * pow2 64 * pow2 64 +
      v h2 * pow2 64 * pow2 64 * pow2 64 + v c1 * pow2 64 * pow2 64 * pow2 64 - v c2 * pow2 64 * pow2 64 * pow2 64 * pow2 64);

  assert (as_nat4 out ==
    v f0 * v u +
    v f1 * v u * pow2 64  +
    v f2 * v u * pow2 64 * pow2 64 +
    v f3 * v u * pow2 64 * pow2 64 * pow2 64 -
    v h3 * pow2 64 * pow2 64 * pow2 64 * pow2 64 -
    v c2 * pow2 64 * pow2 64 * pow2 64 * pow2 64);

  assume (as_nat4 f * v u ==
    v f0 * v u +
    v f1 * v u * pow2 64  +
    v f2 * v u * pow2 64 * pow2 64 +
    v f3 * v u * pow2 64 * pow2 64 * pow2 64);

  assert (as_nat4 out ==
    as_nat4 f * v u -
    v h3 * pow2 64 * pow2 64 * pow2 64 * pow2 64 -
    v c2 * pow2 64 * pow2 64 * pow2 64 * pow2 64);

  lemma_mul_assos_5 (v h3) (pow2 64) (pow2 64) (pow2 64) (pow2 64);
  lemma_mul_assos_5 (v c2) (pow2 64) (pow2 64) (pow2 64) (pow2 64);
  assert_norm (pow2 64 * pow2 64 * pow2 64 * pow2 64 = pow2 256);
  assert (as_nat4 out == as_nat4 f * v u - v h3 * pow2 256 - v c2 * pow2 256);
  assert (as_nat4 out + v h3 * pow2 256 + v c2 * pow2 256 == as_nat4 f * v u);
  FStar.Math.Lemmas.distributivity_add_left (v h3) (v c2) (pow2 256);
  assert (as_nat4 out + (v h3 + v c2) * pow2 256 == as_nat4 f * v u);
  lemma_mul1 f u;
  lemma_as_nat4 out;
  lemma_mul1_no_carry (as_nat4 out) (as_nat4 f * v u) (v h3 + v c2);
  assert (v h3 + v c2 < pow2 64);
  let c3 = h3 +! c2 in
  c3, out

val mul1_add:
    f1:felem4
  -> u2:uint64
  -> f3:felem4
  -> Pure (uint64 & felem4)
    (requires as_nat4 f3 + as_nat4 f1 * v u2 < pow2 320)
    (ensures fun (c, r) ->
      as_nat4 r + v c * pow2 256 == as_nat4 f3 + as_nat4 f1 * v u2)
let mul1_add f1 u2 f3 =
  let c, out0 = mul1 f1 u2 in
  assert (as_nat4 out0 + v c * pow2 256 == as_nat4 f1 * v u2);
  let (o0, o1, o2, o3) = out0 in
  let (f30, f31, f32, f33) = f3 in
  let o0', c0 = addcarry f30 o0 (u64 0) in
  //assert (v o0' + v c0 * pow2 64 == v f30 + v o0);
  let o1', c1 = addcarry f31 o1 c0 in
  //assert (v o1' + v c1 * pow2 64 == v f31 + v o1 + v c0);
  let o2', c2 = addcarry f32 o2 c1 in
  //assert (v o2' + v c2 * pow2 64 == v f32 + v o2 + v c1);
  let o3', c3 = addcarry f33 o3 c2 in
  //assert (v o3' + v c3 * pow2 64 == v f33 + v o3 + v c2);
  let out = (o0', o1', o2', o3') in
  assert (as_nat4 out ==
   v o0' + v o1' * pow2 64 + v o2' * pow2 64 * pow2 64 +
   v o3' * pow2 64 * pow2 64 * pow2 64);
  assert (as_nat4 out ==
   v f30 + v o0 - v c0 * pow2 64 +
   (v f31 + v o1 + v c0 - v c1 * pow2 64) * pow2 64 +
   (v f32 + v o2 + v c1 - v c2 * pow2 64) * pow2 64 * pow2 64 +
   (v f33 + v o3 + v c2 - v c3 * pow2 64) * pow2 64 * pow2 64 * pow2 64);

  assume (as_nat4 out ==
   v f30 + v o0 - v c0 * pow2 64 +
   v f31 * pow2 64 + v o1 * pow2 64 + v c0 * pow2 64 - v c1 * pow2 64 * pow2 64 +
   v f32 * pow2 64 * pow2 64 + v o2 * pow2 64 * pow2 64 + v c1 * pow2 64 * pow2 64 -
     v c2 * pow2 64 * pow2 64 * pow2 64 +
   v f33 * pow2 64 * pow2 64 * pow2 64 + v o3 * pow2 64 * pow2 64 * pow2 64 +
     v c2 * pow2 64 * pow2 64 * pow2 64 - v c3 * pow2 64 * pow2 64 * pow2 64 * pow2 64);

  assert (as_nat4 out ==
   v f30 + v o0  +
   v f31 * pow2 64 + v o1 * pow2 64 +
   v f32 * pow2 64 * pow2 64 + v o2 * pow2 64 * pow2 64 +
   v f33 * pow2 64 * pow2 64 * pow2 64 + v o3 * pow2 64 * pow2 64 * pow2 64 -
   v c3 * pow2 64 * pow2 64 * pow2 64 * pow2 64);

  assert (as_nat4 out == as_nat4 f3 + as_nat4 out0 -
   v c3 * pow2 64 * pow2 64 * pow2 64 * pow2 64);
  lemma_mul_assos_5 (v c3) (pow2 64) (pow2 64) (pow2 64) (pow2 64);
  assert_norm (pow2 64 * pow2 64 * pow2 64 * pow2 64 = pow2 256);
  assert (as_nat4 out == as_nat4 f3 + as_nat4 out0 - v c3 * pow2 256);
  assert (as_nat4 out == as_nat4 f3 + as_nat4 f1 * v u2 - v c * pow2 256 - v c3 * pow2 256);
  assert (as_nat4 out + v c * pow2 256 + v c3 * pow2 256 == as_nat4 f3 + as_nat4 f1 * v u2);
  FStar.Math.Lemmas.distributivity_add_left (v c) (v c3) (pow2 256);
  assert (as_nat4 out + (v c + v c3) * pow2 256 == as_nat4 f3 + as_nat4 f1 * v u2);
  lemma_as_nat4 out;
  assert (as_nat4 out < pow2 256);
  assert (as_nat4 f3 + as_nat4 f1 * v u2 < pow2 320);
  //lemma_mul1_no_carry (as_nat4 out) (as_nat4 f3 + as_nat4 f1 * v u2) (v c + v c3);
  assume (v c + v c3 < pow2 64); //FIXME
  let c4 = c +! c3 in
  c4, out

val lemma_feval_wide:
  f:felem_wide4
  -> Lemma (let (f0, f1, f2, f3, f4, f5, f6, f7) = f in
     (feval_wide f == (as_nat4 (f0, f1, f2, f3) + as_nat4 (f4, f5, f6, f7) * 38) % prime))
let lemma_feval_wide f = admit()

val lemma_carry_wide:
    a:nat{a < pow2 256}
  -> b:nat{b < pow2 263}
  -> c:nat
  -> Lemma
    (requires a + c * pow2 256 == b)
    (ensures c < pow2 7)
let lemma_carry_wide a b c =
  assert (a + c * pow2 256 < pow2 263);
  assert_norm (pow2 7 * pow2 256 = pow2 263)

val carry_wide:
    f:felem_wide4
  -> out:felem4{feval out == feval_wide f}
let carry_wide f =
  let (f0, f1, f2, f3, f4, f5, f6, f7) = f in
  lemma_as_nat4 (f4, f5, f6, f7);
  lemma_as_nat4 (f0, f1, f2, f3);
  assert_norm (38 < pow2 6);
  assert_norm (pow2 6 * pow2 256 = pow2 262);
  assert (as_nat4 (f0, f1, f2, f3) + as_nat4 (f4, f5, f6, f7) * 38 < pow2 263);
  assert_norm (pow2 263 < pow2 320);
  let c0, out0 = mul1_add (f4, f5, f6, f7) (u64 38) (f0, f1, f2, f3) in
  assert (as_nat4 out0 + v c0 * pow2 256 == as_nat4 (f0, f1, f2, f3) + as_nat4 (f4, f5, f6, f7) * 38);
  lemma_as_nat4 out0;
  lemma_carry_wide (as_nat4 out0) (as_nat4 (f0, f1, f2, f3) + as_nat4 (f4, f5, f6, f7) * 38) (v c0);
  let out1 = carry_pass out0 c0 in
  assert (feval out1 == (as_nat4 (f0, f1, f2, f3) + as_nat4 (f4, f5, f6, f7) * 38) % prime);
  lemma_feval_wide f;
  out1

val lemma_mul4_no_carry0:
    a:nat{a < pow2 64}
  -> b:nat{b < pow2 384}
  -> c:nat
  -> Lemma
    (requires a + c * pow2 64 == b)
    (ensures c < pow2 320)
let lemma_mul4_no_carry0 a b c =
  assert (a + c * pow2 64 < pow2 384);
  assert_norm (pow2 320 * pow2 64 = pow2 384)

val lemma_mul4_no_carry1:
    a:nat{a < pow2 128}
  -> b:nat{b < pow2 448}
  -> c:nat
  -> Lemma
    (requires a + c * pow2 64 * pow2 64 == b)
    (ensures c < pow2 320)
let lemma_mul4_no_carry1 a b c =
  assert (a + c * pow2 64 * pow2 64 < pow2 448);
  assert_norm (pow2 320 * pow2 64 * pow2 64 = pow2 448)

val mul4:
    f1:felem4
  -> r:felem4
  -> out:felem_wide4{wide_as_nat4 out == as_nat4 f1 * as_nat4 r}
let mul4 f1 r = admit();
  let (f0, f1, f2, f3) = f1 in
  let c0, out0 = mul1 r f0 in
  assert (as_nat4 out0 + v c0 * pow2 256 == as_nat4 r * v f0);
  let (o00, o01, o02, o03) = out0 in

  let c1, out1 = mul1_add r f1 (o01, o02, o03, c0) in
  assert (as_nat4 out1 + v c1 * pow2 256 == as_nat4 (o01, o02, o03, c0) + as_nat4 r * v f1);
  let (o11, o12, o13, o14) = out1 in

  let c2, out2 = mul1_add r f2 (o12, o13, o14, c1) in
  assert (as_nat4 out2 + v c2 * pow2 256 == as_nat4 (o12, o13, o14, c1) + as_nat4 r * v f2);
  let (o22, o23, o24, o25) = out2 in

  let c3, out3 = mul1_add r f3 (o23, o24, o25, c2) in
  assert (as_nat4 out3 + v c3 * pow2 256 == as_nat4 (o23, o24, o25, c2) + as_nat4 r * v f3);
  let (o33, o34, o35, o36) = out3 in

  let o37 = c3 in
  let out = (o00, o11, o22, o33, o34, o35, o36, o37) in
  out

val fmul4:
    f1:felem4
  -> r:felem4
  -> out:felem4{feval out == fmul (feval f1) (feval r)}
let fmul4 f1 r =
  let tmp = mul4 f1 r in
  assert (wide_as_nat4 tmp == as_nat4 f1 * as_nat4 r);
  let out = carry_wide tmp in
  assert (feval out == (as_nat4 f1 * as_nat4 r) % prime);
  FStar.Math.Lemmas.lemma_mod_mul_distr_l (as_nat4 f1) (as_nat4 r) prime;
  FStar.Math.Lemmas.lemma_mod_mul_distr_r (as_nat4 f1 % prime) (as_nat4 r) prime;
  out

val lemma_fmul14:
  a:nat{a < pow2 256} -> b:nat{b < pow2 17}
  -> Lemma (a * b < pow2 273)
let lemma_fmul14 a b =
  assert_norm (pow2 256 * pow2 17 = pow2 273)

val lemma_fmul14_no_carry0:
    a:nat{a < pow2 256}
  -> b:nat{b < pow2 273}
  -> c:nat
  -> Lemma
    (requires a + c * pow2 256 == b)
    (ensures c < pow2 17)
let lemma_fmul14_no_carry0 a b c =
  assert (a + c * pow2 256 < pow2 273);
  assert_norm (pow2 17 * pow2 256 = pow2 273)

val fmul14:
    f1:felem4
  -> f2:uint64{v f2 < pow2 17} //121665 < pow2 17
  -> out:felem4{feval out == (feval f1 * v f2) % prime}
let fmul14 f1 f2 =
  let c0, out0 = mul1 f1 f2 in
  assert (as_nat4 out0 + v c0 * pow2 256 == as_nat4 f1 * v f2);
  lemma_as_nat4 f1;
  lemma_fmul14 (as_nat4 f1) (v f2);
  assert (as_nat4 f1 * v f2 < pow2 273);
  lemma_as_nat4 out0;
  lemma_fmul14_no_carry0 (as_nat4 out0) (as_nat4 f1 * v f2) (v c0);
  let out1 = carry_pass out0 c0 in
  assert (feval out1 == (as_nat4 f1 * v f2) % prime);
  FStar.Math.Lemmas.lemma_mod_mul_distr_l (as_nat4 f1) (v f2) prime;
  out1

val sqr4: f:felem4 -> out:felem_wide4{wide_as_nat4 out == as_nat4 f * as_nat4 f}
let sqr4 f = mul4 f f

val fsqr4: f:felem4 -> out:felem4{feval out == fmul (feval f) (feval f)}
let fsqr4 f =
  let tmp = sqr4 f in
  let out = carry_wide tmp in
  assert (feval out == (as_nat4 f * as_nat4 f) % prime);
  FStar.Math.Lemmas.lemma_mod_mul_distr_l (as_nat4 f) (as_nat4 f) prime;
  FStar.Math.Lemmas.lemma_mod_mul_distr_r (as_nat4 f % prime) (as_nat4 f) prime;
  out
