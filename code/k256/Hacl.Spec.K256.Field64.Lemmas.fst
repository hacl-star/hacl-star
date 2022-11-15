module Hacl.Spec.K256.Field64.Lemmas

open FStar.Mul

open Lib.IntTypes
open Lib.Sequence

module S = Spec.K256

module SD = Hacl.Spec.Bignum.Definitions
module SB = Hacl.Spec.Bignum

include Hacl.Spec.K256.Field64

#reset-options "--z3rlimit 50 --fuel 0 --ifuel 0"

val lemma_add1_or_sub1_index_0 (f r:felem) (cin c:int) : Lemma
  (requires SD.bn_v r + c * pow2 256 == SD.bn_v f + cin)
  (ensures  v r.[0] == (v f.[0] + cin) % pow2 64)

let lemma_add1_or_sub1_index_0 f r cin c =
  assert (SD.bn_v r + c * pow2 256 == SD.bn_v f + cin);
  SD.bn_eval_split_i f 1;
  SD.bn_eval1 (slice f 0 1);
  assert (SD.bn_v f == v f.[0] + pow2 64 * SD.bn_v (slice f 1 4));
  SD.bn_eval_split_i r 1;
  SD.bn_eval1 (slice r 0 1);
  assert (
    v r.[0] + pow2 64 * SD.bn_v (slice r 1 4) + c * pow2 256 ==
    v f.[0] + pow2 64 * SD.bn_v (slice f 1 4) + cin);

  calc (==) {
    (v r.[0] + pow2 64 * SD.bn_v (slice r 1 4) + c * pow2 256) % pow2 64;
    (==) { Math.Lemmas.modulo_addition_lemma
      (v r.[0] + c * pow2 256) (pow2 64) (SD.bn_v (slice r 1 4)) }
    (v r.[0] + c * pow2 256) % pow2 64;
    (==) { Math.Lemmas.pow2_plus 192 64; Math.Lemmas.paren_mul_right (c) (pow2 192) (pow2 64) }
    (v r.[0] + c * pow2 192 * pow2 64) % pow2 64;
    (==) { Math.Lemmas.modulo_addition_lemma (v r.[0]) (pow2 64) (c * pow2 192) }
    (v r.[0]) % pow2 64;
  };
  Math.Lemmas.small_mod (v r.[0]) (pow2 64);
  assert (v r.[0] == (v f.[0] + pow2 64 * SD.bn_v (slice f 1 4) + cin) % pow2 64);
  Math.Lemmas.modulo_addition_lemma (v f.[0] + cin) (pow2 64) (SD.bn_v (slice f 1 4));
  assert (v r.[0] == (v f.[0] + cin) % pow2 64)


val lemma_add1_carry_is_zero: f:felem -> cin:uint64 -> Lemma
  (requires v f.[0] + v cin < pow2 64)
  (ensures (let c, r = add1 f cin in v c = 0))

let lemma_add1_carry_is_zero f cin =
  let c, r = add1 f cin in
  assert (SD.bn_v r + v c * pow2 256 == SD.bn_v f + v cin);
  SD.bn_eval_split_i f 1;
  SD.bn_eval1 (slice f 0 1);
  assert (SD.bn_v r + v c * pow2 256 == v f.[0] + pow2 64 * SD.bn_v (slice f 1 4) + v cin);
  assert (v f.[0] + pow2 64 * SD.bn_v (slice f 1 4) + v cin <
    pow2 64 + pow2 64 * SD.bn_v (slice f 1 4));
  SD.bn_eval_bound (slice f 1 4) 3;
  Math.Lemmas.lemma_mult_le_left (pow2 64) (SD.bn_v (slice f 1 4)) (pow2 192 - 1);
  assert (pow2 64 + pow2 64 * SD.bn_v (slice f 1 4) <= pow2 64 + pow2 64 * (pow2 192 - 1));
  Math.Lemmas.distributivity_sub_right (pow2 64) (pow2 192) 1;
  Math.Lemmas.pow2_plus 64 192;
  assert (pow2 64 + pow2 64 * SD.bn_v (slice f 1 4) <= pow2 256);
  assert (SD.bn_v r + v c * pow2 256 < pow2 256);
  SD.bn_eval_bound r 4


val lemma_add1_carry_small: f:felem -> cin:uint64{(v cin + 1) * prime_c < pow2 64} ->
  Lemma (let c, r = add1 f (cin *! u64 prime_c) in
    let b1 = r.[0] +. c *. u64 prime_c in
    v b1 == v r.[0] + v c * prime_c)

let lemma_add1_carry_small f cin =
  let c, r = add1 f (cin *! u64 prime_c) in
  assert (SD.bn_v r + v c * pow2 256 == SD.bn_v f + v cin * prime_c);
  lemma_add1_or_sub1_index_0 f r (v cin * prime_c) (v c);
  assert (v r.[0] == (v f.[0] + v cin * prime_c) % pow2 64);

  let b1 = r.[0] +. c *. u64 prime_c in
  assert (v b1 == (v r.[0] + (v c * prime_c % pow2 64)) % pow2 64);
  Math.Lemmas.lemma_mod_plus_distr_r (v r.[0]) (v c * prime_c) (pow2 64);
  assert (v b1 == (v r.[0] + v c * prime_c) % pow2 64);
  if v f.[0] + v cin * prime_c < pow2 64 then begin
    lemma_add1_carry_is_zero f (cin *! u64 prime_c);
    assert (v c = 0);
    Math.Lemmas.small_mod (v r.[0]) (pow2 64) end
  else begin
    Math.Lemmas.euclidean_division_definition (v f.[0] + v cin * prime_c) (pow2 64);
    assert ((v f.[0] + v cin * prime_c) % pow2 64 == v f.[0] + v cin * prime_c - pow2 64);
    assert (v r.[0] + v c * prime_c == v f.[0] + v cin * prime_c - pow2 64 + v c * prime_c);
    Math.Lemmas.distributivity_add_left (v cin) (v c) prime_c;
    assert (v r.[0] + v c * prime_c == v f.[0] + (v cin + v c) * prime_c - pow2 64);
    assert (v r.[0] + v c * prime_c < v f.[0]);
    Math.Lemmas.small_mod (v r.[0] + v c * prime_c) (pow2 64) end


val lemma_prime: unit -> Lemma (pow2 256 % S.prime == prime_c)
let lemma_prime () =
  calc (==) {
    pow2 256 % S.prime;
    (==) { Math.Lemmas.sub_div_mod_1 (pow2 256) S.prime }
    prime_c % S.prime;
    (==) { Math.Lemmas.small_mod prime_c S.prime }
    prime_c;
  }


val lemma_mul_pow256_add: fn:int -> c:int ->
  Lemma ((fn + c * pow2 256) % S.prime == (fn + c * prime_c) % S.prime)
let lemma_mul_pow256_add fn c =
  calc (==) {
    (fn + c * pow2 256) % S.prime;
    (==) { Math.Lemmas.lemma_mod_plus_distr_r fn (c * pow2 256) S.prime }
    (fn + c * pow2 256 % S.prime) % S.prime;
    (==) { Math.Lemmas.lemma_mod_mul_distr_r c (pow2 256) S.prime }
    (fn + c * (pow2 256 % S.prime) % S.prime) % S.prime;
    (==) { lemma_prime () }
    (fn + c * prime_c % S.prime) % S.prime;
    (==) { Math.Lemmas.lemma_mod_plus_distr_r fn (c * prime_c) S.prime }
    (fn + c * prime_c) % S.prime;
  }


let carry_pass_small_lemma f cin =
  let c, r = add1 f (cin *! u64 prime_c) in
  let b1 = r.[0] +. c *. u64 prime_c in

  let out = r.[0] <- b1 in
  SD.bn_upd_eval r b1 0;
  calc (==) {
    SD.bn_v out % S.prime;
    (==) { assert_norm (pow2 0 = 1) }
    (SD.bn_v r - v r.[0] + v b1) % S.prime;
    (==) { lemma_add1_carry_small f cin }
    (SD.bn_v r - v r.[0] + (v r.[0] + v c * prime_c)) % S.prime;
    (==) { }
    (SD.bn_v r + v c * prime_c) % S.prime;
    (==) { lemma_mul_pow256_add (SD.bn_v r) (v c) }
    (SD.bn_v r + v c * pow2 256) % S.prime;
    (==) { }
    (SD.bn_v f + v cin * prime_c) % S.prime;
    (==) { lemma_mul_pow256_add (SD.bn_v f) (v cin) }
    (SD.bn_v f + v cin * pow2 256) % S.prime;
    }

//---------------

val bn_eval_create2 : x0:uint64 -> x1:uint64 ->
  Lemma (SD.bn_v (create2 x0 x1) == v x0 + v x1 * pow2 64)

let bn_eval_create2 x0 x1 =
  let x_bn = create2 x0 x1 in
  SD.bn_eval_unfold_i x_bn 2;
  SD.bn_eval_unfold_i x_bn 1;
  SD.bn_eval0 x_bn;
  assert (SD.bn_v (create2 x0 x1) = v x_bn.[0] + v x_bn.[1] * pow2 64);
  create2_lemma x0 x1


let carry_pass_lemma f cin =
  let x = mul64_wide cin (u64 prime_c) in
  assert (v x = v cin * prime_c);
  let x_lo = to_u64 x in
  let x_hi = to_u64 (x >>. 64ul) in
  assert (v x = v x_lo + v x_hi * pow2 64);
  let x_bn = create2 x_lo x_hi in
  bn_eval_create2 x_lo x_hi;
  assert (SD.bn_v x_bn == v x);

  let (c, out) = SB.bn_add f x_bn in
  SB.bn_add_lemma f x_bn;
  assert (SD.bn_v out + v c * pow2 256 = SD.bn_v f + v cin * prime_c);
  let res = carry_pass_small out c in
  carry_pass_small_lemma out c;
  assert (SD.bn_v (carry_pass f cin) % S.prime == (SD.bn_v f + v cin * prime_c) % S.prime);
  lemma_mul_pow256_add (SD.bn_v f) (v cin)

//---------------

val lemma_carry_bound: a:nat -> b:nat -> c:nat -> d:nat -> e:pos -> Lemma
  (requires
    a + b * pow2 256 == c + d * e /\
    a < pow2 256 /\ c < pow2 256 /\ d < pow2 256)
  (ensures b <= e)

let lemma_carry_bound a b c d e =
  Math.Lemmas.lemma_mult_lt_right e d (pow2 256);
  assert (c + d * e < pow2 256 + pow2 256 * e);
  Math.Lemmas.distributivity_add_right (pow2 256) 1 e;
  assert (b * pow2 256 < pow2 256 * (1 + e));
  assert (b < 1 + e)


let carry_wide_lemma f =
  let c, r0 = mul1_add (sub f 4 4) (u64 prime_c) (sub f 0 4) in
  assert (SD.bn_v r0 + v c * pow2 256 == SD.bn_v (sub f 0 4) + SD.bn_v (sub f 4 4) * prime_c);
  // SD.bn_eval_bound (sub f 0 4) 4;
  // SD.bn_eval_bound (sub f 4 4) 4;
  // SD.bn_eval_bound r0 4;
  // lemma_carry_bound (SD.bn_v r0) (v c) (SD.bn_v (sub f 0 4)) (SD.bn_v (sub f 4 4)) prime_c;
  // assert (v c <= prime_c);
  // Math.Lemmas.lemma_mult_le_right prime_c (v c) prime_c;
  // assert (v c * prime_c <= prime_c * prime_c);
  // assert_norm (prime_c * prime_c < pow2 65);
  // assert (v c * prime_c < pow2 65); // ==> we can't call `carry_pass_small`

  let out = carry_pass r0 c in
  calc (==) {
    SD.bn_v out % S.prime;
    (==) { carry_pass_lemma r0 c }
    (SD.bn_v r0 + v c * pow2 256) % S.prime;
    (==) { }
    (SD.bn_v (sub f 0 4) + SD.bn_v (sub f 4 4) * prime_c) % S.prime;
    (==) { lemma_mul_pow256_add (SD.bn_v (sub f 0 4)) (SD.bn_v (sub f 4 4)) }
    (SD.bn_v (sub f 0 4) + SD.bn_v (sub f 4 4) * pow2 256) % S.prime;
    (==) { SD.bn_concat_lemma (sub f 0 4) (sub f 4 4) }
    SD.bn_v (concat (sub f 0 4) (sub f 4 4)) % S.prime;
    (==) { eq_intro f (concat (sub f 0 4) (sub f 4 4)) }
    SD.bn_v f % S.prime;
  }

//---------------

let fadd4_lemma f1 f2 =
  let c0, out0 = add4 f1 f2 in
  let out = carry_pass_small out0 c0 in
  carry_pass_small_lemma out0 c0;
  assert (SD.bn_v out % S.prime == (SD.bn_v f1 + SD.bn_v f2) % S.prime);
  Math.Lemmas.lemma_mod_plus_distr_l (SD.bn_v f1) (SD.bn_v f2) S.prime;
  Math.Lemmas.lemma_mod_plus_distr_r (SD.bn_v f1 % S.prime) (SD.bn_v f2) S.prime

//---------------

val lemma_sub1_carry_is_zero: f:felem -> cin:uint64 -> Lemma
  (requires 0 <= v f.[0] - v cin)
  (ensures (let c, r = sub1 f cin in v c = 0))

let lemma_sub1_carry_is_zero f cin =
  let c, r = sub1 f cin in
  assert (SD.bn_v r - v c * pow2 256 == SD.bn_v f - v cin);
  SD.bn_eval_split_i f 1;
  SD.bn_eval1 (slice f 0 1);
  assert (SD.bn_v r - v c * pow2 256 == v f.[0] + pow2 64 * SD.bn_v (slice f 1 4) - v cin);
  assert (pow2 64 * SD.bn_v (slice f 1 4) <= SD.bn_v r - v c * pow2 256);
  assert (0 <= SD.bn_v r - v c * pow2 256);
  SD.bn_eval_bound r 4


val lemma_sub1_carry_small: f:felem -> cin:uint64{v cin <= 1} ->
  Lemma (let c, r = sub1 f (cin *! u64 prime_c) in
    let b1 = r.[0] -. c *. u64 prime_c in
    v b1 == v r.[0] - v c * prime_c)

let lemma_sub1_carry_small f cin =
  let c, r = sub1 f (cin *! u64 prime_c) in
  assert (SD.bn_v r - v c * pow2 256 == SD.bn_v f - v cin * prime_c);
  lemma_add1_or_sub1_index_0 f r (- v cin * prime_c) (- v c);
  assert (v r.[0] == (v f.[0] - v cin * prime_c) % pow2 64);

  let b1 = r.[0] -. c *. u64 prime_c in
  assert (v b1 == (v r.[0] - (v c * prime_c % pow2 64)) % pow2 64);
  Math.Lemmas.lemma_mod_sub_distr (v r.[0]) (v c * prime_c) (pow2 64);
  assert (v b1 == (v r.[0] - v c * prime_c) % pow2 64);

  if 0 <= v f.[0] - v cin * prime_c then begin
    lemma_sub1_carry_is_zero f (cin *! u64 prime_c);
    assert (v c = 0);
    Math.Lemmas.small_mod (v r.[0]) (pow2 64) end
  else begin
    assert (v f.[0] - v cin * prime_c < 0);
    Math.Lemmas.euclidean_division_definition (v f.[0] - v cin * prime_c) (pow2 64);
    assert ((v f.[0] - v cin * prime_c) % pow2 64 == v f.[0] - v cin * prime_c + pow2 64);
    assert (v r.[0] - v c * prime_c == v f.[0] - v cin * prime_c + pow2 64 - v c * prime_c);
    assert (v r.[0] - v c * prime_c < pow2 64);
    assert (0 <= v r.[0] - v c * prime_c) end


val lemma_fsub4_aux: fn1:nat -> fn2:nat -> c0:nat -> c1:nat ->
  Lemma ((fn1 - fn2 + c0 * pow2 256 - c0 * prime_c + c1 * pow2 256 - c1 * prime_c) % S.prime ==
    (fn1 % S.prime - fn2 % S.prime) % S.prime)

let lemma_fsub4_aux fn1 fn2 c0 c1 =
  calc (==) {
    (fn1 - fn2 + c0 * pow2 256 - c0 * prime_c + c1 * pow2 256 - c1 * prime_c) % S.prime;
    (==) { lemma_mul_pow256_add (fn1 - fn2 + c0 * pow2 256 - c0 * prime_c + c1 * pow2 256) (- c1) }
    (fn1 - fn2 + c0 * pow2 256 - c0 * prime_c + c1 * pow2 256 - c1 * pow2 256) % S.prime;
    (==) { }
    (fn1 - fn2 + c0 * pow2 256 - c0 * prime_c) % S.prime;
    (==) { lemma_mul_pow256_add (fn1 - fn2 + c0 * pow2 256) (- c0) }
    (fn1 - fn2 + c0 * pow2 256 - c0 * pow2 256) % S.prime;
    (==) { }
    (fn1 - fn2) % S.prime;
    (==) { Math.Lemmas.lemma_mod_plus_distr_l fn1 (- fn2) S.prime }
    (fn1 % S.prime - fn2) % S.prime;
    (==) { Math.Lemmas.lemma_mod_sub_distr (fn1 % S.prime) fn2 S.prime }
    (fn1 % S.prime - fn2 % S.prime) % S.prime;
    }


let fsub4_lemma f1 f2 =
  let c0, r0 = sub4 f1 f2 in
  let c1, r1 = sub1 r0 (c0 *! u64 prime_c) in
  let b1 = r1.[0] -. c1 *. u64 prime_c in
  assert (v c0 <= 1);

  let out = r1.[0] <- b1 in
  SD.bn_upd_eval r1 b1 0;
  calc (==) {
    SD.bn_v out % S.prime;
    (==) { assert_norm (pow2 0 = 1) }
    (SD.bn_v r1 - v r1.[0] + v b1) % S.prime;
    (==) { lemma_sub1_carry_small r0 c0 }
    (SD.bn_v r1 - v r1.[0] + (v r1.[0] - v c1 * prime_c)) % S.prime;
    (==) { }
    (SD.bn_v f1 - SD.bn_v f2 + v c0 * pow2 256 - v c0 * prime_c +
      v c1 * pow2 256 - v c1 * prime_c) % S.prime;
    (==) { lemma_fsub4_aux (SD.bn_v f1) (SD.bn_v f2) (v c0) (v c1) }
    (SD.bn_v f1 % S.prime - SD.bn_v f2 % S.prime) % S.prime;
    }

//-------------------

let fmul4_lemma f1 r =
  let tmp = mul4 f1 r in
  let out = carry_wide tmp in
  carry_wide_lemma tmp;
  Math.Lemmas.lemma_mod_mul_distr_l (SD.bn_v f1) (SD.bn_v r) S.prime;
  Math.Lemmas.lemma_mod_mul_distr_r (SD.bn_v f1 % S.prime) (SD.bn_v r) S.prime

//--------------------

val lemma_mul1_carry_bound: f1:felem -> f2:uint64 ->
  Lemma (let c, r = mul1 f1 f2 in v c <= v f2)

let lemma_mul1_carry_bound f1 f2 =
  let c0, r0 = mul1 f1 f2 in
  assert (SD.bn_v r0 + v c0 * pow2 256 == SD.bn_v f1 * v f2);
  SD.bn_eval_bound f1 4;
  SD.bn_eval_bound r0 4;
  if v f2 = 0 then
    assert (v c0 = 0)
  else
    lemma_carry_bound (SD.bn_v r0) (v c0) 0 (SD.bn_v f1) (v f2)


let fmul14_lemma f1 f2 =
  let c0, r0 = mul1 f1 f2 in
  assert (SD.bn_v r0 + v c0 * pow2 256 == SD.bn_v f1 * v f2);
  lemma_mul1_carry_bound f1 f2;
  assert (v c0 <= v f2);
  Math.Lemmas.lemma_mult_le_right prime_c (v c0 + 1) (pow2 17);
  assert ((v c0 + 1) * prime_c <= pow2 17 * prime_c);
  assert_norm (pow2 17 * prime_c < pow2 64);
  assert ((v c0 + 1) * prime_c < pow2 64);

  let out = carry_pass_small r0 c0 in
  calc (==) {
    SD.bn_v out % S.prime;
    (==) { carry_pass_small_lemma r0 c0 }
    (SD.bn_v r0 + v c0 * pow2 256) % S.prime;
    (==) { }
    (SD.bn_v f1 * v f2) % S.prime;
    (==) {Math.Lemmas.lemma_mod_mul_distr_l (SD.bn_v f1) (v f2) S.prime }
    (SD.bn_v f1 % S.prime * v f2) % S.prime;
    }

//------------------

let fsqr4_lemma f =
  let tmp = sqr4 f in
  let out = carry_wide tmp in
  carry_wide_lemma tmp;
  Math.Lemmas.lemma_mod_mul_distr_l (SD.bn_v f) (SD.bn_v f) S.prime;
  Math.Lemmas.lemma_mod_mul_distr_r (SD.bn_v f % S.prime) (SD.bn_v f) S.prime
