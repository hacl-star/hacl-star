module Hacl.Spec.Bignum.ModInv64

open FStar.Mul

open Lib.IntTypes
open Lib.LoopCombinators

#reset-options "--z3rlimit 50 --fuel 0 --ifuel 0"

(**
the modular inverse function was taken from
https://github.com/google/boringssl/blob/master/crypto/fipsmodule/bn/montgomery_inv.c *)

val mod_inv_u64_f:
    alpha:uint64
  -> beta:uint64
  -> i:nat{i < 64}
  -> tuple2 uint64 uint64 ->
  tuple2 uint64 uint64

let mod_inv_u64_f alpha beta i (ub, vb) =
  let u_is_odd = u64 0 -. (ub &. u64 1) in
  let beta_if_u_is_odd = beta &. u_is_odd in
  let u = ((ub ^. beta_if_u_is_odd) >>. 1ul) +. (ub &. beta_if_u_is_odd) in

  let alpha_if_u_is_odd = alpha &. u_is_odd in
  let v = (vb >>. 1ul) +. alpha_if_u_is_odd in
  (u, v)

let mod_inv_u64_t (i:nat{i <= 64}) = tuple2 uint64 uint64

let mod_inv_u64 n0 =
  let alpha = u64 1 <<. 63ul in
  let beta = n0 in
  let (u, v) = repeat_gen 64 mod_inv_u64_t (mod_inv_u64_f alpha beta) (u64 1, u64 0) in
  v


// Replace with `a >> 1 + b >> 1 + a & b & 1`?
val add_div_2_nooverflow: a:uint64 -> b:uint64 -> Lemma
  (v (((a ^. b) >>. 1ul) +. (a &. b)) == (v a + v b) / 2 % pow2 64)
let add_div_2_nooverflow a b = admit()


val x_if_u_is_odd: x:uint64 -> u:uint64 -> Lemma
  (let u_is_odd = u64 0 -. (u &. u64 1) in
   v (x &. u_is_odd) == (if v u % 2 = 0 then 0 else v x))

let x_if_u_is_odd x u =
  let u_is_odd = u64 0 -. (u &. u64 1) in
  logand_mask u (u64 1) 1;
  assert (v (u &. u64 1) == v u % 2);
  assert (v u_is_odd == (- v u % 2) % pow2 64);
  assert (v u_is_odd == (if v u % 2 = 0 then 0 else pow2 64 - 1));
  if v u % 2 = 0 then
    logand_zeros x
  else
    logand_ones x


val mod_inv_u64_inv_vb_is_even: n0:uint64 -> i:pos{i <= 64} -> ub0:uint64 -> vb0:uint64 -> Lemma
  (requires
   (let alpha = u64 1 <<. 63ul in let beta = n0 in
    v n0 % 2 = 1 /\ pow2 (64 - i + 1) == v ub0 * 2 * v alpha - v vb0 * v beta))
  (ensures v vb0 % 2 = 0)

let mod_inv_u64_inv_vb_is_even n0 i ub0 vb0 =
  let alpha = u64 1 <<. 63ul in let beta = n0 in
  Math.Lemmas.pow2_multiplication_modulo_lemma_1 1 1 (64 - i + 1);
  assert (pow2 (64 - i + 1) % 2 == 0);
  calc (==) {
    pow2 (64 - i + 1) % 2;
    (==) { }
    (v ub0 * 2 * v alpha - v vb0 * v beta) % 2;
    (==) { Math.Lemmas.lemma_mod_plus_distr_l (v ub0 * 2 * v alpha) (- v vb0 * v beta) 2 }
    (- v vb0 * v beta) % 2;
    (==) { Math.Lemmas.lemma_mod_mul_distr_r (- v vb0) (v beta) 2 }
    (- v vb0) % 2;
    (==) { }
    v vb0 % 2;
    }


val mod_inv_u64_inv_step_even: n0:uint64 -> i:pos{i <= 64} -> ub0:uint64 -> vb0:uint64 -> Lemma
  (requires
   (let alpha = u64 1 <<. 63ul in let beta = n0 in
    v n0 % 2 = 1 /\ v ub0 % 2 = 0 /\
    pow2 (64 - i + 1) == v ub0 * 2 * v alpha - v vb0 * v beta))
  (ensures
   (let alpha = u64 1 <<. 63ul in let beta = n0 in
    let ub = v ub0 / 2 % pow2 64 in
    let vb = v vb0 / 2 % pow2 64 in
    pow2 (64 - i + 1) == 2 * (ub * 2 * v alpha - vb * v beta)))

let mod_inv_u64_inv_step_even n0 i ub0 vb0 =
  let alpha = u64 1 <<. 63ul in let beta = n0 in
  let ub = v ub0 / 2 % pow2 64 in
  let vb = v vb0 / 2 % pow2 64 in

  Math.Lemmas.small_mod (v ub0 / 2) (pow2 64);
  Math.Lemmas.small_mod (v vb0 / 2) (pow2 64);
  assert (ub * 2 * v alpha - vb * v beta == v ub0 / 2 * 2 * v alpha - v vb0 / 2 * v beta);
  calc (==) {
    2 * (ub * 2 * v alpha - vb * v beta);
    (==) { }
    2 * (v ub0 / 2 * 2 * v alpha - v vb0 / 2 * v beta);
    (==) { Math.Lemmas.distributivity_sub_right 2 (v ub0 / 2 * 2 * v alpha) (v vb0 / 2 * v beta) }
    2 * v ub0 / 2 * 2 * v alpha - 2 * (v vb0 / 2) * v beta;
    (==) { Math.Lemmas.div_exact_r (v ub0) 2 }
    v ub0 * 2 * v alpha - 2 * (v vb0 / 2) * v beta;
    (==) { mod_inv_u64_inv_vb_is_even n0 i ub0 vb0; Math.Lemmas.div_exact_r (v vb0) 2 }
    v ub0 * 2 * v alpha - v vb0 * v beta;
    (==) {assert (pow2 (64 - i + 1) == v ub0 * 2 * v alpha - v vb0 * v beta) }
    pow2 (64 - i + 1);
    };
  assert (2 * (ub * 2 * v alpha - vb * v beta) == pow2 (64 - i + 1))


#push-options "--z3rlimit 150"
val mod_inv_u64_inv_step_odd: n0:uint64 -> i:pos{i <= 64} -> ub0:uint64 -> vb0:uint64 -> Lemma
  (requires
   (let alpha = u64 1 <<. 63ul in let beta = n0 in
    v n0 % 2 = 1 /\ v ub0 % 2 = 1 /\
    pow2 (64 - i + 1) == v ub0 * 2 * v alpha - v vb0 * v beta))
  (ensures
   (let alpha = u64 1 <<. 63ul in let beta = n0 in
    let ub = (v ub0 + v beta) / 2 % pow2 64 in
    let vb = (v vb0 / 2 + v alpha) % pow2 64 in
    pow2 (64 - i + 1) == 2 * (ub * 2 * v alpha - vb * v beta)))

let mod_inv_u64_inv_step_odd n0 i ub0 vb0 =
  let alpha = u64 1 <<. 63ul in let beta = n0 in
  let ub = (v ub0 + v beta) / 2 % pow2 64 in
  let vb = (v vb0 / 2 + v alpha) % pow2 64 in

  Math.Lemmas.small_mod ((v ub0 + v beta) / 2) (pow2 64);
  Math.Lemmas.small_mod (v vb0 / 2 + v alpha) (pow2 64);

  calc (==) {
    2 * (ub * 2 * v alpha - vb * v beta);
    (==) { }
    2 * ((v ub0 + v beta) / 2 * 2 * v alpha - (v vb0 / 2 + v alpha) * v beta);
    (==) { Math.Lemmas.distributivity_sub_right 2 ((v ub0 + v beta) / 2 * 2 * v alpha) ((v vb0 / 2 + v alpha) * v beta) }
    2 * (v ub0 + v beta) / 2 * 2 * v alpha - 2 * (v vb0 / 2 + v alpha) * v beta;
    (==) { Math.Lemmas.div_exact_r (v ub0 + v beta) 2 }
    (v ub0 + v beta) * 2 * v alpha - 2 * (v vb0 / 2 + v alpha) * v beta;
    (==) { Math.Lemmas.paren_mul_right 2 (v vb0 / 2 + v alpha) (v beta) }
    (v ub0 + v beta) * 2 * v alpha - 2 * ((v vb0 / 2 + v alpha) * v beta);
    (==) { Math.Lemmas.distributivity_add_left (v vb0 / 2) (v alpha) (v beta) }
    (v ub0 + v beta) * 2 * v alpha - 2 * (v vb0 / 2 * v beta + v alpha * v beta);
    (==) { Math.Lemmas.distributivity_add_right 2 (v vb0 / 2 * v beta) (v alpha * v beta) }
    (v ub0 + v beta) * 2 * v alpha - (2 * (v vb0 / 2) * v beta + 2 * v alpha * v beta);
    (==) { mod_inv_u64_inv_vb_is_even n0 i ub0 vb0; Math.Lemmas.div_exact_r (v vb0) 2 }
    (v ub0 + v beta) * 2 * v alpha - (v vb0 * v beta + 2 * v alpha * v beta);
    (==) { Math.Lemmas.distributivity_add_left (v ub0) (v beta) (2 * v alpha) }
    v ub0 * 2 * v alpha + v beta * 2 * v alpha - (v vb0 * v beta + 2 * v alpha * v beta);
    (==) { }
    v ub0 * 2 * v alpha - v vb0 * v beta;
    (==) { assert (pow2 (64 - i + 1) == v ub0 * 2 * v alpha - v vb0 * v beta) }
    pow2 (64 - i + 1);
  };
  assert (2 * (ub * 2 * v alpha - vb * v beta) == pow2 (64 - i + 1))
#pop-options


val mod_inv_u64_inv_step: n0:uint64 -> i:pos{i <= 64} -> ub0:uint64 -> vb0:uint64 -> Lemma
  (requires
   (let alpha = u64 1 <<. 63ul in let beta = n0 in
    v n0 % 2 = 1 /\ pow2 (64 - i + 1) == v ub0 * 2 * v alpha - v vb0 * v beta))
  (ensures
   (let alpha = u64 1 <<. 63ul in let beta = n0 in
    let (ub, vb) = mod_inv_u64_f alpha beta (i - 1) (ub0, vb0) in
    pow2 (64 - i) == v ub * 2 * v alpha - v vb * v beta))

let mod_inv_u64_inv_step n0 i ub0 vb0 =
  let alpha = u64 1 <<. 63ul in
  let beta = n0 in

  let u_is_odd = u64 0 -. (ub0 &. u64 1) in
  let beta_if_u_is_odd = beta &. u_is_odd in
  let ub = ((ub0 ^. beta_if_u_is_odd) >>. 1ul) +. (ub0 &. beta_if_u_is_odd) in

  let alpha_if_u_is_odd = alpha &. u_is_odd in
  let vb = (vb0 >>. 1ul) +. alpha_if_u_is_odd in
  x_if_u_is_odd beta ub0;
  x_if_u_is_odd alpha ub0;
  assert (v beta_if_u_is_odd == (if v ub0 % 2 = 0 then 0 else v beta));
  assert (v alpha_if_u_is_odd == (if v ub0 % 2 = 0 then 0 else v alpha));
  add_div_2_nooverflow ub0 beta_if_u_is_odd;
  assert (v ub == (v ub0 + v beta_if_u_is_odd) / 2 % pow2 64);
  assert (v ub == (if v ub0 % 2 = 0 then v ub0 / 2 % pow2 64 else (v ub0 + v beta) / 2 % pow2 64));

  Math.Lemmas.lemma_mod_plus_distr_l (v vb0 / 2) (v alpha_if_u_is_odd) (pow2 64);
  assert (v vb == (v vb0 / 2 + v alpha_if_u_is_odd) % pow2 64);
  assert (v vb == (if v ub0 % 2 = 0 then v vb0 / 2 % pow2 64 else (v vb0 / 2 + v alpha) % pow2 64));
  if v ub0 % 2 = 0 then
    mod_inv_u64_inv_step_even n0 i ub0 vb0
  else
    mod_inv_u64_inv_step_odd n0 i ub0 vb0;

  assert (2 * (v ub * 2 * v alpha - v vb * v beta) == pow2 (64 - i + 1));
  Math.Lemmas.cancel_mul_div (v ub * 2 * v alpha - v vb * v beta) 2;
  Math.Lemmas.pow2_minus (64 - i + 1) 1


val mod_inv_u64_inv: n0:uint64 -> i:nat{i <= 64} -> Lemma
  (requires v n0 % 2 = 1)
  (ensures
   (let alpha = u64 1 <<. 63ul in
    let beta = n0 in
    let (ub, vb) = repeat_gen i mod_inv_u64_t (mod_inv_u64_f alpha beta) (u64 1, u64 0) in
    pow2 (64 - i) == v ub * 2 * v alpha - v vb * v beta))

let rec mod_inv_u64_inv n0 i =
  let alpha = u64 1 <<. 63ul in
  let beta = n0 in
  let (ub, vb) = repeat_gen i mod_inv_u64_t (mod_inv_u64_f alpha beta) (u64 1, u64 0) in
  if i = 0 then
    eq_repeat_gen0 i mod_inv_u64_t (mod_inv_u64_f alpha beta) (u64 1, u64 0)
  else begin
    let (ub0, vb0) = repeat_gen (i - 1) mod_inv_u64_t (mod_inv_u64_f alpha beta) (u64 1, u64 0) in
    mod_inv_u64_inv n0 (i - 1);
    assert (pow2 (64 - i + 1) == v ub0 * 2 * v alpha - v vb0 * v beta);
    unfold_repeat_gen i mod_inv_u64_t (mod_inv_u64_f alpha beta) (u64 1, u64 0) (i - 1);
    assert ((ub, vb) == mod_inv_u64_f alpha beta (i - 1) (ub0, vb0));
    mod_inv_u64_inv_step n0 i ub0 vb0;
    () end


let mod_inv_u64_lemma n0 =
  let alpha = u64 1 <<. 63ul in
  let beta = n0 in
  let (ub, vb) = repeat_gen 64 mod_inv_u64_t (mod_inv_u64_f alpha beta) (u64 1, u64 0) in
  mod_inv_u64_inv n0 64;
  calc (==) {
    (1 + v vb * v n0) % pow2 64;
    (==) { }
    (v ub * 2 * v alpha) % pow2 64;
    (==) { Math.Lemmas.pow2_plus 1 63 }
    (v ub * pow2 64) % pow2 64;
    (==) { Math.Lemmas.cancel_mul_mod (v ub) (pow2 64) }
    0;
  };
  assert ((1 + v vb * v n0) % pow2 64 == 0)
