module Hacl.Spec.Bignum.ModInvLimb

open FStar.Mul

open Lib.IntTypes
open Lib.LoopCombinators
open Hacl.Spec.Bignum.Definitions

#reset-options "--z3rlimit 50 --fuel 0 --ifuel 0"

(**
the modular inverse function was taken from
https://github.com/google/boringssl/blob/master/crypto/fipsmodule/bn/montgomery_inv.c *)

val mod_inv_limb_f:
    #t:limb_t
  -> alpha:limb t
  -> beta:limb t
  -> i:nat{i < bits t}
  -> tuple2 (limb t) (limb t) ->
  tuple2 (limb t) (limb t)

let mod_inv_limb_f #t alpha beta i (ub, vb) =
  let u_is_odd = uint #t 0 -. (ub &. uint #t 1) in
  let beta_if_u_is_odd = beta &. u_is_odd in
  let u = ((ub ^. beta_if_u_is_odd) >>. 1ul) +. (ub &. beta_if_u_is_odd) in

  let alpha_if_u_is_odd = alpha &. u_is_odd in
  let v = (vb >>. 1ul) +. alpha_if_u_is_odd in
  (u, v)

let mod_inv_limb_t (t:limb_t) (i:nat{i <= bits t}) = tuple2 (limb t) (limb t)

let mod_inv_limb #t n0 =
  let alpha = uint #t 1 <<. size (bits t - 1) in
  let beta = n0 in
  let (u, v) = repeat_gen (bits t) (mod_inv_limb_t t) (mod_inv_limb_f alpha beta) (uint #t 1, uint #t 0) in
  v


// Replace with `a >> 1 + b >> 1 + a & b & 1`?
val add_div_2_nooverflow: #t:limb_t -> a:limb t -> b:limb t ->
  Lemma (v (((a ^. b) >>. 1ul) +. (a &. b)) == (v a + v b) / 2 % pow2 (bits t))
let add_div_2_nooverflow #t a b = admit()


val x_if_u_is_odd: #t:limb_t -> x:limb t -> u:limb t ->
  Lemma (let u_is_odd = uint #t 0 -. (u &. uint #t 1) in
   v (x &. u_is_odd) == (if v u % 2 = 0 then 0 else v x))

let x_if_u_is_odd #t x u =
  let u_is_odd = uint #t 0 -. (u &. uint #t 1) in
  logand_mask u (uint #t 1) 1;
  assert (v (u &. uint #t 1) == v u % 2);
  assert (v u_is_odd == (- v u % 2) % pow2 (bits t));
  assert (v u_is_odd == (if v u % 2 = 0 then 0 else pow2 (bits t) - 1));
  if v u % 2 = 0 then
    logand_zeros x
  else
    logand_ones x


val mod_inv_limb_inv_vb_is_even:
    #t:limb_t -> n0:limb t
  -> i:pos{i <= bits t} -> ub0:limb t -> vb0:limb t -> Lemma
  (requires
   (let alpha = uint #t #SEC 1 <<. size (bits t - 1) in let beta = n0 in
    v n0 % 2 = 1 /\ pow2 (bits t - i + 1) == v ub0 * 2 * v alpha - v vb0 * v beta))
  (ensures v vb0 % 2 = 0)

let mod_inv_limb_inv_vb_is_even #t n0 i ub0 vb0 =
  let alpha = uint #t #SEC 1 <<. size (bits t - 1) in let beta = n0 in
  Math.Lemmas.pow2_multiplication_modulo_lemma_1 1 1 (bits t - i + 1);
  assert (pow2 (bits t - i + 1) % 2 == 0);
  calc (==) {
    pow2 (bits t - i + 1) % 2;
    (==) { }
    (v ub0 * 2 * v alpha - v vb0 * v beta) % 2;
    (==) { Math.Lemmas.lemma_mod_plus_distr_l (v ub0 * 2 * v alpha) (- v vb0 * v beta) 2 }
    (- v vb0 * v beta) % 2;
    (==) { Math.Lemmas.lemma_mod_mul_distr_r (- v vb0) (v beta) 2 }
    (- v vb0) % 2;
    (==) { }
    v vb0 % 2;
    }


val mod_inv_limb_inv_step_even:
    #t:limb_t -> n0:limb t
  -> i:pos{i <= bits t} -> ub0:limb t -> vb0:limb t -> Lemma
  (requires
   (let alpha = uint #t #SEC 1 <<. size (bits t - 1) in let beta = n0 in
    v n0 % 2 = 1 /\ v ub0 % 2 = 0 /\
    pow2 (bits t - i + 1) == v ub0 * 2 * v alpha - v vb0 * v beta))
  (ensures
   (let alpha = uint #t #SEC 1 <<. size (bits t - 1) in let beta = n0 in
    let ub = v ub0 / 2 % pow2 (bits t) in
    let vb = v vb0 / 2 % pow2 (bits t) in
    pow2 (bits t - i + 1) == 2 * (ub * 2 * v alpha - vb * v beta)))

let mod_inv_limb_inv_step_even #t n0 i ub0 vb0 =
  let pbits = bits t in
  let alpha = uint #t #SEC 1 <<. size (bits t - 1) in let beta = n0 in
  let ub = v ub0 / 2 % pow2 pbits in
  let vb = v vb0 / 2 % pow2 pbits in

  Math.Lemmas.small_mod (v ub0 / 2) (pow2 pbits);
  Math.Lemmas.small_mod (v vb0 / 2) (pow2 pbits);
  assert (ub * 2 * v alpha - vb * v beta == v ub0 / 2 * 2 * v alpha - v vb0 / 2 * v beta);
  calc (==) {
    2 * (ub * 2 * v alpha - vb * v beta);
    (==) { }
    2 * (v ub0 / 2 * 2 * v alpha - v vb0 / 2 * v beta);
    (==) { Math.Lemmas.distributivity_sub_right 2 (v ub0 / 2 * 2 * v alpha) (v vb0 / 2 * v beta) }
    2 * v ub0 / 2 * 2 * v alpha - 2 * (v vb0 / 2) * v beta;
    (==) { Math.Lemmas.div_exact_r (v ub0) 2 }
    v ub0 * 2 * v alpha - 2 * (v vb0 / 2) * v beta;
    (==) { mod_inv_limb_inv_vb_is_even n0 i ub0 vb0; Math.Lemmas.div_exact_r (v vb0) 2 }
    v ub0 * 2 * v alpha - v vb0 * v beta;
    (==) {assert (pow2 (pbits - i + 1) == v ub0 * 2 * v alpha - v vb0 * v beta) }
    pow2 (pbits - i + 1);
    };
  assert (2 * (ub * 2 * v alpha - vb * v beta) == pow2 (pbits - i + 1))


#push-options "--z3rlimit 150"
val mod_inv_limb_inv_step_odd:
    #t:limb_t -> n0:limb t
  -> i:pos{i <= bits t} -> ub0:limb t -> vb0:limb t -> Lemma
  (requires
   (let alpha = uint #t #SEC 1 <<. size (bits t - 1) in let beta = n0 in
    v n0 % 2 = 1 /\ v ub0 % 2 = 1 /\
    pow2 (bits t - i + 1) == v ub0 * 2 * v alpha - v vb0 * v beta))
  (ensures
   (let alpha = uint #t #SEC 1 <<. size (bits t - 1) in let beta = n0 in
    let ub = (v ub0 + v beta) / 2 % pow2 (bits t) in
    let vb = (v vb0 / 2 + v alpha) % pow2 (bits t) in
    pow2 (bits t - i + 1) == 2 * (ub * 2 * v alpha - vb * v beta)))

let mod_inv_limb_inv_step_odd #t n0 i ub0 vb0 =
  let pbits = bits t in
  let alpha = uint #t #SEC 1 <<. size (bits t - 1) in let beta = n0 in
  let ub = (v ub0 + v beta) / 2 % pow2 pbits in
  let vb = (v vb0 / 2 + v alpha) % pow2 pbits in

  calc (==) {
    2 * (ub * 2 * v alpha - vb * v beta);
    (==) { Math.Lemmas.small_mod ((v ub0 + v beta) / 2) (pow2 pbits) }
    2 * ((v ub0 + v beta) / 2 * 2 * v alpha - vb * v beta);
    (==) { Math.Lemmas.small_mod (v vb0 / 2 + v alpha) (pow2 pbits) }
    2 * ((v ub0 + v beta) / 2 * 2 * v alpha - (v vb0 / 2 + v alpha) * v beta);
    (==) { Math.Lemmas.distributivity_sub_right 2 ((v ub0 + v beta) / 2 * 2 * v alpha) ((v vb0 / 2 + v alpha) * v beta) }
    2 * (v ub0 + v beta) / 2 * 2 * v alpha - 2 * (v vb0 / 2 + v alpha) * v beta;
    (==) { Math.Lemmas.div_exact_r (v ub0 + v beta) 2 }
    (v ub0 + v beta) * 2 * v alpha - 2 * (v vb0 / 2 + v alpha) * v beta;
    (==) { Math.Lemmas.paren_mul_right 2 (v vb0 / 2 + v alpha) (v beta) }
    (v ub0 + v beta) * 2 * v alpha - 2 * ((v vb0 / 2 + v alpha) * v beta);
    (==) { Math.Lemmas.distributivity_add_left (v vb0 / 2) (v alpha) (v beta) }
    (v ub0 + v beta) * 2 * v alpha - 2 * (v vb0 / 2 * v beta + v alpha * v beta);
    (==) { Math.Lemmas.distributivity_add_right 2 (v vb0 / 2 * v beta) (v alpha * v beta);
           Math.Lemmas.paren_mul_right 2 (v vb0 / 2) (v beta);
           Math.Lemmas.paren_mul_right 2 (v alpha) (v beta) }
    (v ub0 + v beta) * 2 * v alpha - (2 * (v vb0 / 2) * v beta + 2 * v alpha * v beta);
    (==) { mod_inv_limb_inv_vb_is_even n0 i ub0 vb0; Math.Lemmas.div_exact_r (v vb0) 2 }
    (v ub0 + v beta) * 2 * v alpha - (v vb0 * v beta + 2 * v alpha * v beta);
    (==) { Math.Lemmas.distributivity_add_left (v ub0) (v beta) (2 * v alpha) }
    v ub0 * 2 * v alpha + v beta * 2 * v alpha - (v vb0 * v beta + 2 * v alpha * v beta);
    (==) { Math.Lemmas.paren_mul_right (v beta) 2 (v alpha); Math.Lemmas.swap_mul (v beta) (2 * v alpha) }
    v ub0 * 2 * v alpha + 2 * v alpha * v beta - v vb0 * v beta - 2 * v alpha * v beta;
    (==) { }
    v ub0 * 2 * v alpha - v vb0 * v beta;
    (==) { assert (pow2 (pbits - i + 1) == v ub0 * 2 * v alpha - v vb0 * v beta) }
    pow2 (pbits - i + 1);
  };
  assert (2 * (ub * 2 * v alpha - vb * v beta) == pow2 (pbits - i + 1))
#pop-options


val mod_inv_limb_inv_step:
    #t:limb_t -> n0:limb t
  -> i:pos{i <= bits t} -> ub0:limb t -> vb0:limb t -> Lemma
  (requires
   (let alpha = uint #t #SEC 1 <<. size (bits t - 1) in let beta = n0 in
    v n0 % 2 = 1 /\ pow2 (bits t - i + 1) == v ub0 * 2 * v alpha - v vb0 * v beta))
  (ensures
   (let alpha = uint #t #SEC 1 <<. size (bits t - 1) in let beta = n0 in
    let (ub, vb) = mod_inv_limb_f alpha beta (i - 1) (ub0, vb0) in
    pow2 (bits t - i) == v ub * 2 * v alpha - v vb * v beta))

let mod_inv_limb_inv_step #t n0 i ub0 vb0 =
  let pbits = bits t in
  let alpha = uint #t #SEC 1 <<. size (bits t - 1) in
  let beta = n0 in

  let u_is_odd = uint #t 0 -. (ub0 &. uint #t 1) in
  let beta_if_u_is_odd = beta &. u_is_odd in
  let ub = ((ub0 ^. beta_if_u_is_odd) >>. 1ul) +. (ub0 &. beta_if_u_is_odd) in

  let alpha_if_u_is_odd = alpha &. u_is_odd in
  let vb = (vb0 >>. 1ul) +. alpha_if_u_is_odd in
  x_if_u_is_odd beta ub0;
  x_if_u_is_odd alpha ub0;
  assert (v beta_if_u_is_odd == (if v ub0 % 2 = 0 then 0 else v beta));
  assert (v alpha_if_u_is_odd == (if v ub0 % 2 = 0 then 0 else v alpha));
  add_div_2_nooverflow ub0 beta_if_u_is_odd;
  assert (v ub == (v ub0 + v beta_if_u_is_odd) / 2 % pow2 pbits);
  assert (v ub == (if v ub0 % 2 = 0 then v ub0 / 2 % pow2 pbits else (v ub0 + v beta) / 2 % pow2 pbits));

  Math.Lemmas.lemma_mod_plus_distr_l (v vb0 / 2) (v alpha_if_u_is_odd) (pow2 pbits);
  assert (v vb == (v vb0 / 2 + v alpha_if_u_is_odd) % pow2 pbits);
  assert (v vb == (if v ub0 % 2 = 0 then v vb0 / 2 % pow2 pbits else (v vb0 / 2 + v alpha) % pow2 pbits));
  if v ub0 % 2 = 0 then
    mod_inv_limb_inv_step_even n0 i ub0 vb0
  else
    mod_inv_limb_inv_step_odd n0 i ub0 vb0;

  assert (2 * (v ub * 2 * v alpha - v vb * v beta) == pow2 (pbits - i + 1));
  Math.Lemmas.cancel_mul_div (v ub * 2 * v alpha - v vb * v beta) 2;
  Math.Lemmas.pow2_minus (pbits - i + 1) 1


val mod_inv_limb_inv: #t:limb_t -> n0:limb t -> i:nat{i <= bits t} -> Lemma
  (requires v n0 % 2 = 1)
  (ensures
   (let alpha = uint #t #SEC 1 <<. size (bits t - 1) in
    let beta = n0 in
    let (ub, vb) = repeat_gen i (mod_inv_limb_t t) (mod_inv_limb_f alpha beta) (uint #t 1, uint #t 0) in
    pow2 (bits t - i) == v ub * 2 * v alpha - v vb * v beta))

let rec mod_inv_limb_inv #t n0 i =
  let alpha = uint #t #SEC 1 <<. size (bits t - 1) in
  let beta = n0 in
  let (ub, vb) = repeat_gen i (mod_inv_limb_t t) (mod_inv_limb_f alpha beta) (uint #t 1, uint #t 0) in
  if i = 0 then
    eq_repeat_gen0 i (mod_inv_limb_t t) (mod_inv_limb_f alpha beta) (uint #t 1, uint #t 0)
  else begin
    let (ub0, vb0) = repeat_gen (i - 1) (mod_inv_limb_t t) (mod_inv_limb_f alpha beta) (uint #t 1, uint #t 0) in
    mod_inv_limb_inv n0 (i - 1);
    assert (pow2 (bits t - i + 1) == v ub0 * 2 * v alpha - v vb0 * v beta);
    unfold_repeat_gen i (mod_inv_limb_t t) (mod_inv_limb_f alpha beta) (uint #t 1, uint #t 0) (i - 1);
    assert ((ub, vb) == mod_inv_limb_f alpha beta (i - 1) (ub0, vb0));
    mod_inv_limb_inv_step n0 i ub0 vb0;
    () end


let mod_inv_limb_lemma #t n0 =
  let pbits = bits t in
  let alpha = uint #t #SEC 1 <<. size (bits t - 1) in
  let beta = n0 in
  let (ub, vb) = repeat_gen pbits (mod_inv_limb_t t) (mod_inv_limb_f alpha beta) (uint #t 1, uint #t 0) in
  mod_inv_limb_inv n0 pbits;
  calc (==) {
    (1 + v vb * v n0) % pow2 pbits;
    (==) { }
    (v ub * 2 * v alpha) % pow2 pbits;
    (==) { Math.Lemmas.pow2_plus 1 (pbits - 1) }
    (v ub * pow2 pbits) % pow2 pbits;
    (==) { Math.Lemmas.cancel_mul_mod (v ub) (pow2 pbits) }
    0;
  };
  assert ((1 + v vb * v n0) % pow2 pbits == 0)


let bn_mod_inv_limb_lemma #t #nLen n =
  let n0 = Lib.Sequence.index n 0 in
  let mu = mod_inv_limb n0 in
  bn_eval_index n 0;
  assert (bn_v n % pow2 (bits t) == v n0);
  Math.Lemmas.pow2_modulo_modulo_lemma_1 (bn_v n) 2 (bits t);
  assert (v n0 % 2 = 1); // since bn_v n % 2 = 1
  mod_inv_limb_lemma n0;
  assert ((1 + (bn_v n % pow2 (bits t)) * v mu) % pow2 (bits t) == 0)
