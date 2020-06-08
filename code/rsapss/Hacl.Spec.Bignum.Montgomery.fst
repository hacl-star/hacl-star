module Hacl.Spec.Bignum.Montgomery

open FStar.Mul

open Lib.IntTypes
open Lib.Sequence
open Lib.LoopCombinators

open Hacl.Spec.Bignum.Definitions
open Hacl.Spec.Bignum

friend Hacl.Spec.Bignum // TODO: avoid using a friend mechanism for this module

#reset-options "--z3rlimit 100 --fuel 0 --ifuel 0"

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
    (v ub0 * 2 * v alpha - v vb0 * v beta) % 2;
    (==) { Math.Lemmas.lemma_mod_plus_distr_l (v ub0 * 2 * v alpha) (- v vb0 * v beta) 2 }
    (- v vb0 * v beta) % 2;
    (==) { Math.Lemmas.lemma_mod_mul_distr_r (- v vb0) (v beta) 2 }
    (- v vb0) % 2;
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
    (==) { }
    pow2 (64 - i + 1);
    };
  assert (2 * (ub * 2 * v alpha - vb * v beta) == pow2 (64 - i + 1))

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
    (==) { }
    pow2 (64 - i + 1);
  };
  assert (2 * (ub * 2 * v alpha - vb * v beta) == pow2 (64 - i + 1))


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

val bn_lshift1_mod_n: #len:size_nat -> n:lbignum len -> i:nat -> b:lbignum len -> lbignum len
let bn_lshift1_mod_n #len n i b = bn_add_mod_n n b b

val bn_lshift1_mod_n_lemma: #len:size_nat -> n:lbignum len -> i:nat -> b:lbignum len -> Lemma
  (requires 0 < bn_v n /\ bn_v b < bn_v n)
  (ensures  bn_v (bn_lshift1_mod_n n i b) == 2 * bn_v b % bn_v n)
let bn_lshift1_mod_n_lemma #len n i b =
  bn_add_mod_n_lemma n b b

val bn_mul_by_pow2: len:size_nat -> n:lbignum len -> b:lbignum len -> k:nat -> Lemma
  (requires 0 < bn_v n /\ bn_v b < bn_v n)
  (ensures  bn_v (repeati k (bn_lshift1_mod_n n) b) == pow2 k * bn_v b % bn_v n)
let rec bn_mul_by_pow2 len n b k =
  if k = 0 then eq_repeati0 k (bn_lshift1_mod_n n) b
  else begin
    let res = repeati k (bn_lshift1_mod_n n) b in
    let res0 = repeati (k - 1) (bn_lshift1_mod_n n) b in
    bn_mul_by_pow2 len n b (k - 1);
    assert (bn_v res0 == pow2 (k - 1) * bn_v b % bn_v n);
    unfold_repeati k (bn_lshift1_mod_n n) b (k - 1);
    assert (res == bn_lshift1_mod_n n (k - 1) res0);
    bn_lshift1_mod_n_lemma #len n (k - 1) res0;
    assert (bn_v res == 2 * (pow2 (k - 1) * bn_v b % bn_v n) % bn_v n);
    Math.Lemmas.lemma_mod_mul_distr_r 2 (pow2 (k - 1) * bn_v b) (bn_v n);
    assert (bn_v res == 2 * pow2 (k - 1) * bn_v b % bn_v n);
    Math.Lemmas.pow2_plus 1 (k - 1) end


let precomp_r2_mod_n #nLen modBits n =
  let c = create nLen (u64 0) in
  let c0 = bn_bit_set c (modBits - 1) in // c0 == pow2 (modBits - 1)
  // pow2 (128 * (nLen + 1)) / pow2 (modBits - 1) == pow2 (128 * nLen + 129 - modBits)

  repeati (128 * nLen + 129 - modBits) (bn_lshift1_mod_n n) c0


let precomp_r2_mod_n_lemma #nLen modBits n =
  let c = create nLen (u64 0) in
  let c0 = bn_bit_set c (modBits - 1) in
  bn_eval_zeroes nLen nLen;
  bn_bit_set_lemma c (modBits - 1);
  assert (bn_v c0 == pow2 (modBits - 1));
  let res = repeati (128 * nLen + 129 - modBits) (bn_lshift1_mod_n n) c0 in
  bn_mul_by_pow2 nLen n c0 (128 * nLen + 129 - modBits);
  assert (bn_v res == pow2 (128 * nLen + 129 - modBits) * pow2 (modBits - 1) % bn_v n);
  Math.Lemmas.pow2_plus (128 * nLen + 129 - modBits) (modBits - 1);
  assert (bn_v res == pow2 (128 * nLen + 128) % bn_v n)

///
///  Low-level specification of Montgomery arithmetic
///

val mont_reduction_f:
    #nLen:size_nat
  -> #rLen:size_nat{rLen = nLen + 1 /\ rLen + rLen <= max_size_t}
  -> n:lbignum nLen
  -> mu:uint64
  -> j:size_nat{j < rLen}
  -> acc:lbignum (rLen + rLen) ->
  lbignum (rLen + rLen)

let mont_reduction_f #nLen #rLen n mu j acc =
  let qj = mu *. acc.[j] in
  let c, res1 = bn_mul1_lshift_add #nLen #(rLen + rLen) n qj j acc in

  let res2 = slice res1 (j + nLen) (rLen + rLen) in
  let _, res3 = bn_add res2 (create 1 c) in
  update_sub res1 (j + nLen) (rLen + rLen - j - nLen) res3


let mont_reduction #nLen #rLen n mu c =
  let c = repeati rLen (mont_reduction_f #nLen #rLen n mu) c in
  bn_rshift c rLen


let to_mont #nLen #rLen n mu r2 a =
  let c = bn_mul a r2 in // c = a * r2
  let tmp = create (rLen + rLen) (u64 0) in
  let tmp = update_sub tmp 0 (nLen + nLen) c in
  mont_reduction #nLen #rLen n mu tmp // aM = c % n


let from_mont #nLen #rLen n mu aM =
  let tmp = create (rLen + rLen) (u64 0) in
  let tmp = update_sub tmp 0 rLen aM in
  let a' = mont_reduction #nLen #rLen n mu tmp in
  sub a' 0 nLen


let mont_mul #nLen #rLen n mu aM bM =
  let c = bn_mul aM bM in // c = aM * bM
  mont_reduction n mu c // resM = c % n



val mont_reduction_f_carry:
    #nLen:size_nat
  -> #rLen:size_nat{rLen = nLen + 1 /\ rLen + rLen <= max_size_t}
  -> n:lbignum nLen
  -> mu:uint64
  -> j:size_nat{j < rLen}
  -> acc:lbignum (rLen + rLen) ->
  uint64 & lbignum (rLen + rLen)

let mont_reduction_f_carry #nLen #rLen n mu j acc =
  let qj = mu *. acc.[j] in
  let c, res1 = bn_mul1_lshift_add #nLen #(rLen + rLen) n qj j acc in

  let res2 = slice res1 (j + nLen) (rLen + rLen) in
  let c1, res3 = bn_add res2 (create 1 c) in
  c1, update_sub res1 (j + nLen) (rLen + rLen - j - nLen) res3


val mont_reduction_f_lemma_bound:
    #nLen:size_nat
  -> #rLen:size_nat{rLen = nLen + 1 /\ rLen + rLen <= max_size_t}
  -> n:lbignum nLen
  -> qj:uint64
  -> c:lbignum (rLen + rLen)
  -> j:size_nat{j < rLen}
  -> acc:lbignum (rLen + rLen) -> Lemma
  (requires
    0 < bn_v n /\ bn_v n < pow2 (64 * nLen) /\
    bn_v c < 4 * bn_v n * bn_v n /\
    bn_v acc <= bn_v c + (pow2 (64 * j) - 1) * bn_v n)
  (ensures
    bn_v acc + bn_v n * v qj * pow2 (64 * j) <= bn_v c + (pow2 (64 * (j + 1)) - 1) * bn_v n /\
    bn_v acc + bn_v n * v qj * pow2 (64 * j) < pow2 (128 * rLen))

let mont_reduction_f_lemma_bound #nLen #rLen n qj c j acc =
  M.mont_reduction_lemma_step_bound_aux rLen (bn_v n) (v qj) (j + 1) (bn_v c) (bn_v acc);
  calc (<) {
    bn_v c + (pow2 (64 * (j + 1)) - 1) * bn_v n;
    (<) { Math.Lemmas.pow2_le_compat (64 * rLen) (64 * (j + 1)) }
    bn_v c + pow2 (64 * rLen) * bn_v n;
    (<) { }
    4 * bn_v n * bn_v n + pow2 (64 * rLen) * bn_v n;
    (<) { M.mont_preconditions_rLen nLen (bn_v n);
      Math.Lemmas.lemma_mult_lt_right (bn_v n) (4 * bn_v n) (pow2 (64 * (nLen + 1))) }
    pow2 (64 * rLen) * bn_v n + pow2 (64 * rLen) * bn_v n;
    (==) { Math.Lemmas.pow2_plus 1 (64 * rLen) }
    pow2 (1 + 64 * rLen) * bn_v n;
    (<) { Math.Lemmas.lemma_mult_lt_left (pow2 (1 + 64 * rLen)) (bn_v n) (pow2 (64 * nLen)) }
    pow2 (1 + 64 * rLen) * pow2 (64 * nLen);
    (==) { Math.Lemmas.pow2_plus (1 + 64 * rLen) (64 * nLen) }
    pow2 (1 + 64 * rLen + 64 * nLen);
    (<) { Math.Lemmas.pow2_lt_compat (64 * rLen + 64 * rLen) (1 + 64 * rLen + 64 * nLen) }
    pow2 (128 * rLen);
  };
  assert (bn_v c + (pow2 (64 * (j + 1)) - 1) * bn_v n < pow2 (128 * rLen))


val mont_reduction_f_lemma_aux:
  nLen:nat -> resLen:nat{resLen == nLen + nLen + 2} -> a:nat -> b:nat -> c:nat -> j:nat{j <= nLen} -> Lemma
  (pow2 (64 * (nLen + j)) * (a + b - c * pow2 (64 * (resLen - j - nLen))) + pow2 (64 * resLen) * c ==
   pow2 (64 * (nLen + j)) * a + pow2 (64 * (nLen + j)) * b)
let mont_reduction_f_lemma_aux nLen resLen a b c j =
  calc (==) {
    pow2 (64 * (nLen + j)) * (a + b - c * pow2 (64 * (resLen - j - nLen)));
    (==) { Math.Lemmas.distributivity_sub_right (pow2 (64 * (nLen + j))) (a + b) (c * pow2 (64 * (resLen - j - nLen))) }
    pow2 (64 * (nLen + j)) * (a + b) - pow2 (64 * (nLen + j)) * c * pow2 (64 * (resLen - j - nLen));
    (==) { Math.Lemmas.distributivity_add_right (pow2 (64 * (nLen + j))) a b }
    pow2 (64 * (nLen + j)) * a + pow2 (64 * (nLen + j)) * b - pow2 (64 * (nLen + j)) * c * pow2 (64 * (resLen - j - nLen));
    (==) { Math.Lemmas.paren_mul_right (pow2 (64 * (nLen + j))) (pow2 (64 * (resLen - j - nLen))) c }
    pow2 (64 * (nLen + j)) * a + pow2 (64 * (nLen + j)) * b - pow2 (64 * (nLen + j)) * pow2 (64 * (resLen - j - nLen)) * c;
    (==) { Math.Lemmas.pow2_plus (64 * (nLen + j)) (64 * (resLen - nLen - j)) }
    pow2 (64 * (nLen + j)) * a + pow2 (64 * (nLen + j)) * b - pow2 (64 * resLen) * c;
  };
  assert (pow2 (64 * (nLen + j)) * (a + b - c * pow2 (64 * (resLen - j - nLen))) ==
    pow2 (64 * (nLen + j)) * a + pow2 (64 * (nLen + j)) * b - pow2 (64 * resLen) * c)


val mont_reduction_f_carry_lemma:
    #nLen:size_nat
  -> #rLen:size_nat{rLen = nLen + 1 /\ rLen + rLen <= max_size_t}
  -> n:lbignum nLen
  -> mu:uint64
  -> c:lbignum (rLen + rLen)
  -> j:size_nat{j < rLen}
  -> acc:lbignum (rLen + rLen) -> Lemma
   (let c1, res = mont_reduction_f_carry #nLen #rLen n mu j acc in
    let qj = mu *. acc.[j] in
    bn_v res + pow2 (128 * rLen) * v c1 == bn_v acc + bn_v n * v qj * pow2 (64 * j))

let mont_reduction_f_carry_lemma #nLen #rLen n mu c j acc =
  let resLen = rLen + rLen in
  let qj = mu *. acc.[j] in
  let c, res1 = bn_mul1_lshift_add #nLen #resLen n qj j acc in
  bn_mul1_lshift_add_lemma #nLen #(rLen+rLen) n qj j acc;
  assert (v c * pow2 (64 * (nLen + j)) + eval_ resLen res1 (nLen + j) == eval_ resLen acc (nLen + j) + bn_v n * v qj * pow2 (64 * j));

  let res2 = slice res1 (j + nLen) resLen in
  let acc2 = slice acc (j + nLen) resLen in
  assert (res1 == update_sub acc j nLen (snd (Hacl.Spec.Bignum.Multiplication.bn_mul1_add_in_place #nLen n qj (sub acc j nLen))));
  eq_intro res2 acc2;
  assert (res2 == acc2);

  let c1, res3 = bn_add res2 (create 1 c) in
  bn_add_lemma res2 (create 1 c);
  bn_eval_create1 c;
  assert (v c1 * pow2 (64 * (resLen - j - nLen)) + bn_v res3 == bn_v acc2 + v c);

  let res4 = update_sub res1 (j + nLen) (resLen - j - nLen) res3 in
  calc (==) {
    bn_v res4 + pow2 (64 * resLen) * v c1;
    (==) { bn_eval_split_i res4 (j + nLen) }
    bn_v (slice res4 0 (j + nLen)) + pow2 (64 * (j + nLen)) * bn_v (slice res4 (j + nLen) resLen) + pow2 (64 * resLen) * v c1;
    (==) { }
    bn_v (slice res4 0 (j + nLen)) + pow2 (64 * (j + nLen)) * bn_v res3 + pow2 (64 * resLen) * v c1;
    (==) { eq_intro (sub res4 0 (j + nLen)) (sub res1 0 (j + nLen)) }
    bn_v (slice res1 0 (j + nLen)) + pow2 (64 * (j + nLen)) * bn_v res3 + pow2 (64 * resLen) * v c1;
    (==) { }
    bn_v (slice res1 0 (nLen + j)) + pow2 (64 * (nLen + j)) * (bn_v acc2 + v c - v c1 * pow2 (64 * (resLen - j - nLen))) + pow2 (64 * resLen) * v c1;
    (==) { bn_eval_extensionality_j res1 (slice res1 0 (nLen + j)) (nLen + j) }
    eval_ resLen res1 (nLen + j) + pow2 (64 * (nLen + j)) * (bn_v acc2 + v c - v c1 * pow2 (64 * (resLen - j - nLen))) + pow2 (64 * resLen) * v c1;
    (==) { }
    eval_ resLen acc (nLen + j) + bn_v n * v qj * pow2 (64 * j) - v c * pow2 (64 * (nLen + j)) +
      pow2 (64 * (nLen + j)) * (bn_v acc2 + v c - v c1 * pow2 (64 * (resLen - j - nLen))) + pow2 (64 * resLen) * v c1;
    (==) { mont_reduction_f_lemma_aux nLen resLen (bn_v acc2) (v c) (v c1) j }
    eval_ resLen acc (nLen + j) + bn_v n * v qj * pow2 (64 * j) + pow2 (64 * (nLen + j)) * bn_v acc2;
    (==) { bn_eval_extensionality_j acc (slice acc 0 (nLen + j)) (nLen + j) }
    bn_v (slice acc 0 (nLen + j)) + bn_v n * v qj * pow2 (64 * j) + pow2 (64 * (nLen + j)) * bn_v acc2;
    (==) { }
    bn_v (slice acc 0 (nLen + j)) + pow2 (64 * (nLen + j)) * bn_v acc2 + bn_v n * v qj * pow2 (64 * j);
    (==) { bn_eval_split_i acc (nLen + j) }
    bn_v acc + bn_v n * v qj * pow2 (64 * j);
  };
  assert (bn_v res4 + pow2 (64 * resLen) * v c1 == bn_v acc + bn_v n * v qj * pow2 (64 * j))


val mont_reduction_f_carry_drop_lemma:
    #nLen:size_nat
  -> #rLen:size_nat{rLen = nLen + 1 /\ rLen + rLen <= max_size_t}
  -> n:lbignum nLen
  -> mu:uint64
  -> c:lbignum (rLen + rLen)
  -> j:size_nat{j < rLen}
  -> acc:lbignum (rLen + rLen) -> Lemma
  (requires
    0 < bn_v n /\ bn_v n < pow2 (64 * nLen) /\
    bn_v c < 4 * bn_v n * bn_v n /\
    bn_v acc <= bn_v c + (pow2 (64 * j) - 1) * bn_v n)
  (ensures
   (let res = mont_reduction_f #nLen #rLen n mu j acc in
    bn_v res == bn_v acc + bn_v n * (v mu * v acc.[j] % pow2 64) * pow2 (64 * j) /\
    bn_v res <= bn_v c + (pow2 (64 * (j + 1)) - 1) * bn_v n))

let mont_reduction_f_carry_drop_lemma #nLen #rLen n mu c j acc =
  let c1, res = mont_reduction_f_carry #nLen #rLen n mu j acc in
  let qj = mu *. acc.[j] in
  mont_reduction_f_carry_lemma #nLen #rLen n mu c j acc;
  assert (bn_v res + pow2 (128 * rLen) * v c1 == bn_v acc + bn_v n * v qj * pow2 (64 * j));
  mont_reduction_f_lemma_bound #nLen #rLen n qj c j acc;
  assert (bn_v acc + bn_v n * v qj * pow2 (64 * j) < pow2 (128 * rLen));
  assert (v c1 = 0)


val mont_reduction_f_lemma:
    #nLen:size_nat
  -> #rLen:size_nat{rLen = nLen + 1 /\ rLen + rLen <= max_size_t}
  -> n:lbignum nLen
  -> mu:uint64
  -> c:lbignum (rLen + rLen)
  -> j:size_nat{j < rLen}
  -> acc:lbignum (rLen + rLen) -> Lemma
  (requires
    0 < bn_v n /\ bn_v n < pow2 (64 * nLen) /\
    bn_v c < 4 * bn_v n * bn_v n /\
    bn_v acc <= bn_v c + (pow2 (64 * j) - 1) * bn_v n)
  (ensures
   (let res = mont_reduction_f #nLen #rLen n mu j acc in
    bn_v res == M.smont_reduction_f rLen (bn_v n) (v mu) j (bn_v acc) /\
    bn_v res <= bn_v c + (pow2 (64 * (j + 1)) - 1) * bn_v n))

let mont_reduction_f_lemma #nLen #rLen n mu c j acc =
  let res = mont_reduction_f #nLen #rLen n mu j acc in
  mont_reduction_f_carry_drop_lemma #nLen #rLen n mu c j acc;
  bn_eval_index acc j;
  assert (v acc.[j] == bn_v acc / pow2 (64 * j) % pow2 64)


val mont_reduction_loop_lemma:
    #nLen:size_nat
  -> #rLen:size_nat{rLen = nLen + 1 /\ rLen + rLen <= max_size_t}
  -> n:lbignum nLen
  -> mu:uint64
  -> c:lbignum (rLen + rLen)
  -> j:size_nat{j <= rLen} -> Lemma
  (requires
    0 < bn_v n /\ bn_v n < pow2 (64 * nLen) /\
    bn_v c < 4 * bn_v n * bn_v n)
  (ensures
   (let res = repeati j (mont_reduction_f #nLen #rLen n mu) c in
    bn_v res == repeati j (M.smont_reduction_f rLen (bn_v n) (v mu)) (bn_v c) /\
    bn_v res <= bn_v c + (pow2 (64 * j) - 1) * bn_v n))

let rec mont_reduction_loop_lemma #nLen #rLen n mu c j =
  let res1 = repeati j (mont_reduction_f #nLen #rLen n mu) c in
  let res2 = repeati j (M.smont_reduction_f rLen (bn_v n) (v mu)) (bn_v c) in
  if j = 0 then begin
    eq_repeati0 j (mont_reduction_f #nLen #rLen n mu) c;
    eq_repeati0 j (M.smont_reduction_f rLen (bn_v n) (v mu)) (bn_v c) end
  else begin
    unfold_repeati j (mont_reduction_f #nLen #rLen n mu) c (j - 1);
    unfold_repeati j (M.smont_reduction_f rLen (bn_v n) (v mu)) (bn_v c) (j - 1);
    let res3 = repeati (j - 1) (mont_reduction_f #nLen #rLen n mu) c in
    let res4 = repeati (j - 1) (M.smont_reduction_f rLen (bn_v n) (v mu)) (bn_v c) in
    mont_reduction_loop_lemma #nLen #rLen n mu c (j - 1);
    assert (bn_v res3 == res4);
    assert (res1 == mont_reduction_f #nLen #rLen n mu (j - 1) res3);
    assert (res2 == M.smont_reduction_f rLen (bn_v n) (v mu) (j - 1) res4);
    assert (bn_v res3 <= bn_v c + (pow2 (64 * (j - 1)) - 1) * bn_v n);
    mont_reduction_f_lemma #nLen #rLen n mu c (j - 1) res3;
    assert (bn_v res1 == res2);
    () end


let mont_reduction_lemma #nLen #rLen n mu c =
  let res1 = repeati rLen (mont_reduction_f #nLen #rLen n mu) c in
  mont_reduction_loop_lemma #nLen #rLen n mu c rLen;
  bn_rshift_lemma res1 rLen;
  assert (bn_v (mont_reduction #nLen #rLen n mu c) == M.mont_reduction rLen (bn_v n) (v mu) (bn_v c));
  let d, k = M.eea_pow2_odd (64 * rLen) (bn_v n) in
  M.mont_preconditions nLen (bn_v n) (v mu);
  M.mont_mult_lemma_fits rLen (bn_v n) d (v mu) (bn_v c)


val lemma_mult_lt: a:nat -> b:nat -> c:nat -> d:nat -> Lemma
  (requires a < b /\ c < d)
  (ensures a * c < b * d)
let lemma_mult_lt a b c d = ()


let to_mont_lemma #nLen #rLen n mu r2 a =
  let c = bn_mul a r2 in // c = a * r2
  bn_mul_lemma a r2;
  lemma_mult_lt (bn_v a) (bn_v n) (bn_v r2) (bn_v n);
  assert (bn_v c < bn_v n * bn_v n);

  let tmp = create (rLen + rLen) (u64 0) in
  let tmp = update_sub tmp 0 (nLen + nLen) c in
  bn_eval_update_sub (nLen + nLen) c (rLen + rLen);
  assert (bn_v c == bn_v tmp);

  let aM = mont_reduction #nLen #rLen n mu tmp in // aM = c % n
  mont_reduction_lemma #nLen #rLen n mu tmp;
  assert (bn_v aM == M.mont_reduction rLen (bn_v n) (v mu) (bn_v tmp));

  let d, k = M.eea_pow2_odd (64 * rLen) (bn_v n) in
  M.mont_preconditions nLen (bn_v n) (v mu);
  M.to_mont_lemma_fits rLen (bn_v n) d (v mu) (bn_v a)


val lemma_top_is_zero:
    #nLen:size_nat
  -> #rLen:size_nat{rLen = nLen + 1 /\ rLen + rLen <= max_size_t}
  -> n:lbignum nLen
  -> a:lbignum rLen -> Lemma
  (requires bn_v a <= bn_v n)
  (ensures  bn_v a == eval_ rLen a nLen)

let lemma_top_is_zero #nLen #rLen n a =
  bn_eval_split_i a nLen;
  assert (bn_v a == bn_v (slice a 0 nLen) + pow2 (64 * nLen) * bn_v (slice a nLen rLen));
  bn_eval_bound n nLen;
  assert (bn_v a < pow2 (64 * nLen));
  bn_eval_bound (slice a 0 nLen) nLen;
  assert (bn_v (slice a 0 nLen) < pow2 (64 * nLen));
  assert (bn_v a == bn_v (slice a 0 nLen));
  bn_eval_extensionality_j (slice a 0 nLen) a nLen


let from_mont_lemma #nLen #rLen n mu aM =
  let tmp = create (rLen + rLen) (u64 0) in
  let tmp = update_sub tmp 0 rLen aM in
  bn_eval_update_sub rLen aM (rLen + rLen);
  assert (bn_v tmp == bn_v aM);

  let a' = mont_reduction #nLen #rLen n mu tmp in
  mont_reduction_lemma n mu tmp;
  assert (bn_v a' == M.mont_reduction rLen (bn_v n) (v mu) (bn_v tmp));

  let d, k = M.eea_pow2_odd (64 * rLen) (bn_v n) in
  M.mont_preconditions nLen (bn_v n) (v mu);
  M.from_mont_lemma_fits rLen (bn_v n) d (v mu) (bn_v aM);
  assert (bn_v a' <= bn_v n);

  let res = sub a' 0 nLen in
  bn_eval_extensionality_j a' res nLen;
  assert (eval_ nLen res nLen == eval_ rLen a' nLen);
  assert (bn_v res == eval_ rLen a' nLen);
  lemma_top_is_zero #nLen #rLen n a';
  assert (bn_v a' == eval_ rLen a' nLen);
  assert (bn_v res == M.mont_reduction rLen (bn_v n) (v mu) (bn_v tmp))


let mont_mul_lemma #nLen #rLen n mu aM bM =
  let c = bn_mul aM bM in
  bn_mul_lemma aM bM;
  assert (bn_v c == bn_v aM * bn_v bM);
  Math.Lemmas.lemma_mult_lt_sqr (bn_v aM) (bn_v bM) (2 * bn_v n);
  assert (bn_v c < 4 * bn_v n * bn_v n);
  mont_reduction_lemma #nLen #rLen n mu c
