module Hacl.Spec.Bignum.Montgomery.Lemmas

open FStar.Mul

open Lib.IntTypes
open Lib.LoopCombinators


(**
https://members.loria.fr/PZimmermann/mca/mca-cup-0.5.9.pdf
https://eprint.iacr.org/2017/1057.pdf *)

#reset-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0"

val smont_reduction_f: rLen:size_nat -> n:pos -> mu:nat -> i:size_nat{i < rLen} -> c:nat -> nat
let smont_reduction_f rLen n mu i c =
  let c_i = c / pow2 (64 * i) % pow2 64 in
  let q_i = mu * c_i % pow2 64 in
  let res = c + n * q_i * pow2 (64 * i) in
  res


val mont_reduction_lemma_step_bound: rLen:size_nat -> n:pos -> mu:nat -> i:size_pos{i <= rLen} -> c:nat -> res0:nat -> Lemma
   (requires res0 <= c + (pow2 (64 * (i - 1)) - 1) * n)
   (ensures (let res = smont_reduction_f rLen n mu (i - 1) res0 in res <= c + (pow2 (64 * i) - 1) * n))

let mont_reduction_lemma_step_bound rLen n mu i c res0 =
  let res = smont_reduction_f rLen n mu (i - 1) res0 in
  let c_i = res0 / pow2 (64 * (i - 1)) % pow2 64 in
  let q_i = mu * c_i % pow2 64 in
  assert (res == res0 + n * q_i * pow2 (64 * (i - 1)));
  calc (<=) {
    res0 + n * q_i * pow2 (64 * (i - 1));
    (<=) { Math.Lemmas.lemma_mult_le_right (pow2 (64 * (i - 1))) q_i (pow2 64 - 1) }
    res0 + n * (pow2 64 - 1) * pow2 (64 * (i - 1));
    (==) { Math.Lemmas.paren_mul_right n (pow2 64 - 1) (pow2 (64 * (i - 1))) }
    res0 + n * ((pow2 64 - 1) * pow2 (64 * (i - 1)));
    (==) { Math.Lemmas.distributivity_sub_left (pow2 64) 1 (pow2 (64 * (i - 1))) }
    res0 + n * (pow2 64 * pow2 (64 * (i - 1)) - pow2 (64 * (i - 1)));
    (==) { Math.Lemmas.pow2_plus 64 (64 * (i - 1)) }
    res0 + n * (pow2 (64 * i) - pow2 (64 * (i - 1)));
    (==) { Math.Lemmas.distributivity_sub_right n (pow2 (64 * i)) (pow2 (64 * (i - 1))) }
    res0 + n * pow2 (64 * i) - n * pow2 (64 * (i - 1));
    (<=) { }
    c + (pow2 (64 * (i - 1)) - 1) * n + n * pow2 (64 * i) - n * pow2 (64 * (i - 1));
    (==) { Math.Lemmas.distributivity_sub_left (pow2 (64 * (i - 1))) 1 n }
    c + pow2 (64 * (i - 1)) * n - n + n * pow2 (64 * i) - n * pow2 (64 * (i - 1));
    (==) { }
    c - n + pow2 (64 * i) * n;
    (==) { Math.Lemmas.distributivity_sub_left (pow2 (64 * i)) 1 n }
    c + (pow2 (64 * i) - 1) * n;
  };
  assert (res <= c + (pow2 (64 * i) - 1) * n)


val mont_reduction_lemma_step_modr: rLen:size_nat -> n:pos -> mu:nat -> i:size_pos{i <= rLen} -> c:nat -> res0:nat -> Lemma
   (requires (res0 % pow2 (64 * (i - 1)) == 0 /\ (1 + n * mu) % pow2 64 == 0))
   (ensures (let res = smont_reduction_f rLen n mu (i - 1) res0 in res % pow2 (64 * i) == 0))

let mont_reduction_lemma_step_modr rLen n mu i c res0 =
  let res = smont_reduction_f rLen n mu (i - 1) res0 in
  let c_i = res0 / pow2 (64 * (i - 1)) % pow2 64 in
  let q_i = mu * c_i % pow2 64 in
  assert (res == res0 + n * q_i * pow2 (64 * (i - 1)));
  calc (==) {
    res % pow2 (64 * i);
    (==) { }
    (res0 + n * q_i * pow2 (64 * (i - 1))) % pow2 (64 * i);
    (==) { Math.Lemmas.euclidean_division_definition res0 (pow2 (64 * (i -1))) }
    (res0 / pow2 (64 * (i - 1)) * pow2 (64 * (i - 1)) + n * q_i * pow2 (64 * (i - 1))) % pow2 (64 * i);
    (==) { Math.Lemmas.lemma_mod_plus_distr_l (res0 / pow2 (64 * (i -1)) * pow2 (64 * (i -1))) (n * q_i * pow2 (64 * (i - 1))) (pow2 (64 * i)) }
    (res0 / pow2 (64 * (i - 1)) * pow2 (64 * (i - 1)) % pow2 (64 * i) + n * q_i * pow2 (64 * (i - 1))) % pow2 (64 * i);
    (==) { Math.Lemmas.pow2_multiplication_modulo_lemma_2 (res0 / pow2 (64 * (i -1))) (64 * i) (64 * (i - 1)) }
    (res0 / pow2 (64 * (i - 1)) % pow2 64 * pow2 (64 * (i - 1)) + n * q_i * pow2 (64 * (i - 1))) % pow2 (64 * i);
    (==) { Math.Lemmas.distributivity_add_left (res0 / pow2 (64 * (i - 1)) % pow2 64) (n * q_i) (pow2 (64 * (i - 1))) }
    (res0 / pow2 (64 * (i - 1)) % pow2 64 + n * q_i) * pow2 (64 * (i - 1)) % pow2 (64 * i);
    (==) { Math.Lemmas.pow2_multiplication_modulo_lemma_2 (res0 / pow2 (64 * (i - 1)) % pow2 64 + n * q_i) (64 * i) (64 * (i - 1)) }
    (res0 / pow2 (64 * (i - 1)) % pow2 64 + n * q_i) % pow2 64 * pow2 (64 * (i - 1));
    (==) { }
    (c_i + n * (mu * c_i % pow2 64)) % pow2 64 * pow2 (64 * (i - 1));
    (==) { Math.Lemmas.lemma_mod_plus_distr_r c_i (n * (mu * c_i % pow2 64)) (pow2 64) }
    (c_i + n * (mu * c_i % pow2 64) % pow2 64) % pow2 64 * pow2 (64 * (i - 1));
    (==) { Math.Lemmas.lemma_mod_mul_distr_r n (mu * c_i) (pow2 64); Math.Lemmas.paren_mul_right n mu c_i }
    (c_i + n * mu * c_i % pow2 64) % pow2 64 * pow2 (64 * (i - 1));
    (==) { Math.Lemmas.lemma_mod_plus_distr_r c_i (n * mu * c_i) (pow2 64) }
    (c_i + n * mu * c_i) % pow2 64 * pow2 (64 * (i - 1));
    (==) { Math.Lemmas.distributivity_add_left 1 (n * mu) c_i }
    ((1 + n * mu) * c_i) % pow2 64 * pow2 (64 * (i - 1));
    (==) { Math.Lemmas.lemma_mod_mul_distr_l (1 + n * mu) c_i (pow2 64) }
    ((1 + n * mu) % pow2 64 * c_i) % pow2 64 * pow2 (64 * (i - 1));
    (==) { assert ((1 + n * mu) % pow2 64 == 0) }
    0;
  };
  assert (res % pow2 (64 * i) == 0)


val mont_reduction_lemma_step_modn: rLen:size_nat -> n:pos -> mu:nat -> i:size_pos{i <= rLen} -> c:nat -> res0:nat -> Lemma
   (requires res0 % n == c % n)
   (ensures (let res = smont_reduction_f rLen n mu (i - 1) res0 in res % n == c % n))

let mont_reduction_lemma_step_modn rLen n mu i c res0 =
  let res = smont_reduction_f rLen n mu (i - 1) res0 in
  let c_i = res0 / pow2 (64 * (i - 1)) % pow2 64 in
  let q_i = mu * c_i % pow2 64 in
  assert (res == res0 + n * q_i * pow2 (64 * (i - 1)));
  Math.Lemmas.paren_mul_right n q_i (pow2 (64 * (i - 1)));
  Math.Lemmas.modulo_addition_lemma res0 n (q_i * pow2 (64 * (i - 1)))


val mont_reduction_lemma_step: rLen:size_nat -> n:pos -> mu:nat -> i:size_pos{i <= rLen} -> c:nat -> res0:nat -> Lemma
   (requires (res0 % n == c % n /\ res0 % pow2 (64 * (i - 1)) == 0 /\
     res0 <= c + (pow2 (64 * (i - 1)) - 1) * n /\ (1 + n * mu) % pow2 64 == 0))
   (ensures  (let res = smont_reduction_f rLen n mu (i - 1) res0 in
     res % n == c % n /\ res % pow2 (64 * i) == 0 /\ res <= c + (pow2 (64 * i) - 1) * n))
let mont_reduction_lemma_step rLen n mu i c res0 =
  mont_reduction_lemma_step_bound rLen n mu i c res0;
  mont_reduction_lemma_step_modr rLen n mu i c res0;
  mont_reduction_lemma_step_modn rLen n mu i c res0


val mont_reduction_loop_lemma: rLen:size_nat -> n:pos -> mu:nat -> i:size_nat{i <= rLen} -> c:nat -> Lemma
  (requires (1 + n * mu) % pow2 64 == 0)
  (ensures  (let res = repeati i (smont_reduction_f rLen n mu) c in
   res % n == c % n /\ res % pow2 (64 * i) == 0 /\ res <= c + (pow2 (64 * i) - 1) * n))

let rec mont_reduction_loop_lemma rLen n mu i c =
  let res : nat = repeati i (smont_reduction_f rLen n mu) c in
  if i = 0 then begin
    eq_repeati0 i (smont_reduction_f rLen n mu) c;
    () end
  else begin
    unfold_repeati i (smont_reduction_f rLen n mu) c (i - 1);
    let res0 : nat = repeati (i - 1) (smont_reduction_f rLen n mu) c in
    mont_reduction_loop_lemma rLen n mu (i - 1) c;
    mont_reduction_lemma_step rLen n mu i c res0;
    () end


val mont_reduction: rLen:size_nat -> n:pos -> mu:nat -> c:nat -> res:nat
let mont_reduction rLen n mu c =
  let res = repeati rLen (smont_reduction_f rLen n mu) c in
  res / pow2 (64 * rLen)


val mont_reduction_lemma: rLen:size_nat -> n:pos -> d:nat-> mu:nat -> c:nat -> Lemma
  (requires (1 + n * mu) % pow2 64 == 0 /\ pow2 (64 * rLen) * d % n == 1)
  (ensures  (let res = mont_reduction rLen n mu c in res % n == c * d % n))

let mont_reduction_lemma rLen n d mu c =
  let r = pow2 (64 * rLen) in
  let res : nat = repeati rLen (smont_reduction_f rLen n mu) c in
  mont_reduction_loop_lemma rLen n mu rLen c;
  assert (res % n == c % n /\ res % r == 0 /\ res <= c + (r - 1) * n);
  calc (==) {
    res / r % n;
    (==) { assert (r * d % n == 1) }
    res / r * (r * d % n) % n;
    (==) { Math.Lemmas.lemma_mod_mul_distr_r (res / r) (r * d) n }
    res / r * (r * d) % n;
    (==) { Math.Lemmas.paren_mul_right (res / r) r d }
    res / r * r * d % n;
    (==) { Math.Lemmas.div_exact_r res r }
    res * d % n;
    (==) { Math.Lemmas.lemma_mod_mul_distr_l res d n }
    res % n * d % n;
    (==) { assert (res % n == c % n) }
    c % n * d % n;
    (==) { Math.Lemmas.lemma_mod_mul_distr_l c d n }
    c * d % n;
  };
  assert (res / r % n == c * d % n)
