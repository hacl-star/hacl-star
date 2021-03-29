module Hacl.Spec.Montgomery.Lemmas

open FStar.Mul

open Lib.IntTypes
open Lib.LoopCombinators


(**
https://members.loria.fr/PZimmermann/mca/mca-cup-0.5.9.pdf
https://eprint.iacr.org/2011/239.pdf
https://eprint.iacr.org/2017/1057.pdf *)

#reset-options "--z3rlimit 50 --fuel 0 --ifuel 0"

val eea_pow2_odd_k_lemma_d: a:pos -> n:pos -> k1:pos -> Lemma
  (requires n * k1 % pow2 (a - 1) == 1 /\ n % 2 = 1)
  (ensures (let d = n * k1 / pow2 (a - 1) in
    d % 2 == (if n * k1 % pow2 a < pow2 (a - 1) then 0 else 1)))

let eea_pow2_odd_k_lemma_d a n k1 =
  let d = n * k1 / pow2 (a - 1) in
  Math.Lemmas.pow2_modulo_division_lemma_1 (n * k1) (a - 1) a;
  assert (d % 2 == n * k1 % pow2 a / pow2 (a - 1));
  if d % 2 = 0 then begin
    Math.Lemmas.small_division_lemma_2 (n * k1 % pow2 a) (pow2 (a - 1));
    assert (n * k1 % pow2 a < pow2 (a - 1));
    () end


#push-options "--z3rlimit 100"
val eea_pow2_odd_k_lemma: a:pos -> n:pos -> k1:pos -> Lemma
  (requires n * k1 % pow2 (a - 1) == 1 /\ n % 2 = 1)
  (ensures (let k = if n * k1 % pow2 a < pow2 (a - 1) then k1 else k1 + pow2 (a - 1) in
    n * k % pow2 a == 1))

let eea_pow2_odd_k_lemma a n k1 =
  let d = n * k1 / pow2 (a - 1) in
  let k = if n * k1 % pow2 a < pow2 (a - 1) then k1 else k1 + pow2 (a - 1) in
  calc (==) {
    n * k1;
    (==) { Math.Lemmas.euclidean_division_definition (n * k1) (pow2 (a - 1)) }
    1 + d * pow2 (a - 1);
    (==) { Math.Lemmas.euclidean_division_definition d 2 }
    1 + (d / 2 * 2 + d % 2) * pow2 (a - 1);
    (==) { Math.Lemmas.distributivity_add_left (d / 2 * 2) (d % 2) (pow2 (a - 1)) }
    1 + d / 2 * 2 * pow2 (a - 1) + d % 2 * pow2 (a - 1);
    (==) { Math.Lemmas.pow2_plus 1 (a - 1) }
    1 + d / 2 * pow2 a + d % 2 * pow2 (a - 1);
  };

  assert (n * k1 == 1 + d / 2 * pow2 a + d % 2 * pow2 (a - 1));
  if n * k1 % pow2 a < pow2 (a - 1) then begin
    eea_pow2_odd_k_lemma_d a n k1;
    assert (d % 2 = 0);
    calc (==) {
      n * k % pow2 a;
      (==) { }
      (1 + d / 2 * pow2 a) % pow2 a;
      (==) { Math.Lemmas.modulo_addition_lemma 1 (pow2 a) (d / 2) }
      1 % pow2 a;
      (==) { Math.Lemmas.pow2_le_compat a 1; Math.Lemmas.small_mod 1 (pow2 a) }
      1;
    };
    assert (n * k % pow2 a = 1);
    () end
  else begin
    eea_pow2_odd_k_lemma_d a n k1;
    assert (d % 2 = 1);
    assert (n * k1 == 1 + d / 2 * pow2 a + pow2 (a - 1));
    //assert (n * k == 1 + d / 2 * pow2 a + pow2 (a - 1) + n * pow2 (a - 1));
    calc (==) {
      n * k % pow2 a;
      (==) { Math.Lemmas.distributivity_add_right n k1 (pow2 (a - 1)) }
      (n * k1 + n * pow2 (a - 1)) % pow2 a;
      (==) { }
      (1 + pow2 (a - 1) + n * pow2 (a - 1) + d / 2 * pow2 a) % pow2 a;
      (==) { Math.Lemmas.modulo_addition_lemma (1 + pow2 (a - 1) + n * pow2 (a - 1)) (pow2 a) (d / 2) }
      (1 + pow2 (a - 1) + n * pow2 (a - 1)) % pow2 a;
      (==) { Math.Lemmas.distributivity_add_left 1 n (pow2 (a - 1)) }
      (1 + (1 + n) * pow2 (a - 1)) % pow2 a;
      (==) { Math.Lemmas.lemma_div_exact (1 + n) 2 }
      (1 + (1 + n) / 2 * 2 * pow2 (a - 1)) % pow2 a;
      (==) { Math.Lemmas.paren_mul_right ((1 + n) / 2) 2 (pow2 (a - 1)) }
      (1 + (1 + n) / 2 * (2 * pow2 (a - 1))) % pow2 a;
      (==) { Math.Lemmas.pow2_plus 1 (a - 1)}
      (1 + (1 + n) / 2 * pow2 a) % pow2 a;
      (==) { Math.Lemmas.modulo_addition_lemma 1 (pow2 a) ((1 + n) / 2) }
      1 % pow2 a;
      (==) { Math.Lemmas.pow2_le_compat a 1; Math.Lemmas.small_mod 1 (pow2 a) }
      1;
    };
    assert (n * k % pow2 a == 1);
    () end
#pop-options


val eea_pow2_odd_k_lemma_bound: a:pos -> n:pos -> k1:pos -> Lemma
  (requires n * k1 % pow2 (a - 1) == 1 /\ n % 2 = 1 /\ k1 < pow2 (a - 1))
  (ensures (let k = if n * k1 % pow2 a < pow2 (a - 1) then k1 else k1 + pow2 (a - 1) in
    k < pow2 a))

let eea_pow2_odd_k_lemma_bound a n k1 =
  if n * k1 % pow2 a < pow2 (a - 1) then
    Math.Lemmas.pow2_lt_compat a (a - 1)
  else
    Math.Lemmas.pow2_double_sum (a - 1)


val eea_pow2_odd_k: a:pos -> n:pos ->
  Pure pos
  (requires n % 2 = 1)
  (ensures  fun k ->
    n * k % pow2 a == 1 /\ k < pow2 a)

let rec eea_pow2_odd_k a n =
  if a = 1 then 1
  else begin
    let k1 = eea_pow2_odd_k (a - 1) n in
    assert (n * k1 % pow2 (a - 1) == 1);
    let k = if n * k1 % pow2 a < pow2 (a - 1) then k1 else k1 + pow2 (a - 1) in
    eea_pow2_odd_k_lemma a n k1;
    eea_pow2_odd_k_lemma_bound a n k1;
    assert (n * k % pow2 a == 1);
    k end


val eea_pow2_odd: a:pos -> n:pos ->
  Pure (tuple2 int int)
  (requires n % 2 = 1)
  (ensures  fun (d, k) ->
    pow2 a * d == 1 + k * n /\ - d < n)

let eea_pow2_odd a n =
  let k = eea_pow2_odd_k a n in
  assert (n * k % pow2 a == 1);
  assert (n * k == n * k / pow2 a * pow2 a + 1);
  let d = n * k / pow2 a in
  Math.Lemmas.lemma_mult_lt_left n k (pow2 a);
  assert (n * k < n * pow2 a);
  Math.Lemmas.cancel_mul_div n (pow2 a);
  assert (d < n);
  assert (n * k == d * pow2 a + 1);
  (- d, - k)


val mont_preconditions_d: pbits:pos -> rLen:pos -> n:pos{1 < n} -> Lemma
  (requires  n % 2 = 1)
  (ensures  (let d, k = eea_pow2_odd (pbits * rLen) n in pow2 (pbits * rLen) * d % n == 1))

let mont_preconditions_d pbits rLen n =
  let d, k = eea_pow2_odd (pbits * rLen) n in
  calc (==) {
    pow2 (pbits * rLen) * d % n;
    (==) { }
    (1 + k * n) % n;
    (==) { Math.Lemmas.modulo_addition_lemma 1 n k }
    1 % n;
    (==) { Math.Lemmas.small_mod 1 n }
    1;
  };
  assert (pow2 (pbits * rLen) * d % n == 1)


val mont_preconditions_n0: pbits:pos -> n:pos{n > 1} -> mu:nat -> Lemma
  (requires (1 + (n % pow2 pbits) * mu) % pow2 pbits == 0)
  (ensures  (1 + n * mu) % pow2 pbits == 0)

let mont_preconditions_n0 pbits n mu =
  calc (==) {
    (1 + n * mu) % pow2 pbits;
    (==) { Math.Lemmas.lemma_mod_plus_distr_r 1 (n * mu) (pow2 pbits) }
    (1 + n * mu % pow2 pbits) % pow2 pbits;
    (==) { Math.Lemmas.lemma_mod_mul_distr_l n mu (pow2 pbits) }
    (1 + n % pow2 pbits * mu % pow2 pbits) % pow2 pbits;
    (==) { Math.Lemmas.lemma_mod_plus_distr_r 1 (n % pow2 pbits * mu) (pow2 pbits) }
    (1 + n % pow2 pbits * mu) % pow2 pbits;
    (==) { assert ((1 + (n % pow2 pbits) * mu) % pow2 pbits == 0) }
    0;
  };
  assert ((1 + n * mu) % pow2 pbits == 0)


val mont_preconditions: pbits:pos -> rLen:pos -> n:pos{1 < n} -> mu:nat -> Lemma
  (requires
    n % 2 = 1 /\ (1 + (n % pow2 pbits) * mu) % pow2 pbits == 0)
  (ensures
    (let r = pow2 (pbits * rLen) in
     let d, _ = eea_pow2_odd (pbits * rLen) n in
     r * d % n == 1 /\ (1 + n * mu) % pow2 pbits == 0))

let mont_preconditions pbits rLen n mu =
  mont_preconditions_d pbits rLen n;
  mont_preconditions_n0 pbits n mu


///  High-level specification of Montgomery arithmetic

val mont_reduction_f: pbits:pos -> rLen:nat -> n:pos -> mu:nat -> i:nat{i < rLen} -> c:nat -> nat
let mont_reduction_f pbits rLen n mu i c =
  let c_i = c / pow2 (pbits * i) % pow2 pbits in
  let q_i = mu * c_i % pow2 pbits in
  let res = c + n * q_i * pow2 (pbits * i) in
  res

val mont_reduction_loop_div_r: pbits:pos -> rLen:nat -> n:pos -> mu:nat -> c:nat -> nat
let mont_reduction_loop_div_r pbits rLen n mu c =
  let res = repeati rLen (mont_reduction_f pbits rLen n mu) c in
  let res = res / pow2 (pbits * rLen) in
  res

val mont_reduction: pbits:pos -> rLen:nat -> n:pos -> mu:nat -> c:nat -> nat
let mont_reduction pbits rLen n mu c =
  let res = mont_reduction_loop_div_r pbits rLen n mu c in
  if res < n then res else res - n

val to_mont: pbits:pos -> rLen:nat -> n:pos -> mu:nat -> a:nat -> nat
let to_mont pbits rLen n mu a =
  let r2 = pow2 (2 * pbits * rLen) % n in
  let c = a * r2 in
  mont_reduction pbits rLen n mu c

val from_mont: pbits:pos -> rLen:nat -> n:pos -> mu:nat -> aM:nat -> nat
let from_mont pbits rLen n mu aM =
  mont_reduction pbits rLen n mu aM

val mont_mul: pbits:pos -> rLen:nat -> n:pos -> mu:nat -> a:nat -> b:nat -> nat
let mont_mul pbits rLen n mu a b =
  let c = a * b in
  mont_reduction pbits rLen n mu c

val mont_sqr: pbits:pos -> rLen:nat -> n:pos -> mu:nat -> a:nat -> nat
let mont_sqr pbits rLen n mu a =
  mont_mul pbits rLen n mu a a

val mont_one: pbits:pos -> rLen:nat -> n:pos -> mu:nat -> nat
let mont_one pbits rLen n mu =
  let r2 = pow2 (2 * pbits * rLen) % n in
  mont_reduction pbits rLen n mu r2

///  Lemma (let res = mont_reduction_loop_div_r pbits rLen n mu c in
///         res % n == c * d % n /\ res <= (c - n) / r + n)

val mont_reduction_lemma_step_bound_aux:
  pbits:pos -> n:pos -> q_i:nat{q_i < pow2 pbits} -> i:pos -> c:nat -> res0:nat -> Lemma
  (requires res0 <= c + (pow2 (pbits * (i - 1)) - 1) * n)
  (ensures  res0 + n * q_i * pow2 (pbits * (i - 1)) <= c + (pow2 (pbits * i) - 1) * n)

let mont_reduction_lemma_step_bound_aux pbits n q_i i c res0 =
  let b = pow2 (pbits * i) in
  let b1 = pow2 (pbits * (i - 1)) in

  calc (<=) {
    res0 + n * q_i * b1;
    (<=) { Math.Lemmas.lemma_mult_le_right b1 q_i (pow2 pbits - 1) }
    res0 + n * (pow2 pbits - 1) * b1;
    (==) { Math.Lemmas.paren_mul_right n (pow2 pbits - 1) b1 }
    res0 + n * ((pow2 pbits - 1) * b1);
    (==) { Math.Lemmas.distributivity_sub_left (pow2 pbits) 1 b1 }
    res0 + n * (pow2 pbits * b1 - b1);
    (==) { Math.Lemmas.pow2_plus pbits (pbits * (i - 1)) }
    res0 + n * (b - b1);
    (==) { Math.Lemmas.distributivity_sub_right n b b1 }
    res0 + n * b - n * b1;
    (<=) { }
    c + (b1 - 1) * n + n * b - n * b1;
    (==) { Math.Lemmas.distributivity_sub_left b1 1 n }
    c + b1 * n - n + n * b - n * b1;
    (==) { }
    c - n + b * n;
    (==) { Math.Lemmas.distributivity_sub_left b 1 n }
    c + (b - 1) * n;
  }


val mont_reduction_lemma_step_bound:
  pbits:pos -> rLen:nat -> n:pos -> mu:nat -> i:pos{i <= rLen} -> c:nat -> res0:nat -> Lemma
  (requires res0 <= c + (pow2 (pbits * (i - 1)) - 1) * n)
  (ensures  mont_reduction_f pbits rLen n mu (i - 1) res0 <= c + (pow2 (pbits * i) - 1) * n)

let mont_reduction_lemma_step_bound pbits rLen n mu i c res0 =
  let res = mont_reduction_f pbits rLen n mu (i - 1) res0 in
  let c_i = res0 / pow2 (pbits * (i - 1)) % pow2 pbits in
  let q_i = mu * c_i % pow2 pbits in
  assert (res == res0 + n * q_i * pow2 (pbits * (i - 1)));
  mont_reduction_lemma_step_bound_aux pbits n q_i i c res0;
  assert (res <= c + (pow2 (pbits * i) - 1) * n)


val mont_reduction_lemma_step_mod_pbits: pbits:pos -> n:pos -> mu:nat -> c_i:nat -> Lemma
  (requires (1 + n * mu) % pow2 pbits == 0)
  (ensures  (c_i + n * (mu * c_i % pow2 pbits)) % pow2 pbits == 0)

let mont_reduction_lemma_step_mod_pbits pbits n mu c_i =
  let r = pow2 pbits in
  let q_i = mu * c_i % r in
  calc (==) {
    (c_i + n * q_i) % r;
    (==) { Math.Lemmas.lemma_mod_plus_distr_r c_i (n * q_i) r }
    (c_i + n * q_i % r) % r;
    (==) { }
    (c_i + n * (mu * c_i % r) % r) % r;
    (==) { Math.Lemmas.lemma_mod_mul_distr_r n (mu * c_i) r }
    (c_i + n * (mu * c_i) % r) % r;
    (==) { Math.Lemmas.lemma_mod_plus_distr_r c_i (n * (mu * c_i)) r }
    (c_i + n * (mu * c_i)) % r;
    (==) { Math.Lemmas.paren_mul_right n mu c_i }
    (c_i + n * mu * c_i) % r;
    (==) { Math.Lemmas.distributivity_add_left 1 (n * mu) c_i }
    ((1 + n * mu) * c_i) % r;
    (==) { Math.Lemmas.lemma_mod_mul_distr_l (1 + n * mu) c_i r }
    ((1 + n * mu) % r * c_i) % r;
    (==) { assert ((1 + n * mu) % r = 0) }
    0;
  }


val mont_reduction_lemma_step_modr_aux: pbits:pos -> n:pos -> q_i:nat -> i:pos -> res0:nat ->
  Lemma (let b1 = pow2 (pbits * (i - 1)) in
    (res0 / b1 * b1 + n * q_i * b1) % pow2 (pbits * i) == (res0 / b1 % pow2 pbits + n * q_i) % pow2 pbits * b1)

let mont_reduction_lemma_step_modr_aux pbits n q_i i res0 =
  let b1 = pow2 (pbits * (i - 1)) in
  Math.Lemmas.distributivity_sub_right pbits i 1;
  assert (pbits * i - pbits * (i - 1) == pbits);

  calc (==) {
    (res0 / b1 * b1 + n * q_i * b1) % pow2 (pbits * i);
    (==) { Math.Lemmas.distributivity_add_left (res0 / b1) (n * q_i) b1 }
    (res0 / b1 + n * q_i) * b1 % pow2 (pbits * i);
    (==) { Math.Lemmas.pow2_multiplication_modulo_lemma_2 (res0 / b1 + n * q_i) (pbits * i) (pbits * (i - 1)) }
    (res0 / b1 + n * q_i) % pow2 pbits * b1;
    (==) { Math.Lemmas.lemma_mod_plus_distr_l (res0 / b1) (n * q_i) (pow2 pbits) }
    (res0 / b1 % pow2 pbits + n * q_i) % pow2 pbits * b1;
    }


val mont_reduction_lemma_step_modr:
  pbits:pos -> rLen:nat -> n:pos -> mu:nat -> i:pos{i <= rLen} -> res0:nat -> Lemma
  (requires res0 % pow2 (pbits * (i - 1)) == 0 /\ (1 + n * mu) % pow2 pbits == 0)
  (ensures  mont_reduction_f pbits rLen n mu (i - 1) res0 % pow2 (pbits * i) == 0)

let mont_reduction_lemma_step_modr pbits rLen n mu i res0 =
  let b1 = pow2 (pbits * (i - 1)) in

  let res = mont_reduction_f pbits rLen n mu (i - 1) res0 in
  let c_i = res0 / b1 % pow2 pbits in
  let q_i = mu * c_i % pow2 pbits in
  Math.Lemmas.lemma_div_exact res0 b1;
  mont_reduction_lemma_step_modr_aux pbits n q_i i res0;
  mont_reduction_lemma_step_mod_pbits pbits n mu c_i


val mont_reduction_lemma_step_modn:
  pbits:pos -> rLen:nat -> n:pos -> mu:nat -> i:pos{i <= rLen} -> c:nat -> res0:nat -> Lemma
  (requires res0 % n == c % n)
  (ensures  mont_reduction_f pbits rLen n mu (i - 1) res0 % n == c % n)

let mont_reduction_lemma_step_modn pbits rLen n mu i c res0 =
  let res = mont_reduction_f pbits rLen n mu (i - 1) res0 in
  let c_i = res0 / pow2 (pbits * (i - 1)) % pow2 pbits in
  let q_i = mu * c_i % pow2 pbits in
  assert (res == res0 + n * q_i * pow2 (pbits * (i - 1)));
  Math.Lemmas.paren_mul_right n q_i (pow2 (pbits * (i - 1)));
  Math.Lemmas.modulo_addition_lemma res0 n (q_i * pow2 (pbits * (i - 1)))


val mont_reduction_lemma_step:
  pbits:pos -> rLen:nat -> n:pos -> mu:nat -> i:pos{i <= rLen} -> c:nat -> res0:nat -> Lemma
  (requires
    res0 % n == c % n /\ res0 % pow2 (pbits * (i - 1)) == 0 /\
    res0 <= c + (pow2 (pbits * (i - 1)) - 1) * n /\ (1 + n * mu) % pow2 pbits == 0)
  (ensures  (let res = mont_reduction_f pbits rLen n mu (i - 1) res0 in
    res % n == c % n /\ res % pow2 (pbits * i) == 0 /\ res <= c + (pow2 (pbits * i) - 1) * n))

let mont_reduction_lemma_step pbits rLen n mu i c res0 =
  mont_reduction_lemma_step_bound pbits rLen n mu i c res0;
  mont_reduction_lemma_step_modr pbits rLen n mu i res0;
  mont_reduction_lemma_step_modn pbits rLen n mu i c res0


val mont_reduction_loop_lemma: pbits:pos -> rLen:nat -> n:pos -> mu:nat -> i:nat{i <= rLen} -> c:nat -> Lemma
  (requires (1 + n * mu) % pow2 pbits == 0)
  (ensures  (let res = repeati i (mont_reduction_f pbits rLen n mu) c in
    res % n == c % n /\ res % pow2 (pbits * i) == 0 /\ res <= c + (pow2 (pbits * i) - 1) * n))

let rec mont_reduction_loop_lemma pbits rLen n mu i c =
  let res : nat = repeati i (mont_reduction_f pbits rLen n mu) c in
  if i = 0 then
    eq_repeati0 i (mont_reduction_f pbits rLen n mu) c
  else begin
    unfold_repeati i (mont_reduction_f pbits rLen n mu) c (i - 1);
    let res0 : nat = repeati (i - 1) (mont_reduction_f pbits rLen n mu) c in
    mont_reduction_loop_lemma pbits rLen n mu (i - 1) c;
    mont_reduction_lemma_step pbits rLen n mu i c res0 end


val mont_reduction_loop_div_r_fits_lemma: pbits:pos -> rLen:nat -> n:pos -> mu:nat -> c:nat -> Lemma
  (requires (let r = pow2 (pbits * rLen) in
    (1 + n * mu) % pow2 pbits == 0))
  (ensures  (let res = mont_reduction_loop_div_r pbits rLen n mu c in
    let r = pow2 (pbits * rLen) in
    res <= (c - n) / r + n))

let mont_reduction_loop_div_r_fits_lemma pbits rLen n mu c =
  let r = pow2 (pbits * rLen) in
  let res : nat = repeati rLen (mont_reduction_f pbits rLen n mu) c in
  mont_reduction_loop_lemma pbits rLen n mu rLen c;
  assert (res % n == c % n /\ res % r == 0 /\ res <= c + (r - 1) * n);
  Math.Lemmas.lemma_div_le res (c + (r - 1) * n) r;
  assert (res / r <= (c + (r - 1) * n) / r);

  calc (==) {
    (c + (r - 1) * n) / r;
    (==) { Math.Lemmas.distributivity_sub_left r 1 n }
    (c - n + r * n) / r;
    (==) { Math.Lemmas.division_addition_lemma (c - n) r n }
    (c - n) / r + n;
    };
  assert (res / r <= (c - n) / r + n)


val mont_reduction_loop_div_r_eval_lemma: pbits:pos -> rLen:nat -> n:pos -> d:int -> mu:nat -> c:nat -> Lemma
  (requires (let r = pow2 (pbits * rLen) in
    (1 + n * mu) % pow2 pbits == 0 /\ r * d % n == 1))
  (ensures  (let res = mont_reduction_loop_div_r pbits rLen n mu c in
    res % n == c * d % n))

let mont_reduction_loop_div_r_eval_lemma pbits rLen n d mu c =
  let r = pow2 (pbits * rLen) in
  let res : nat = repeati rLen (mont_reduction_f pbits rLen n mu) c in
  mont_reduction_loop_lemma pbits rLen n mu rLen c;
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


let mont_pre (pbits:pos) (rLen:pos) (n:pos) (mu:nat) =
  (1 + n * mu) % pow2 pbits == 0 /\
  1 < n /\ n < pow2 (pbits * rLen) /\ n % 2 = 1

val mont_reduction_loop_div_r_lemma: pbits:pos -> rLen:pos -> n:pos -> mu:nat -> c:nat -> Lemma
  (requires mont_pre pbits rLen n mu)
  (ensures  (let res = mont_reduction_loop_div_r pbits rLen n mu c in
    let r = pow2 (pbits * rLen) in
    let d, _ = eea_pow2_odd (pbits * rLen) n in
    res % n == c * d % n /\ res <= (c - n) / r + n))

let mont_reduction_loop_div_r_lemma pbits rLen n mu c =
  let d, _ = eea_pow2_odd (pbits * rLen) n in
  mont_preconditions_d pbits rLen n;
  mont_reduction_loop_div_r_fits_lemma pbits rLen n mu c;
  mont_reduction_loop_div_r_eval_lemma pbits rLen n d mu c


///  Montgomery multiplication

val lemma_fits_c_lt_rn: c:nat -> r:pos -> n:pos -> Lemma
  (requires c < r * n)
  (ensures (c - n) / r < n)

let lemma_fits_c_lt_rn c r n =
  assert (c < r * n);
  Math.Lemmas.cancel_mul_div n r;
  assert (c / r < n);
  Math.Lemmas.lemma_div_le (c - n) c r


val mont_reduction_lemma: pbits:pos -> rLen:pos -> n:pos -> mu:nat -> c:nat -> Lemma
  (requires
    mont_pre pbits rLen n mu /\ c < pow2 (pbits * rLen) * n)
  (ensures  (let d, _ = eea_pow2_odd (pbits * rLen) n in
    mont_reduction pbits rLen n mu c == c * d % n))

let mont_reduction_lemma pbits rLen n mu c =
  let r = pow2 (pbits * rLen) in
  let d, _ = eea_pow2_odd (pbits * rLen) n in
  let res = mont_reduction_loop_div_r pbits rLen n mu c in
  mont_reduction_loop_div_r_lemma pbits rLen n mu c;
  assert (res % n == c * d % n /\ res <= (c - n) / r + n);

  let res1 = if res < n then res else res - n in
  if res < n then ()
  else begin
    assert (res1 % n == (res - n) % n);
    Math.Lemmas.lemma_mod_sub res n 1;
    assert (res1 % n == res % n);
    assert (res1 <= (c - n) / r);
    lemma_fits_c_lt_rn c r n end;
  Math.Lemmas.small_mod res1 n


val mont_mul_lemma: pbits:pos -> rLen:pos -> n:pos -> mu:nat -> a:nat -> b:nat -> Lemma
  (requires mont_pre pbits rLen n mu /\ a < n /\ b < n)
  (ensures  (let d, _ = eea_pow2_odd (pbits * rLen) n in
    mont_mul pbits rLen n mu a b == a * b * d % n))

let mont_mul_lemma pbits rLen n mu a b =
  let r = pow2 (pbits * rLen) in
  let d, _ = eea_pow2_odd (pbits * rLen) n in
  let res = mont_mul pbits rLen n mu a b in
  Math.Lemmas.lemma_mult_lt_sqr a b n;
  assert (a * b < n * n);
  Math.Lemmas.lemma_mult_lt_right n n r;
  assert (a * b < r * n);
  mont_reduction_lemma pbits rLen n mu (a * b)

///  Lemma (to_mont rLen n mu a == a * r % n)

val lemma_mod_mul_distr3: a:int -> b:int -> c:int -> n:pos -> Lemma
  (a * (b % n) * c % n == a * b * c % n)
let lemma_mod_mul_distr3 a b c n =
  calc (==) {
    a * (b % n) * c % n;
    (==) { }
    (b % n) * a * c % n;
    (==) { Math.Lemmas.paren_mul_right (b % n) a c }
    (b % n) * (a * c) % n;
    (==) { Math.Lemmas.lemma_mod_mul_distr_l b (a * c) n }
    b * (a * c) % n;
    (==) { Math.Lemmas.paren_mul_right b a c }
    a * b * c % n;
  }


val mult_lt_lemma: a:nat -> b:nat -> c:nat -> d:nat -> Lemma
  (requires a < c /\ b < d)
  (ensures  a * b < c * d)
let mult_lt_lemma a b c d = ()


val to_mont_eval_lemma: pbits:pos -> rLen:pos -> n:pos -> mu:nat -> a:nat -> Lemma
  (requires mont_pre pbits rLen n mu)
  (ensures  (let r = pow2 (pbits * rLen) in
    let r2 = pow2 (2 * pbits * rLen) % n in
    let d, _ = eea_pow2_odd (pbits * rLen) n in
    a * r2 * d % n == a * r % n))

let to_mont_eval_lemma pbits rLen n mu a =
  let r = pow2 (pbits * rLen) in
  let r2 = pow2 (2 * pbits * rLen) % n in
  let d, _ = eea_pow2_odd (pbits * rLen) n in
  mont_preconditions_d pbits rLen n;
  let c = a * r2 in
  calc (==) {
    c * d % n;
    (==) { }
    a * r2 * d % n;
    (==) { Math.Lemmas.paren_mul_right 2 pbits rLen;
           Math.Lemmas.pow2_plus (pbits * rLen) (pbits * rLen) }
    a * (r * r % n) * d % n;
    (==) { lemma_mod_mul_distr3 a (r * r) d n }
    a * (r * r) * d % n;
    (==) { Math.Lemmas.paren_mul_right a r r }
    a * r * r * d % n;
    (==) { Math.Lemmas.paren_mul_right (a * r) r d }
    a * r * (r * d) % n;
    (==) { Math.Lemmas.lemma_mod_mul_distr_r (a * r) (r * d) n }
    a * r * (r * d % n) % n;
    (==) { assert (r * d % n == 1) }
    a * r % n;
    };
  assert (c * d % n == a * r % n)


val to_mont_lemma: pbits:pos -> rLen:pos -> n:pos -> mu:nat -> a:nat -> Lemma
  (requires mont_pre pbits rLen n mu /\ a < pow2 (pbits * rLen))
  (ensures  to_mont pbits rLen n mu a == a * pow2 (pbits * rLen) % n)

let to_mont_lemma pbits rLen n mu a =
  let r = pow2 (pbits * rLen) in
  let r2 = pow2 (2 * pbits * rLen) % n in
  let d, _ = eea_pow2_odd (pbits * rLen) n in
  let c = a * r2 in
  let aM = to_mont pbits rLen n mu a in
  assert (aM == mont_reduction pbits rLen n mu c);
  mult_lt_lemma a r2 r n;
  assert (a * r2 < r * n);
  mont_reduction_lemma pbits rLen n mu c;
  assert (aM == c * d % n);
  to_mont_eval_lemma pbits rLen n mu a;
  assert (aM == a * r % n)

///  Lemma (from_mont rLen n mu aM == aM * d % n)

val from_mont_lemma: pbits:pos -> rLen:pos -> n:pos -> mu:nat -> aM:nat -> Lemma
  (requires mont_pre pbits rLen n mu /\ aM < pow2 (pbits * rLen))
  (ensures  (let d, _ = eea_pow2_odd (pbits * rLen) n in
    from_mont pbits rLen n mu aM == aM * d % n))

let from_mont_lemma pbits rLen n mu aM =
  mont_reduction_lemma pbits rLen n mu aM


///  Lemma (mont_one pbits rLen n mu == 1 * r % n)

val mont_one_lemma: pbits:pos -> rLen:pos -> n:pos -> mu:nat -> Lemma
  (requires mont_pre pbits rLen n mu)
  (ensures  mont_one pbits rLen n mu == 1 * pow2 (pbits * rLen) % n)

let mont_one_lemma pbits rLen n mu =
  to_mont_lemma pbits rLen n mu 1


///  Properties of Montgomery arithmetic

// from_mont (to_mont a) = a % n
val lemma_mont_id: n:pos -> r:pos -> d:int{r * d % n == 1} -> a:nat ->
  Lemma (a * r % n * d % n == a % n)
let lemma_mont_id n r d a =
  calc (==) {
    a * r % n * d % n;
    (==) { Math.Lemmas.lemma_mod_mul_distr_l (a * r) d n }
    a * r * d % n;
    (==) { Math.Lemmas.paren_mul_right a r d; Math.Lemmas.lemma_mod_mul_distr_r a (r * d) n }
    a * (r * d % n) % n;
    (==) { assert (r * d % n == 1) }
    a % n;
  }


// to_mont (mont_reduction a) = a % n
val lemma_mont_id1: n:pos -> r:pos -> d:int{r * d % n = 1} -> a:nat ->
  Lemma (a * d % n * r % n == a % n)
let lemma_mont_id1 n r d a =
  calc (==) {
    ((a * d % n) * r) % n;
    (==) { Math.Lemmas.lemma_mod_mul_distr_l (a * d) r n }
    ((a * d) * r) % n;
    (==) { Math.Lemmas.paren_mul_right a d r }
    (a * (d * r)) % n;
    (==) { Math.Lemmas.lemma_mod_mul_distr_r a (d * r) n }
    (a * (d * r % n)) % n;
    (==) { assert (r * d % n = 1) }
    a % n;
  };
  assert (a * d % n * r % n == a % n)


//  one_M * a = a
val lemma_mont_mul_one: n:pos -> r:pos -> d:int{r * d % n = 1} -> a:nat ->
  Lemma (let r0 = 1 * r % n in let r1 = a * r % n in r0 * r1 * d % n == r1 % n)
let lemma_mont_mul_one n r d a =
  let r0 = 1 * r % n in
  let r1 = a * r % n in

  calc (==) {
    r1 * r0 * d % n;
    (==) { Math.Lemmas.paren_mul_right r1 r0 d; Math.Lemmas.lemma_mod_mul_distr_r r1 (r0 * d) n }
    r1 * (r0 * d % n) % n;
    (==) { lemma_mont_id n r d 1 }
    r1 * (1 % n) % n;
    (==) { Math.Lemmas.lemma_mod_mul_distr_r r1 1 n }
    r1 % n;
    }


val from_mont_add_lemma: pbits:pos -> rLen:pos -> n:pos -> mu:nat -> aM:nat -> bM:nat -> Lemma
  (requires
    mont_pre pbits rLen n mu /\
    aM < n /\ bM < n)
  (ensures
   (let cM = (aM + bM) % n in
    let c = from_mont pbits rLen n mu cM in
    let a = from_mont pbits rLen n mu aM in
    let b = from_mont pbits rLen n mu bM in
    c == (a + b) % n))

let from_mont_add_lemma pbits rLen n mu aM bM =
  let r = pow2 (pbits * rLen) in
  let d, _ = eea_pow2_odd (pbits * rLen) n in

  let cM = (aM + bM) % n in
  let c = from_mont pbits rLen n mu cM in
  let a = from_mont pbits rLen n mu aM in
  let b = from_mont pbits rLen n mu bM in

  from_mont_lemma pbits rLen n mu cM;
  assert (c == cM * d % n);

  calc (==) { //c
    cM * d % n;
    (==) { }
    (aM + bM) % n * d % n;
    (==) { Math.Lemmas.lemma_mod_mul_distr_l (aM + bM) d n }
    (aM + bM) * d % n;
    (==) { Math.Lemmas.distributivity_add_left aM bM d }
    (aM * d + bM * d) % n;
    (==) { Math.Lemmas.modulo_distributivity (aM * d) (bM * d) n }
    (aM * d % n + bM * d % n) % n;
    };

  from_mont_lemma pbits rLen n mu aM;
  from_mont_lemma pbits rLen n mu bM


val from_mont_sub_lemma: pbits:pos -> rLen:pos -> n:pos -> mu:nat -> aM:nat -> bM:nat -> Lemma
  (requires
    mont_pre pbits rLen n mu /\
    aM < n /\ bM < n)
  (ensures
   (let cM = (aM - bM) % n in
    let c = from_mont pbits rLen n mu cM in
    let a = from_mont pbits rLen n mu aM in
    let b = from_mont pbits rLen n mu bM in
    c == (a - b) % n))

let from_mont_sub_lemma pbits rLen n mu aM bM =
  let r = pow2 (pbits * rLen) in
  let d, _ = eea_pow2_odd (pbits * rLen) n in

  let cM = (aM - bM) % n in
  let c = from_mont pbits rLen n mu cM in
  let a = from_mont pbits rLen n mu aM in
  let b = from_mont pbits rLen n mu bM in

  from_mont_lemma pbits rLen n mu cM;
  assert (c == cM * d % n);

  calc (==) { //c
    cM * d % n;
    (==) { }
    (aM - bM) % n * d % n;
    (==) { Math.Lemmas.lemma_mod_mul_distr_l (aM - bM) d n }
    (aM - bM) * d % n;
    (==) { Math.Lemmas.distributivity_sub_left aM bM d }
    (aM * d - bM * d) % n;
    (==) { Math.Lemmas.lemma_mod_plus_distr_l (aM * d) (- bM * d) n }
    (aM * d % n - bM * d) % n;
    (==) { Math.Lemmas.lemma_mod_sub_distr (aM * d % n) (bM * d) n }
    (aM * d % n - bM * d % n) % n;
    };

  from_mont_lemma pbits rLen n mu aM;
  from_mont_lemma pbits rLen n mu bM


val from_mont_mul_lemma: pbits:pos -> rLen:pos -> n:pos -> mu:nat -> aM:nat -> bM:nat -> Lemma
  (requires
    mont_pre pbits rLen n mu /\
    aM < n /\ bM < n)
  (ensures
   (let cM = mont_mul pbits rLen n mu aM bM in
    let c = from_mont pbits rLen n mu cM in
    let a = from_mont pbits rLen n mu aM in
    let b = from_mont pbits rLen n mu bM in
    c == a * b % n))

let from_mont_mul_lemma pbits rLen n mu aM bM =
  let r = pow2 (pbits * rLen) in
  let d, _ = eea_pow2_odd (pbits * rLen) n in

  let cM = mont_mul pbits rLen n mu aM bM in
  let c = from_mont pbits rLen n mu cM in
  let a = from_mont pbits rLen n mu aM in
  let b = from_mont pbits rLen n mu bM in

  mont_mul_lemma pbits rLen n mu aM bM;
  assert (cM == aM * bM * d % n);

  from_mont_lemma pbits rLen n mu cM;

  calc (==) { //c
    cM * d % n;
    (==) { }
    (aM * bM * d % n) * d % n;
    (==) { Math.Lemmas.lemma_mod_mul_distr_l (aM * bM * d) d n }
    aM * bM * d * d % n;
    (==) { Math.Lemmas.paren_mul_right aM bM d }
    aM * (bM * d) * d % n;
    (==) {
      Math.Lemmas.paren_mul_right aM (bM * d) d;
      Math.Lemmas.swap_mul (bM * d) d;
      Math.Lemmas.paren_mul_right aM d (bM * d) }
    aM * d * (bM * d) % n;
    (==) { Math.Lemmas.lemma_mod_mul_distr_l (aM * d) (bM * d) n }
    (aM * d % n) * (bM * d) % n;
    (==) { Math.Lemmas.lemma_mod_mul_distr_r (aM * d % n) (bM * d) n }
    (aM * d % n) * (bM * d % n) % n;
    };

  from_mont_lemma pbits rLen n mu aM;
  from_mont_lemma pbits rLen n mu bM


val from_mont_one_lemma: pbits:pos -> rLen:pos -> n:pos -> mu:nat -> Lemma
  (requires
    mont_pre pbits rLen n mu)
  (ensures
   (let oneM = mont_one pbits rLen n mu in
    let one = from_mont pbits rLen n mu oneM in
    one == 1))

let from_mont_one_lemma pbits rLen n mu =
  let r = pow2 (pbits * rLen) in
  let d, _ = eea_pow2_odd (pbits * rLen) n in
  mont_preconditions_d pbits rLen n;

  let oneM = mont_one pbits rLen n mu in
  mont_one_lemma pbits rLen n mu;
  assert (oneM == r % n);
  let one = from_mont pbits rLen n mu oneM in
  from_mont_lemma pbits rLen n mu oneM;
  assert (one == oneM * d % n);
  assert (one == (r % n) * d % n);
  lemma_mont_id n r d 1;
  assert (one == 1 % n);
  Math.Lemmas.small_mod 1 n


val from_to_mont_lemma: pbits:pos -> rLen:pos -> n:pos -> mu:nat -> a:nat -> Lemma
  (requires (let r = pow2 (pbits * rLen) in
    mont_pre pbits rLen n mu /\ a < r))
  (ensures
   (let aM = to_mont pbits rLen n mu a in
    let a' = from_mont pbits rLen n mu aM in
    a' == a % n))

let from_to_mont_lemma pbits rLen n mu a =
  let aM = to_mont pbits rLen n mu a in
  let a' = from_mont pbits rLen n mu aM in

  let r = pow2 (pbits * rLen) in
  let d, _ = eea_pow2_odd (pbits * rLen) n in
  mont_preconditions_d pbits rLen n;
  assert (r * d % n == 1);

  to_mont_lemma pbits rLen n mu a;
  assert (aM == a * r % n);

  from_mont_lemma pbits rLen n mu aM;
  assert (a' == aM * d % n);
  lemma_mont_id n r d a;
  assert (a' == a % n)
