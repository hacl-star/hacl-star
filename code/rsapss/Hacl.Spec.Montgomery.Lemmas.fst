module Hacl.Spec.Montgomery.Lemmas

open FStar.Mul

open Lib.IntTypes
open Lib.LoopCombinators


(**
https://members.loria.fr/PZimmermann/mca/mca-cup-0.5.9.pdf
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

val eea_pow2_odd_k: a:pos -> n:pos ->
  Pure pos
  (requires n % 2 = 1)
  (ensures  fun k -> n * k % pow2 a == 1)

let rec eea_pow2_odd_k a n =
  if a = 1 then 1
  else begin
    let k1 = eea_pow2_odd_k (a - 1) n in
    assert (n * k1 % pow2 (a - 1) == 1);
    let k = if n * k1 % pow2 a < pow2 (a - 1) then k1 else k1 + pow2 (a - 1) in
    eea_pow2_odd_k_lemma a n k1;
    assert (n * k % pow2 a == 1);
    k end


val eea_pow2_odd: a:pos -> n:pos ->
  Pure (tuple2 int int)
  (requires n % 2 = 1)
  (ensures  fun (d, k) -> pow2 a * d == 1 + k * n)

let eea_pow2_odd a n =
  let k = eea_pow2_odd_k a n in
  assert (n * k % pow2 a == 1);
  assert (n * k == n * k / pow2 a * pow2 a + 1);
  let d = n * k / pow2 a in
  assert (n * k == d * pow2 a + 1);
  (- d, - k)


val mont_preconditions_d: rLen:pos -> n:pos{n > 1} -> Lemma
  (requires  n % 2 = 1)
  (ensures  (let d, k = eea_pow2_odd (64 * rLen) n in pow2 (64 * rLen) * d % n == 1))

let mont_preconditions_d rLen n =
  let d, k = eea_pow2_odd (64 * rLen) n in
  calc (==) {
    pow2 (64 * rLen) * d % n;
    (==) { }
    (1 + k * n) % n;
    (==) { Math.Lemmas.modulo_addition_lemma 1 n k }
    1 % n;
    (==) { Math.Lemmas.small_mod 1 n }
    1;
  };
  assert (pow2 (64 * rLen) * d % n == 1)


val mont_preconditions_n0: n:pos{n > 1} -> mu:nat -> Lemma
  (requires (1 + (n % pow2 64) * mu) % pow2 64 == 0)
  (ensures  (1 + n * mu) % pow2 64 == 0)

let mont_preconditions_n0 n mu =
  calc (==) {
    (1 + n * mu) % pow2 64;
    (==) { Math.Lemmas.lemma_mod_plus_distr_r 1 (n * mu) (pow2 64) }
    (1 + n * mu % pow2 64) % pow2 64;
    (==) { Math.Lemmas.lemma_mod_mul_distr_l n mu (pow2 64) }
    (1 + n % pow2 64 * mu % pow2 64) % pow2 64;
    (==) { Math.Lemmas.lemma_mod_plus_distr_r 1 (n % pow2 64 * mu) (pow2 64) }
    (1 + n % pow2 64 * mu) % pow2 64;
    (==) { assert ((1 + (n % pow2 64) * mu) % pow2 64 == 0) }
    0;
  };
  assert ((1 + n * mu) % pow2 64 == 0)

val mont_preconditions:
  nLen:nat -> n:pos{1 < n /\ n < pow2 (64 * nLen)} -> mu:nat -> Lemma
  (requires n % 2 = 1 /\ (1 + (n % pow2 64) * mu) % pow2 64 == 0)
  (ensures
    (let r = pow2 (64 * nLen) in
     let d, _ = eea_pow2_odd (64 * nLen) n in
     r * d % n == 1 /\ n < r /\ (1 + n * mu) % pow2 64 == 0))

let mont_preconditions nLen n mu =
  mont_preconditions_d nLen n;
  mont_preconditions_n0 n mu

///
///  High-level specification of Montgomery arithmetic
///

val mont_reduction_f: rLen:nat -> n:pos -> mu:nat -> i:nat{i < rLen} -> c:nat -> nat
let mont_reduction_f rLen n mu i c =
  let c_i = c / pow2 (64 * i) % pow2 64 in
  let q_i = mu * c_i % pow2 64 in
  let res = c + n * q_i * pow2 (64 * i) in
  res

val mont_reduction: rLen:nat -> n:pos -> mu:nat -> c:nat -> nat
let mont_reduction rLen n mu c =
  let res = repeati rLen (mont_reduction_f rLen n mu) c in
  let res = res / pow2 (64 * rLen) in
  if res < n then res else res - n

val to_mont: rLen:nat -> n:pos -> mu:nat -> a:nat -> nat
let to_mont rLen n mu a =
  let r2 = pow2 (128 * rLen) % n in
  let c = a * r2 in
  mont_reduction rLen n mu c

val from_mont: rLen:nat -> n:pos -> mu:nat -> aM:nat -> nat
let from_mont rLen n mu aM = mont_reduction rLen n mu aM

val mont_mul: rLen:nat -> n:pos -> mu:nat -> a:nat -> b:nat -> nat
let mont_mul rLen n mu a b =
  let c = a * b in
  mont_reduction rLen n mu c


///
///  Lemma (mont_reduction rLen n mu c == c * d % n)
///


val mont_reduction_lemma_step_bound_aux:
  rLen:nat -> n:pos -> q_i:nat{q_i < pow2 64} -> i:pos{i <= rLen} -> c:nat -> res0:nat -> Lemma
  (requires res0 <= c + (pow2 (64 * (i - 1)) - 1) * n)
  (ensures  res0 + n * q_i * pow2 (64 * (i - 1)) <= c + (pow2 (64 * i) - 1) * n)

let mont_reduction_lemma_step_bound_aux rLen n q_i i c res0 =
  let b = pow2 (64 * i) in
  let b1 = pow2 (64 * (i - 1)) in

  calc (<=) {
    res0 + n * q_i * b1;
    (<=) { Math.Lemmas.lemma_mult_le_right b1 q_i (pow2 64 - 1) }
    res0 + n * (pow2 64 - 1) * b1;
    (==) { Math.Lemmas.paren_mul_right n (pow2 64 - 1) b1 }
    res0 + n * ((pow2 64 - 1) * b1);
    (==) { Math.Lemmas.distributivity_sub_left (pow2 64) 1 b1 }
    res0 + n * (pow2 64 * b1 - b1);
    (==) { Math.Lemmas.pow2_plus 64 (64 * (i - 1)) }
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
  rLen:nat -> n:pos -> mu:nat -> i:pos{i <= rLen} -> c:nat -> res0:nat -> Lemma
  (requires res0 <= c + (pow2 (64 * (i - 1)) - 1) * n)
  (ensures  mont_reduction_f rLen n mu (i - 1) res0 <= c + (pow2 (64 * i) - 1) * n)

let mont_reduction_lemma_step_bound rLen n mu i c res0 =
  let res = mont_reduction_f rLen n mu (i - 1) res0 in
  let c_i = res0 / pow2 (64 * (i - 1)) % pow2 64 in
  let q_i = mu * c_i % pow2 64 in
  assert (res == res0 + n * q_i * pow2 (64 * (i - 1)));
  mont_reduction_lemma_step_bound_aux rLen n q_i i c res0;
  assert (res <= c + (pow2 (64 * i) - 1) * n)


val mont_reduction_lemma_step_modr:
  rLen:nat -> n:pos -> mu:nat -> i:pos{i <= rLen} -> c:nat -> res0:nat -> Lemma
  (requires res0 % pow2 (64 * (i - 1)) == 0 /\ (1 + n * mu) % pow2 64 == 0)
  (ensures  mont_reduction_f rLen n mu (i - 1) res0 % pow2 (64 * i) == 0)

let mont_reduction_lemma_step_modr rLen n mu i c res0 =
  let b = pow2 (64 * i) in
  let b1 = pow2 (64 * (i - 1)) in

  let res = mont_reduction_f rLen n mu (i - 1) res0 in
  let c_i = res0 / b1 % pow2 64 in
  let q_i = mu * c_i % pow2 64 in
  assert (res == res0 + n * q_i * b1);
  calc (==) {
    res % b;
    (==) { }
    (res0 + n * q_i * b1) % b;
    (==) { Math.Lemmas.euclidean_division_definition res0 b1 }
    (res0 / b1 * b1 + n * q_i * b1) % b;
    (==) { Math.Lemmas.lemma_mod_plus_distr_l (res0 / b1 * b1) (n * q_i * b1) b }
    (res0 / b1 * b1 % b + n * q_i * b1) % b;
    (==) { Math.Lemmas.pow2_multiplication_modulo_lemma_2 (res0 / b1) (64 * i) (64 * (i - 1)) }
    (res0 / b1 % pow2 64 * b1 + n * q_i * b1) % b;
    (==) { Math.Lemmas.distributivity_add_left (res0 / b1 % pow2 64) (n * q_i) b1 }
    (res0 / b1 % pow2 64 + n * q_i) * b1 % b;
    (==) { Math.Lemmas.pow2_multiplication_modulo_lemma_2 (res0 / b1 % pow2 64 + n * q_i) (64 * i) (64 * (i - 1)) }
    (res0 / b1 % pow2 64 + n * q_i) % pow2 64 * b1;
    (==) { }
    (c_i + n * (mu * c_i % pow2 64)) % pow2 64 * b1;
    (==) { Math.Lemmas.lemma_mod_plus_distr_r c_i (n * (mu * c_i % pow2 64)) (pow2 64) }
    (c_i + n * (mu * c_i % pow2 64) % pow2 64) % pow2 64 * b1;
    (==) { Math.Lemmas.lemma_mod_mul_distr_r n (mu * c_i) (pow2 64); Math.Lemmas.paren_mul_right n mu c_i }
    (c_i + n * mu * c_i % pow2 64) % pow2 64 * b1;
    (==) { Math.Lemmas.lemma_mod_plus_distr_r c_i (n * mu * c_i) (pow2 64) }
    (c_i + n * mu * c_i) % pow2 64 * b1;
    (==) { Math.Lemmas.distributivity_add_left 1 (n * mu) c_i }
    ((1 + n * mu) * c_i) % pow2 64 * b1;
    (==) { Math.Lemmas.lemma_mod_mul_distr_l (1 + n * mu) c_i (pow2 64) }
    ((1 + n * mu) % pow2 64 * c_i) % pow2 64 * b1;
    (==) { assert ((1 + n * mu) % pow2 64 == 0) }
    0;
  };
  assert (res % b == 0)


val mont_reduction_lemma_step_modn:
  rLen:nat -> n:pos -> mu:nat -> i:pos{i <= rLen} -> c:nat -> res0:nat -> Lemma
  (requires res0 % n == c % n)
  (ensures  mont_reduction_f rLen n mu (i - 1) res0 % n == c % n)

let mont_reduction_lemma_step_modn rLen n mu i c res0 =
  let res = mont_reduction_f rLen n mu (i - 1) res0 in
  let c_i = res0 / pow2 (64 * (i - 1)) % pow2 64 in
  let q_i = mu * c_i % pow2 64 in
  assert (res == res0 + n * q_i * pow2 (64 * (i - 1)));
  Math.Lemmas.paren_mul_right n q_i (pow2 (64 * (i - 1)));
  Math.Lemmas.modulo_addition_lemma res0 n (q_i * pow2 (64 * (i - 1)))


val mont_reduction_lemma_step:
  rLen:nat -> n:pos -> mu:nat -> i:pos{i <= rLen} -> c:nat -> res0:nat -> Lemma
  (requires
    res0 % n == c % n /\ res0 % pow2 (64 * (i - 1)) == 0 /\
    res0 <= c + (pow2 (64 * (i - 1)) - 1) * n /\ (1 + n * mu) % pow2 64 == 0)
  (ensures  (let res = mont_reduction_f rLen n mu (i - 1) res0 in
    res % n == c % n /\ res % pow2 (64 * i) == 0 /\ res <= c + (pow2 (64 * i) - 1) * n))

let mont_reduction_lemma_step rLen n mu i c res0 =
  mont_reduction_lemma_step_bound rLen n mu i c res0;
  mont_reduction_lemma_step_modr rLen n mu i c res0;
  mont_reduction_lemma_step_modn rLen n mu i c res0


val mont_reduction_loop_lemma: rLen:nat -> n:pos -> mu:nat -> i:nat{i <= rLen} -> c:nat -> Lemma
  (requires (1 + n * mu) % pow2 64 == 0)
  (ensures  (let res = repeati i (mont_reduction_f rLen n mu) c in
    res % n == c % n /\ res % pow2 (64 * i) == 0 /\ res <= c + (pow2 (64 * i) - 1) * n))

let rec mont_reduction_loop_lemma rLen n mu i c =
  let res : nat = repeati i (mont_reduction_f rLen n mu) c in
  if i = 0 then
    eq_repeati0 i (mont_reduction_f rLen n mu) c
  else begin
    unfold_repeati i (mont_reduction_f rLen n mu) c (i - 1);
    let res0 : nat = repeati (i - 1) (mont_reduction_f rLen n mu) c in
    mont_reduction_loop_lemma rLen n mu (i - 1) c;
    mont_reduction_lemma_step rLen n mu i c res0 end


val lemma_fits_aux: c:nat -> r:pos -> n:pos -> Lemma
  (requires c < n * n /\ n < r)
  (ensures (c - n) / r < n)

let lemma_fits_aux c r n =
  assert (c < r * n);
  assert (c / r < n);
  Math.Lemmas.lemma_div_le (c - n) c r


val mont_mult_lemma_fits_aux: rLen:nat -> n:pos -> d:int -> mu:nat -> c:nat -> Lemma
  (requires
    (1 + n * mu) % pow2 64 == 0 /\ pow2 (64 * rLen) * d % n == 1 /\
     n < pow2 (64 * rLen) /\ c < n * n)
  (ensures
    (let res : nat = repeati rLen (mont_reduction_f rLen n mu) c in
     res / pow2 (64 * rLen) < 2 * n))

let mont_mult_lemma_fits_aux rLen n d mu c =
  let r = pow2 (64 * rLen) in
  let res : nat = repeati rLen (mont_reduction_f rLen n mu) c in
  mont_reduction_loop_lemma rLen n mu rLen c;
  assert (res <= c + (r - 1) * n /\ res % r == 0);
  Math.Lemmas.lemma_div_le res (c + (r - 1) * n) r;
  assert (res / r <= (c + (r - 1) * n) / r);
  calc (<) {
    (c + (r - 1) * n) / r;
    (==) { Math.Lemmas.distributivity_sub_left r 1 n }
    (c - n + r * n) / r;
    (==) { Math.Lemmas.lemma_div_plus (c - n) n r }
    (c - n) / r + n;
    (<) { lemma_fits_aux c r n }
    n + n;
  };
  assert (res / r < 2 * n)


val mont_mult_lemma_fits: rLen:nat -> n:pos -> d:int -> mu:nat -> c:nat -> Lemma
  (requires
    (1 + n * mu) % pow2 64 == 0 /\ pow2 (64 * rLen) * d % n == 1 /\
     n < pow2 (64 * rLen) /\ c < n * n)
  (ensures mont_reduction rLen n mu c < n)

let mont_mult_lemma_fits rLen n d mu c =
  let r = pow2 (64 * rLen) in
  let res : nat = repeati rLen (mont_reduction_f rLen n mu) c in
  let res = res / r in
  mont_mult_lemma_fits_aux rLen n d mu c;
  let res1 = if res < n then res else res - n in
  assert (res1 < n)


val mont_reduction_lemma: rLen:nat -> n:pos -> d:int-> mu:nat -> c:nat -> Lemma
  (requires
    (1 + n * mu) % pow2 64 == 0 /\ pow2 (64 * rLen) * d % n == 1 /\
    n < pow2 (64 * rLen) /\ c < n * n)
  (ensures  mont_reduction rLen n mu c == c * d % n)

let mont_reduction_lemma rLen n d mu c =
  let r = pow2 (64 * rLen) in
  let res : nat = repeati rLen (mont_reduction_f rLen n mu) c in

  let r = pow2 (64 * rLen) in
  let res : nat = repeati rLen (mont_reduction_f rLen n mu) c in
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
  assert (res / r % n == c * d % n);

  let res1 = res / r in
  let res2 = if res1 < n then res1 else res1 - n in
  Math.Lemmas.lemma_mod_sub res1 n 1;
  assert (res2 % n == res1 % n);
  mont_mult_lemma_fits rLen n d mu c;
  Math.Lemmas.small_mod res2 n

///
///  Lemma (to_mont rLen n mu a == a * pow2 (64 * rLen) % n)
///

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


val to_mont_lemma: rLen:nat -> n:pos -> d:int-> mu:nat -> a:nat -> Lemma
  (requires
    (1 + n * mu) % pow2 64 == 0 /\ pow2 (64 * rLen) * d % n == 1 /\
    n < pow2 (64 * rLen) /\ a < n)
  (ensures  to_mont rLen n mu a == a * pow2 (64 * rLen) % n)

let to_mont_lemma rLen n d mu a =
  let r = pow2 (64 * rLen) in
  let r2 = pow2 (128 * rLen) % n in
  let c = a * r2 in
  let aM = to_mont rLen n mu a in
  assert (aM == mont_reduction rLen n mu c);
  mont_reduction_lemma rLen n d mu c;
  assert (aM == c * d % n);
  calc (==) {
    c * d % n;
    (==) { }
    a * r2 * d % n;
    (==) { Math.Lemmas.pow2_plus (64 * rLen) (64 * rLen) }
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
  assert (aM == a * r % n)

///
///  Lemma (from_mont rLen n mu aM == aM * d % n)
///

val from_mont_lemma: rLen:nat -> n:pos -> d:int -> mu:nat -> aM:nat -> Lemma
  (requires
    (1 + n * mu) % pow2 64 == 0 /\ pow2 (64 * rLen) * d % n == 1 /\
    n < pow2 (64 * rLen) /\ aM < n)
  (ensures  from_mont rLen n mu aM == aM * d % n)

let from_mont_lemma rLen n d mu aM =
  mont_reduction_lemma rLen n d mu aM
