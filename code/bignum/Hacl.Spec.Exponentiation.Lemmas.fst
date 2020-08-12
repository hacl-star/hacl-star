module Hacl.Spec.Exponentiation.Lemmas

open FStar.Mul
open Lib.NatMod

module M = Hacl.Spec.Montgomery.Lemmas
module Loops = Lib.LoopCombinators


#reset-options "--z3rlimit 50 --fuel 0 --ifuel 0"

///
///  Generic math lemmas
///
val lemma_mul_ass3: a:int -> b:int -> c:int -> Lemma
  (a * b * c == a * c * b)
let lemma_mul_ass3 a b c = ()

val lemma_mul_ass5_aux: a:int -> b:int -> c:int -> d:int -> e:int -> Lemma
  (a * b * c * d * e == a * b * (c * d * e))
let lemma_mul_ass5_aux a b c d e =
  calc (==) {
    a * b * c * d * e;
    (==) { Math.Lemmas.paren_mul_right (a * b) c d }
    a * b * (c * d) * e;
    (==) { Math.Lemmas.paren_mul_right (a * b) (c * d) e }
    a * b * (c * d * e);
  }


val lemma_mul_ass5: a:int -> b:int -> c:int -> d:int -> e:int -> Lemma
  (a * b * (c * d) * e == a * c * (b * d * e))
let lemma_mul_ass5 a b c d e =
  calc (==) {
    a * b * (c * d) * e;
    (==) { Math.Lemmas.paren_mul_right (a * b) (c * d) e }
    a * b * ((c * d) * e);
    (==) { Math.Lemmas.paren_mul_right c d e }
    a * b * (c * d * e);
    (==) { lemma_mul_ass5_aux a b c d e }
    a * b * c * d * e;
    (==) { lemma_mul_ass3 a b c }
    a * c * b * d * e;
    (==) { lemma_mul_ass5_aux a c b d e }
    a * c * (b * d * e);
  }

val lemma_mod_mul_distr_aux: a:int -> b:int -> c:int -> n:pos -> Lemma
  (a * b * c % n == a % n * (b % n) * c % n)
let lemma_mod_mul_distr_aux a b c n =
  calc (==) {
    a * b * c % n;
    (==) { Math.Lemmas.lemma_mod_mul_distr_l (a * b) c n }
    a * b % n * c % n;
    (==) { Math.Lemmas.lemma_mod_mul_distr_l a b n }
    a % n * b % n * c % n;
    (==) { Math.Lemmas.lemma_mod_mul_distr_r (a % n) b n }
    a % n * (b % n) % n * c % n;
    (==) { Math.Lemmas.lemma_mod_mul_distr_l (a % n * (b % n)) c n }
    a % n * (b % n) * c % n;
  }

///
///  High-level specification of Montgomery exponentiation
///

val mod_exp_f: n:pos -> d:int -> bBits:nat -> b:nat{b < pow2 bBits} -> i:nat{i < bBits} -> tuple2 nat nat -> tuple2 nat nat
let mod_exp_f n d bBits b i (aM, accM) =
  let accM = if (b / pow2 i % 2 = 1) then accM * aM * d % n else accM in
  let aM = aM * aM * d % n in
  (aM, accM)

val mod_exp_mont: n:pos -> r:pos -> d:int{r * d % n == 1} -> a:nat -> bBits:nat -> b:nat{b < pow2 bBits} -> nat
let mod_exp_mont n r d a bBits b =
  let aM = a * r % n in
  let accM = 1 * r % n in
  let (aM, accM) = Loops.repeati bBits (mod_exp_f n d bBits b) (aM, accM) in
  let acc = accM * d % n in
  acc


///
///  Lemma (mod_exp_mont n r d a bBits b == pow a b % n)
///

val mod_exp_mont_lemma_step_a:
    n:pos -> d:int
  -> bBits:nat -> b:nat{b < pow2 bBits}
  -> i:pos{i <= bBits}
  -> aM0:nat -> accM0:nat
  -> aM1:nat -> accM1:nat ->
  Lemma
  (requires
    aM1 == pow aM0 (pow2 (i - 1)) * pow d (pow2 (i - 1) - 1) % n /\
    accM1 == pow aM0 (b % pow2 (i - 1)) * accM0 * pow d (b % pow2 (i - 1)) % n)
  (ensures
   (let (aM2, accM2) = mod_exp_f n d bBits b (i - 1) (aM1, accM1) in
    aM2 == pow aM0 (pow2 i) * pow d (pow2 i - 1) % n))

let mod_exp_mont_lemma_step_a n d bBits b i aM0 accM0 aM1 accM1 =
  let b1 = pow2 (i - 1) in
  let pow2i_loc () : Lemma (b1 + b1 == pow2 i) =
    Math.Lemmas.pow2_double_sum (i - 1) in
  let (aM2, accM2) = mod_exp_f n d bBits b (i - 1) (aM1, accM1) in
  assert (aM2 == aM1 * aM1 * d % n);
  calc (==) {
    aM1 * aM1 * d % n;
    (==) { }
    (pow aM0 b1 * pow d (b1 - 1) % n) * (pow aM0 b1 * pow d (b1 - 1) % n) * d % n;
    (==) { lemma_mod_mul_distr_aux (pow aM0 b1 * pow d (b1 - 1)) (pow aM0 b1 * pow d (b1 - 1)) d n }
    pow aM0 b1 * pow d (b1 - 1) * (pow aM0 b1 * pow d (b1 - 1)) * d % n;
    (==) { lemma_mul_ass5 (pow aM0 b1) (pow d (b1 - 1)) (pow aM0 b1) (pow d (b1 - 1)) d }
    pow aM0 b1 * pow aM0 b1 * (pow d (b1 - 1) * pow d (b1 - 1) * d) % n;
    (==) { lemma_pow_add aM0 b1 b1 }
    pow aM0 (b1 + b1) * (pow d (b1 - 1) * pow d (b1 - 1) * d) % n;
    (==) { lemma_pow_add d (b1 - 1) (b1 - 1) }
    pow aM0 (b1 + b1) * (pow d (b1 - 1 + b1 - 1) * d) % n;
    (==) { lemma_pow1 d; lemma_pow_add d (b1 - 1 + b1 - 1) 1 }
    pow aM0 (b1 + b1) * pow d (b1 + b1 - 1) % n;
    (==) { pow2i_loc () }
    pow aM0 (pow2 i) * pow d (pow2 i - 1) % n;
  };
  assert (aM1 * aM1 * d % n == pow aM0 (pow2 i) * pow d (pow2 i - 1) % n)


val lemma_b_mod_pow2i: bBits:nat -> b:nat{b < pow2 bBits} -> i:pos{i <= bBits} -> Lemma
  (b % pow2 i == b / pow2 (i - 1) % 2 * pow2 (i - 1) + b % pow2 (i - 1))
let lemma_b_mod_pow2i bBits b i =
  calc (==) {
    b % pow2 i;
    (==) { Math.Lemmas.euclidean_division_definition (b % pow2 i) (pow2 (i - 1)) }
    b % pow2 i / pow2 (i - 1) * pow2 (i - 1) + b % pow2 i % pow2 (i - 1);
    (==) { Math.Lemmas.pow2_modulo_modulo_lemma_1 b (i - 1) i }
    b % pow2 i / pow2 (i - 1) * pow2 (i - 1) + b % pow2 (i - 1);
    (==) { Math.Lemmas.pow2_modulo_division_lemma_1 b (i - 1) i; assert_norm (pow2 1 = 2) }
    b / pow2 (i - 1) % 2 * pow2 (i - 1) + b % pow2 (i - 1);
  }


val mod_exp_mont_lemma_step_acc0:
    n:pos -> d:int
  -> bBits:nat -> b:nat{b < pow2 bBits}
  -> i:pos{i <= bBits}
  -> aM0:nat -> accM0:nat
  -> aM1:nat -> accM1:nat ->
  Lemma
  (requires
    b / pow2 (i - 1) % 2 == 0 /\
    aM1 == pow aM0 (pow2 (i - 1)) * pow d (pow2 (i - 1) - 1) % n /\
    accM1 == pow aM0 (b % pow2 (i - 1)) * accM0 * pow d (b % pow2 (i - 1)) % n)
  (ensures
   (let (aM2, accM2) = mod_exp_f n d bBits b (i - 1) (aM1, accM1) in
    accM2 == pow aM0 (b % pow2 i) * accM0 * pow d (b % pow2 i) % n))

let mod_exp_mont_lemma_step_acc0 n d bBits b i aM0 accM0 aM1 accM1 =
  let (aM2, accM2) = mod_exp_f n d bBits b (i - 1) (aM1, accM1) in
  assert (accM2 = accM1);
  lemma_b_mod_pow2i bBits b i;
  assert (b % pow2 i == b % pow2 (i - 1))


val mod_exp_mont_lemma_step_acc1:
    n:pos -> d:int
  -> bBits:nat -> b:nat{b < pow2 bBits}
  -> i:pos{i <= bBits}
  -> aM0:nat -> accM0:nat
  -> aM1:nat -> accM1:nat ->
  Lemma
  (requires
    b / pow2 (i - 1) % 2 == 1 /\
    aM1 == pow aM0 (pow2 (i - 1)) * pow d (pow2 (i - 1) - 1) % n /\
    accM1 == pow aM0 (b % pow2 (i - 1)) * accM0 * pow d (b % pow2 (i - 1)) % n)
  (ensures
   (let (aM2, accM2) = mod_exp_f n d bBits b (i - 1) (aM1, accM1) in
    accM2 == pow aM0 (b % pow2 i) * accM0 * pow d (b % pow2 i) % n))

let mod_exp_mont_lemma_step_acc1 n d bBits b i aM0 accM0 aM1 accM1 =
  let (aM2, accM2) = mod_exp_f n d bBits b (i - 1) (aM1, accM1) in
  let p1 = pow2 (i - 1) in
  assert (accM2 == accM1 * aM1 * d % n);
  let lemma_b_mod_pow2i_loc () : Lemma (b % pow2 i == p1 + b % p1) =
    lemma_b_mod_pow2i bBits b i in

  calc (==) {
    accM1 * aM1 * d % n;
    (==) { }
    (pow aM0 (b % p1) * accM0 * pow d (b % p1) % n) * (pow aM0 p1 * pow d (p1 - 1) % n) * d % n;
    (==) { lemma_mod_mul_distr_aux (pow aM0 (b % p1) * accM0 * pow d (b % p1)) (pow aM0 p1 * pow d (p1 - 1)) d n }
    pow aM0 (b % p1) * accM0 * pow d (b % p1) * (pow aM0 p1 * pow d (p1 - 1)) * d % n;
    (==) { lemma_mul_ass5 (pow aM0 (b % p1) * accM0) (pow d (b % p1)) (pow aM0 p1) (pow d (p1 - 1)) d }
    pow aM0 (b % p1) * accM0 * pow aM0 p1 * (pow d (b % p1) * pow d (p1 - 1) * d) % n;
    (==) { lemma_mul_ass3 (pow aM0 (b % p1)) accM0 (pow aM0 p1) }
    pow aM0 (b % p1) * pow aM0 p1 * accM0 * (pow d (b % p1) * pow d (p1 - 1) * d) % n;
    (==) { lemma_pow_add aM0 (b % p1) p1 }
    pow aM0 (b % p1 + p1) * accM0 * (pow d (b % p1) * pow d (p1 - 1) * d) % n;
    (==) { lemma_pow_add d (b % p1) (p1 - 1) }
    pow aM0 (b % p1 + p1) * accM0 * (pow d (b % p1 + p1 - 1) * d) % n;
    (==) { lemma_pow1 d; lemma_pow_add d (b % p1 + p1 - 1) 1 }
    pow aM0 (b % p1 + p1) * accM0 * pow d (b % p1 + p1) % n;
    (==) { lemma_b_mod_pow2i_loc () }
    pow aM0 (b % pow2 i) * accM0 * pow d (b % pow2 i) % n;
    };
  assert (accM1 * aM1 * d % n == pow aM0 (b % pow2 i) * accM0 * pow d (b % pow2 i) % n)


val mod_exp_mont_lemma_step_acc:
    n:pos -> d:int
  -> bBits:nat -> b:nat{b < pow2 bBits}
  -> i:pos{i <= bBits}
  -> aM0:nat -> accM0:nat
  -> aM1:nat -> accM1:nat ->
  Lemma
  (requires
    aM1 == pow aM0 (pow2 (i - 1)) * pow d (pow2 (i - 1) - 1) % n /\
    accM1 == pow aM0 (b % pow2 (i - 1)) * accM0 * pow d (b % pow2 (i - 1)) % n)
  (ensures
   (let (aM2, accM2) = mod_exp_f n d bBits b (i - 1) (aM1, accM1) in
    accM2 == pow aM0 (b % pow2 i) * accM0 * pow d (b % pow2 i) % n))

let mod_exp_mont_lemma_step_acc n d bBits b i aM0 accM0 aM1 accM1 =
  let (aM2, accM2) = mod_exp_f n d bBits b (i - 1) (aM1, accM1) in
  if (b / pow2 (i - 1) % 2 = 1) then
    mod_exp_mont_lemma_step_acc1 n d bBits b i aM0 accM0 aM1 accM1
  else
    mod_exp_mont_lemma_step_acc0 n d bBits b i aM0 accM0 aM1 accM1


val mod_exp_mont_lemma:
    n:pos -> d:int
  -> bBits:nat -> b:nat{b < pow2 bBits}
  -> i:nat{i <= bBits}
  -> aM0:nat{aM0 < n} -> accM0:nat{accM0 < n} ->
  Lemma
   (let aM1, accM1 = Loops.repeati i (mod_exp_f n d bBits b) (aM0, accM0) in
    accM1 == pow aM0 (b % pow2 i) * accM0 * pow d (b % pow2 i) % n /\
    aM1 == pow aM0 (pow2 i) * pow d (pow2 i - 1) % n)

let rec mod_exp_mont_lemma n d bBits b i aM0 accM0 =
  if i = 0 then begin
    Loops.eq_repeati0 i (mod_exp_f n d bBits b) (aM0, accM0);
    calc (==) {
      pow aM0 (b % pow2 i) * accM0 * pow d (b % pow2 i) % n;
      (==) { assert_norm (b % pow2 0 = 0) }
      pow aM0 0 * accM0 * pow d 0 % n;
      (==) { lemma_pow0 aM0; lemma_pow0 d }
      accM0 % n;
      (==) { Math.Lemmas.small_mod accM0 n }
      accM0;
      };

    calc (==) {
      pow aM0 (pow2 i) * pow d (pow2 i - 1) % n;
      (==) { assert_norm (pow2 i = 1) }
      pow aM0 1 * pow d 0 % n;
      (==) { lemma_pow1 aM0; lemma_pow0 d }
      aM0 % n;
      (==) { Math.Lemmas.small_mod aM0 n }
      aM0;
      } end
  else begin
    Loops.unfold_repeati i (mod_exp_f n d bBits b) (aM0, accM0) (i - 1);
    let aM1, accM1 = Loops.repeati (i - 1) (mod_exp_f n d bBits b) (aM0, accM0) in
    mod_exp_mont_lemma n d bBits b (i - 1) aM0 accM0;
    mod_exp_mont_lemma_step_a n d bBits b i aM0 accM0 aM1 accM1;
    mod_exp_mont_lemma_step_acc n d bBits b i aM0 accM0 aM1 accM1;
    () end


val lemma_mont_aux: n:pos -> r:pos -> d:int{r * d % n == 1} -> a:nat -> Lemma
  (a * r % n * d % n == a % n)
let lemma_mont_aux n r d a =
  calc (==) {
    a * r % n * d % n;
    (==) { Math.Lemmas.lemma_mod_mul_distr_l (a * r) d n }
    a * r * d % n;
    (==) { Math.Lemmas.paren_mul_right a r d; Math.Lemmas.lemma_mod_mul_distr_r a (r * d) n }
    a * (r * d % n) % n;
    (==) { assert (r * d % n == 1) }
    a % n;
  }


val mont_mod_exp_lemma_before_to_mont:
  n:pos -> r:pos -> d:int{r * d % n == 1} -> bBits:nat -> b:pos{b < pow2 bBits} -> a:nat -> accM0:nat{accM0 < n} -> Lemma
  (pow (a * r % n) b * accM0 * pow d b % n == pow a b * accM0 % n)

let mont_mod_exp_lemma_before_to_mont n r d bBits b a accM0 =
  let aM0 = a * r % n in
  let (aM1, accM1) : tuple2 nat nat = Loops.repeati bBits (mod_exp_f n d bBits b) (aM0, accM0) in
  mod_exp_mont_lemma n d bBits b bBits aM0 accM0;
  Math.Lemmas.small_mod b (pow2 bBits);
  assert (accM1 == pow aM0 b * accM0 * pow d b % n);
  calc (==) {
    pow aM0 b * accM0 * pow d b % n;
    (==) { lemma_mul_ass3 (pow aM0 b) accM0 (pow d b) }
    pow aM0 b * pow d b * accM0 % n;
    (==) { lemma_pow_mul_base aM0 d b }
    pow (aM0 * d) b * accM0 % n;
    (==) { Math.Lemmas.lemma_mod_mul_distr_l (pow (aM0 * d) b) accM0 n }
    pow (aM0 * d) b % n * accM0 % n;
    (==) { lemma_pow_mod_base (aM0 * d) b n }
    pow (aM0 * d % n) b % n * accM0 % n;
    (==) { lemma_mont_aux n r d a }
    pow (a % n) b % n * accM0 % n;
    (==) { lemma_pow_mod_base a b n }
    pow a b % n * accM0 % n;
    (==) { Math.Lemmas.lemma_mod_mul_distr_l (pow a b) accM0 n }
    pow a b * accM0 % n;
  };
  assert (accM1 == pow a b * accM0 % n)


val mont_mod_exp_lemma_after_to_mont:
  n:pos -> r:pos -> d:int{r * d % n == 1} -> bBits:nat -> b:pos{b < pow2 bBits} -> a:nat -> Lemma
  (pow a b * (1 * r % n) % n * d % n == pow a b % n)

let mont_mod_exp_lemma_after_to_mont n r d bBits b a =
  let accM0 = 1 * r % n in
  calc (==) {
    pow a b * accM0 % n * d % n;
    (==) { Math.Lemmas.lemma_mod_mul_distr_l (pow a b * accM0) d n }
    pow a b * accM0 * d % n;
    (==) { Math.Lemmas.paren_mul_right (pow a b) accM0 d }
    pow a b * (accM0 * d) % n;
    (==) { Math.Lemmas.lemma_mod_mul_distr_r (pow a b) (accM0 * d) n }
    pow a b * (accM0 * d % n) % n;
    (==) { lemma_mont_aux n r d 1 }
    pow a b * (1 % n) % n;
    (==) { Math.Lemmas.lemma_mod_mul_distr_r (pow a b) 1 n }
    pow a b % n;
  }


val mod_exp_lemma: n:pos -> r:pos -> d:int{r * d % n == 1} -> a:nat -> bBits:nat -> b:pos{b < pow2 bBits} -> Lemma
  (mod_exp_mont n r d a bBits b == pow a b % n)

let mod_exp_lemma n r d a bBits b =
  let open Lib.LoopCombinators in
  let aM0 = a * r % n in
  let accM0 = 1 * r % n in
  let (aM1, accM1) : tuple2 nat nat = repeati bBits (mod_exp_f n d bBits b) (aM0, accM0) in
  mod_exp_mont_lemma n d bBits b bBits aM0 accM0;
  Math.Lemmas.small_mod b (pow2 bBits);
  assert (accM1 == pow aM0 b * accM0 * pow d b % n);
  mont_mod_exp_lemma_before_to_mont n r d bBits b a accM0;
  assert (accM1 == pow a b * accM0 % n);
  let res = accM1 * d % n in
  mont_mod_exp_lemma_after_to_mont n r d bBits b a;
  assert (accM1 * d % n == pow a b % n)

///
///  High-level specification of Montgomery exponentiation using functions defined in Hacl.Spec.Montgomery.Lemmas
///

val mod_exp_f_ll: rLen:nat -> n:pos -> mu:nat -> bBits:nat -> b:nat{b < pow2 bBits} -> i:nat{i < bBits} -> tuple2 nat nat -> tuple2 nat nat
let mod_exp_f_ll rLen n mu bBits b i (aM, accM) =
  let accM = if (b / pow2 i % 2 = 1) then M.mont_mul rLen n mu accM aM else accM in
  let aM = M.mont_mul rLen n mu aM aM in
  (aM, accM)

val mod_exp_mont_ll: rLen:nat -> n:pos -> mu:nat -> a:nat -> bBits:nat -> b:pos{b < pow2 bBits} -> nat
let mod_exp_mont_ll rLen n mu a bBits b =
  let aM = M.to_mont rLen n mu a in
  let accM = M.to_mont rLen n mu 1 in
  let (aM, accM) = Loops.repeati bBits (mod_exp_f_ll rLen n mu bBits b) (aM, accM) in
  M.from_mont rLen n mu accM


val mod_exp_mont_ll_lemma_loop:
    rLen:nat -> n:pos -> d:int -> mu:nat -> bBits:nat -> b:pos{b < pow2 bBits}
  -> i:nat{i <= bBits} -> aM0:nat -> accM0:nat -> Lemma
  (requires
    (1 + n * mu) % pow2 64 == 0 /\ pow2 (64 * rLen) * d % n == 1 /\
    n < pow2 (64 * rLen) /\ aM0 < n /\ accM0 < n)
  (ensures
    (let aM1, accM1 = Loops.repeati i (mod_exp_f_ll rLen n mu bBits b) (aM0, accM0) in
     let aM2, accM2 = Loops.repeati i (mod_exp_f n d bBits b) (aM0, accM0) in
     aM1 == aM2 /\ accM1 == accM2 /\ aM1 < n /\ accM1 < n))

let rec mod_exp_mont_ll_lemma_loop rLen n d mu bBits b i aM0 accM0 =
  let aM1, accM1 = Loops.repeati i (mod_exp_f_ll rLen n mu bBits b) (aM0, accM0) in
  let aM2, accM2 = Loops.repeati i (mod_exp_f n d bBits b) (aM0, accM0) in
  if i = 0 then begin
    Loops.eq_repeati0 i (mod_exp_f n d bBits b) (aM0, accM0);
    Loops.eq_repeati0 i (mod_exp_f_ll rLen n mu bBits b) (aM0, accM0);
    () end
  else begin
    let aM3, accM3 = Loops.repeati (i - 1) (mod_exp_f_ll rLen n mu bBits b) (aM0, accM0) in
    let aM4, accM4 = Loops.repeati (i - 1) (mod_exp_f n d bBits b) (aM0, accM0) in
    Loops.unfold_repeati i (mod_exp_f n d bBits b) (aM0, accM0) (i - 1);
    Loops.unfold_repeati i (mod_exp_f_ll rLen n mu bBits b) (aM0, accM0) (i - 1);
    //assert ((aM1, accM1) == mod_exp_f_ll rLen n mu bBits b (i - 1) (aM3, accM3));
    //assert ((aM2, accM2) == mod_exp_f n d bBits b (i - 1) (aM4, accM4));
    mod_exp_mont_ll_lemma_loop rLen n d mu bBits b (i - 1) aM0 accM0;
    assert (aM3 == aM4 /\ accM3 == accM4 /\ aM3 < n /\ accM3 < n);
    Math.Lemmas.lemma_mult_lt_sqr aM3 aM3 n;
    M.mont_reduction_lemma rLen n d mu (aM3 * aM3);

    Math.Lemmas.lemma_mult_lt_sqr accM3 aM3 n;
    M.mont_reduction_lemma rLen n d mu (accM3 * aM3);
    () end

///
///  Lemma (mod_exp_mont_ll rLen n mu a bBits b == pow a b % n)
///

val mod_exp_mont_ll_lemma_eval:
  rLen:nat -> n:pos -> d:int -> mu:nat -> a:nat -> bBits:nat -> b:pos{b < pow2 bBits} -> Lemma
  (requires
    (1 + n * mu) % pow2 64 == 0 /\ pow2 (64 * rLen) * d % n == 1 /\
    1 < n /\ n < pow2 (64 * rLen) /\ a < n)
  (ensures  mod_exp_mont_ll rLen n mu a bBits b == pow a b % n)

let mod_exp_mont_ll_lemma_eval rLen n d mu a bBits b =
  let r = pow2 (64 * rLen) in
  let aM0 = M.to_mont rLen n mu a in
  let accM0 = M.to_mont rLen n mu 1 in
  M.to_mont_lemma rLen n d mu a;
  M.to_mont_lemma rLen n d mu 1;
  let (aM1, accM1) : tuple2 nat nat = Loops.repeati bBits (mod_exp_f_ll rLen n mu bBits b) (aM0, accM0) in
  mod_exp_mont_ll_lemma_loop rLen n d mu bBits b bBits aM0 accM0;
  let res = M.from_mont rLen n mu accM1 in
  M.from_mont_lemma rLen n d mu accM1;
  mod_exp_lemma n r d a bBits b


val mod_exp_mont_ll_lemma:
  rLen:nat -> n:pos -> d:int -> mu:nat -> a:nat -> bBits:nat -> b:pos{b < pow2 bBits} -> Lemma
  (requires
    (1 + n * mu) % pow2 64 == 0 /\ pow2 (64 * rLen) * d % n == 1 /\
    1 < n /\ n < pow2 (64 * rLen) /\ a < n)
  (ensures mod_exp_mont_ll rLen n mu a bBits b == pow_mod #n a b)

let mod_exp_mont_ll_lemma rLen n d mu a bBits b =
  mod_exp_mont_ll_lemma_eval rLen n d mu a bBits b;
  lemma_pow_mod #n a b
