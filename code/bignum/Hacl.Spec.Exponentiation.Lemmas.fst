module Hacl.Spec.Exponentiation.Lemmas

open FStar.Mul
open Lib.NatMod

module M = Hacl.Spec.Montgomery.Lemmas
module Loops = Lib.LoopCombinators


#reset-options "--z3rlimit 50 --fuel 0 --ifuel 0"

///
///  Generic math lemmas
///
val lemma_mul_ass3: a:int -> b:int -> c:int ->
  Lemma (a * b * c == a * c * b)
let lemma_mul_ass3 a b c = ()

val lemma_mul_ass4: a:int -> b:int -> c:int -> d:int ->
  Lemma ((a * b) * (c * d) == (a * c) * (b * d))
let lemma_mul_ass4 a b c d = ()

val lemma_mul_ass5_aux: a:int -> b:int -> c:int -> d:int -> e:int ->
  Lemma (a * b * c * d * e == a * b * (c * d * e))
let lemma_mul_ass5_aux a b c d e =
  calc (==) {
    a * b * c * d * e;
    (==) { Math.Lemmas.paren_mul_right (a * b) c d }
    a * b * (c * d) * e;
    (==) { Math.Lemmas.paren_mul_right (a * b) (c * d) e }
    a * b * (c * d * e);
  }


val lemma_mul_ass5: a:int -> b:int -> c:int -> d:int -> e:int ->
  Lemma (a * b * (c * d) * e == a * c * (b * d * e))
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

val lemma_mod_mul_distr_aux: a:int -> b:int -> c:int -> n:pos ->
  Lemma (a * b * c % n == a % n * (b % n) * c % n)
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
///  the right-to-left and left-to-right binary exponentiation functions are
///  defined here just to infer the loop invariant
///

val lemma_b_mod_pow2i: bBits:nat -> b:nat{b < pow2 bBits} -> i:pos{i <= bBits} ->
  Lemma (b % pow2 i == b / pow2 (i - 1) % 2 * pow2 (i - 1) + b % pow2 (i - 1))
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

val lemma_b_div_pow2i: bBits:nat -> b:nat{b < pow2 bBits} -> i:nat{i <= bBits} ->
  Lemma (b / pow2 (bBits - i) == b / pow2 (bBits - i + 1) * 2 + b / pow2 (bBits - i) % 2)
let lemma_b_div_pow2i bBits b i =
  calc (==) {
    b / pow2 (bBits - i);
    (==) { Math.Lemmas.euclidean_division_definition (b / pow2 (bBits - i)) 2 }
    (b / pow2 (bBits - i)) / 2 * 2 + b / pow2 (bBits - i) % 2;
    (==) { assert_norm (pow2 1 = 2) }
    (b / pow2 (bBits - i)) / pow2 1 * 2 + b / pow2 (bBits - i) % 2;
    (==) { Math.Lemmas.division_multiplication_lemma b (pow2 (bBits - i)) (pow2 1); Math.Lemmas.pow2_plus (bBits - i) 1 }
    b / pow2 (bBits - i + 1) * 2 + b / pow2 (bBits - i) % 2;
    }


//a right-to-left binary method
val exp_rl_f: bBits:nat -> b:nat{b < pow2 bBits} -> i:nat{i < bBits} -> tuple2 nat nat -> tuple2 nat nat
let exp_rl_f bBits b i (a, acc) =
  let acc = if (b / pow2 i % 2 = 1) then acc * a else acc in
  let a = a * a in
  (a, acc)

val exp_rl: a:nat -> bBits:nat -> b:nat{b < pow2 bBits} -> nat
let exp_rl a bBits b =
  let (a, acc) = Loops.repeati bBits (exp_rl_f bBits b) (a, 1) in
  acc


val exp_rl_lemma_loop:
    bBits:nat -> b:nat{b < pow2 bBits}
  -> i:nat{i <= bBits}
  -> a0:nat -> acc0:nat ->
  Lemma
   (let (a, acc) = Loops.repeati i (exp_rl_f bBits b) (a0, acc0) in
    acc == pow a0 (b % pow2 i) * acc0 /\ a == pow a0 (pow2 i))

let rec exp_rl_lemma_loop bBits b i a0 acc0 =
  let (a, acc) = Loops.repeati i (exp_rl_f bBits b) (a0, acc0) in
  if i = 0 then begin
    Loops.eq_repeati0 i (exp_rl_f bBits b) (a0, acc0);
    assert_norm (pow2 0 = 1);
    lemma_pow0 a;
    lemma_pow1 a;
    () end
  else begin
    Loops.unfold_repeati i (exp_rl_f bBits b) (a0, acc0) (i - 1);
    let (a1, acc1) = Loops.repeati (i - 1) (exp_rl_f bBits b) (a0, acc0) in
    //assert (a == a1 * a1);
    //assert (acc == (if (b / pow2 (i - 1) % 2 = 1) then acc1 * a1 else acc1));

    exp_rl_lemma_loop bBits b (i - 1) a0 acc0;
    assert (acc1 == pow a0 (b % pow2 (i - 1)) * acc0 /\ a1 == pow a0 (pow2 (i - 1)));
    lemma_pow_add a0 (pow2 (i - 1)) (pow2 (i - 1));
    Math.Lemmas.pow2_double_sum (i - 1);
    assert (a == pow a0 (pow2 i));

    lemma_b_mod_pow2i bBits b i;
    assert (b % pow2 i == b / pow2 (i - 1) % 2 * pow2 (i - 1) + b % pow2 (i - 1));

    if (b / pow2 (i - 1) % 2 = 1) then begin
      //assert (acc == acc1 * a1);
      assert (acc == pow a0 (b % pow2 (i - 1)) * acc0 * pow a0 (pow2 (i - 1)));
      lemma_pow_add a0 (b % pow2 (i - 1)) (pow2 (i - 1));
      assert (acc == pow a0 (b % pow2 i) * acc0);
      () end
    else () end


val exp_rl_lemma: a:nat -> bBits:nat -> b:nat{b < pow2 bBits} ->
  Lemma (exp_rl a bBits b == pow a b)
let exp_rl_lemma a bBits b =
  let (a1, acc1) = Loops.repeati bBits (exp_rl_f bBits b) (a, 1) in
  exp_rl_lemma_loop bBits b bBits a 1;
  assert (acc1 == pow a (b % pow2 bBits));
  Math.Lemmas.small_mod b (pow2 bBits)


//a left-to-right binary method
val exp_lr_f: a:nat -> bBits:nat -> b:nat{b < pow2 bBits} -> i:nat{i < bBits} -> acc:nat -> nat
let exp_lr_f a bBits b i acc =
  let acc = acc * acc  in
  let acc = if (b / pow2 (bBits - i - 1) % 2 = 0) then acc else acc * a in
  acc


val exp_lr: a:nat -> bBits:nat -> b:nat{b < pow2 bBits} -> nat
let exp_lr a bBits b = Loops.repeati bBits (exp_lr_f a bBits b) 1


val exp_lr_lemma_step0:
    a:int -> bBits:nat -> b:nat{b < pow2 bBits}
  -> i:nat{i < bBits} -> acc0:nat ->
  Lemma (let acc1 = pow a (b / pow2 (bBits - i)) * acc0 in
    acc1 * acc1 == pow a (b / pow2 (bBits - i - 1) - b / pow2 (bBits - i - 1) % 2) * (acc0 * acc0))

let exp_lr_lemma_step0 a bBits b i acc0 =
  let acc1 = pow a (b / pow2 (bBits - i)) * acc0 in
  lemma_b_div_pow2i bBits b (i + 1);
  assert (b / pow2 (bBits - i - 1) == b / pow2 (bBits - i) * 2 + b / pow2 (bBits - i - 1) % 2);

  let a1 = pow a (b / pow2 (bBits - i)) in
  calc (==) {
    acc1 * acc1;
    (==) { }
    (a1 * acc0) * (a1 * acc0);
    (==) { lemma_mul_ass4 a1 acc0 a1 acc0 }
    a1 * a1 * (acc0 * acc0);
    (==) { lemma_pow_add a (b / pow2 (bBits - i)) (b / pow2 (bBits - i)) }
    pow a (b / pow2 (bBits - i) * 2) * (acc0 * acc0);
    }


val exp_lr_lemma_step1:
    a:int -> bBits:nat -> b:nat{b < pow2 bBits}
  -> i:nat{i < bBits} -> acc0:nat ->
  Lemma (let acc1 = pow a (b / pow2 (bBits - i)) * acc0 in
    acc1 * acc1 * a == pow a (b / pow2 (bBits - i - 1) - b / pow2 (bBits - i - 1) % 2 + 1) * (acc0 * acc0))

let exp_lr_lemma_step1 a bBits b i acc0 =
  let acc1 = pow a (b / pow2 (bBits - i)) * acc0 in
  calc (==) {
    acc1 * acc1 * a;
    (==) { exp_lr_lemma_step0 a bBits b i acc0 }
    pow a (b / pow2 (bBits - i - 1) - b / pow2 (bBits - i - 1) % 2) * (acc0 * acc0) * a;
    (==) { Math.Lemmas.paren_mul_right (acc0 * acc0) (pow a (b / pow2 (bBits - i - 1) - b / pow2 (bBits - i - 1) % 2)) a }
    (acc0 * acc0) * (pow a (b / pow2 (bBits - i - 1) - b / pow2 (bBits - i - 1) % 2) * a);
    (==) { lemma_pow1 a; lemma_pow_add a (b / pow2 (bBits - i - 1) - b / pow2 (bBits - i - 1) % 2) 1 }
    (acc0 * acc0) * pow a (b / pow2 (bBits - i - 1) - b / pow2 (bBits - i - 1) % 2 + 1);
    }


val exp_lr_lemma_step:
    a:nat -> bBits:nat -> b:nat{b < pow2 bBits}
  -> i:nat{i < bBits}
  -> acc0:nat
  -> acc1:nat -> Lemma
  (requires acc1 == pow a (b / pow2 (bBits - i)) * acc0 /\ acc0 * acc0 = acc0)
  (ensures  exp_lr_f a bBits b i acc1 == pow a (b / pow2 (bBits - i - 1)) * acc0)

let exp_lr_lemma_step a bBits b i acc0 acc1 =
  let acc = exp_lr_f a bBits b i acc1 in

  if (b / pow2 (bBits - i - 1) % 2 = 0) then
    exp_lr_lemma_step0 a bBits b i acc0
  else
    exp_lr_lemma_step1 a bBits b i acc0


val exp_lr_lemma_loop:
    a:nat -> bBits:nat -> b:nat{b < pow2 bBits}
  -> i:nat{i <= bBits}
  -> acc0:nat{acc0 * acc0 = acc0} ->
  Lemma
   (let acc = Loops.repeati i (exp_lr_f a bBits b) acc0 in
    acc == pow a (b / pow2 (bBits - i)) * acc0)

let rec exp_lr_lemma_loop a bBits b i acc0 =
  let acc = Loops.repeati i (exp_lr_f a bBits b) acc0 in
  if i = 0 then begin
    Loops.eq_repeati0 i (exp_lr_f a bBits b) acc0;
    lemma_pow0 a;
    () end
  else begin
    let acc1 = Loops.repeati (i - 1) (exp_lr_f a bBits b) acc0 in
    Loops.unfold_repeati i (exp_lr_f a bBits b) acc0 (i - 1);
    //assert (acc == exp_lr_f a bBits b (i - 1) acc1);
    exp_lr_lemma_loop a bBits b (i - 1) acc0;
    //assert (acc1 == pow a (b / pow2 (bBits - i + 1)) * acc0);
    exp_lr_lemma_step a bBits b (i - 1) acc0 acc1;
    () end


val exp_lr_lemma: a:nat -> bBits:nat -> b:nat{b < pow2 bBits} ->
  Lemma (exp_lr a bBits b == pow a b)
let exp_lr_lemma a bBits b =
  let acc = Loops.repeati bBits (exp_lr_f a bBits b) 1 in
  exp_lr_lemma_loop a bBits b bBits 1;
  assert (acc == pow a (b / pow2 0));
  assert_norm (pow2 0 = 1)


// Montgomery ladder for exponentiation
val exp_mont_ladder_f: bBits:nat -> b:nat{b < pow2 bBits} -> i:nat{i < bBits} -> tuple2 nat nat -> tuple2 nat nat
let exp_mont_ladder_f bBits b i (r0, r1) =
  if (b / pow2 (bBits - i - 1) % 2 = 0) then
    (r0 * r0, r1 * r0)
  else
    (r0 * r1, r1 * r1)


val exp_mont_ladder: a:nat -> bBits:nat -> b:nat{b < pow2 bBits} -> nat
let exp_mont_ladder a bBits b =
  let r0 = 1 in
  let r1 = a in
  let (r0', r1') = Loops.repeati bBits (exp_mont_ladder_f bBits b) (r0, r1) in
  r0'


val exp_mont_ladder_lemma_step:
    a:nat -> bBits:nat -> b:nat{b < pow2 bBits}
  -> r0:nat{r0 * r0 == r0} -> r1:nat{r1 == r0 * a}
  -> r0'':nat -> r1'':nat
  -> i:nat{i < bBits} -> Lemma
  (requires
    r1'' == r0'' * a /\ r0'' == pow a (b / pow2 (bBits - i)) * r0)
  (ensures
    (let (r0', r1') = exp_mont_ladder_f bBits b i (r0'', r1'') in
    r1' == r0' * a /\ r0' == pow a (b / pow2 (bBits - i - 1)) * r0))

let exp_mont_ladder_lemma_step a bBits b r0 r1 r0'' r1'' i =
  let (r0', r1') = exp_mont_ladder_f bBits b i (r0'', r1'') in

  if (b / pow2 (bBits - i - 1) % 2 = 0) then begin
    assert (r0' == r0'' * r0'');
    assert (r1' == r1'' * r0'');
    exp_lr_lemma_step0 a bBits b i r0;
    () end
  else begin
    assert (r0' == r0'' * r1'');
    //assert (r0' == r0'' * (r0'' * a));
    assert (r1' == r1'' * r1'');

    Math.Lemmas.paren_mul_right r0'' r0'' a;
    exp_lr_lemma_step1 a bBits b i r0;
    lemma_mul_ass4 r0'' a r0'' a;
    () end


val exp_mont_ladder_lemma_loop:
    a:nat -> bBits:nat -> b:nat{b < pow2 bBits}
  -> r0:nat{r0 * r0 == r0} -> r1:nat{r1 == r0 * a}
  -> i:nat{i <= bBits} ->
  Lemma
   (let (r0', r1') = Loops.repeati i (exp_mont_ladder_f bBits b) (r0, r1) in
    r1' == r0' * a /\ r0' == pow a (b / pow2 (bBits - i)) * r0)

let rec exp_mont_ladder_lemma_loop a bBits b r0 r1 i =
  let (r0', r1') = Loops.repeati i (exp_mont_ladder_f bBits b) (r0, r1) in
  if i = 0 then begin
    Loops.eq_repeati0 i (exp_mont_ladder_f bBits b) (r0, r1);
    Math.Lemmas.small_div b (pow2 bBits);
    lemma_pow0 a;
    () end
  else begin
    let (r0'', r1'') = Loops.repeati (i - 1) (exp_mont_ladder_f bBits b) (r0, r1) in
    Loops.unfold_repeati i (exp_mont_ladder_f bBits b) (r0, r1) (i - 1);
    assert ((r0', r1') == exp_mont_ladder_f bBits b (i - 1) (r0'', r1''));
    exp_mont_ladder_lemma_loop a bBits b r0 r1 (i - 1);
    assert (r1'' == r0'' * a);
    assert (r0'' == pow a (b / pow2 (bBits - i + 1)) * r0);
    exp_mont_ladder_lemma_step a bBits b r0 r1 r0'' r1'' (i - 1);
    () end


val exp_mont_ladder_lemma: a:nat -> bBits:nat -> b:nat{b < pow2 bBits} ->
  Lemma (exp_mont_ladder a bBits b == pow a b)
let exp_mont_ladder_lemma a bBits b =
  let r0 = 1 in
  let r1 = a in
  let (r0', r1') = Loops.repeati bBits (exp_mont_ladder_f bBits b) (r0, r1) in
  exp_mont_ladder_lemma_loop a bBits b r0 r1 bBits;
  assert (r0' == pow a (b / pow2 0) * r0);
  assert_norm (pow2 0 = 1)


// Montgomery ladder for exponentiation with cswap
val cswap: sw:nat -> r0:nat -> r1:nat -> tuple2 nat nat
let cswap sw r0 r1 =
  if sw = 1 then (r1, r0) else (r0, r1)

// cswap -> step -> cswap -> cswap -> step -> cswap -> ..
val exp_mont_ladder_swap2_f: bBits:nat -> b:nat{b < pow2 bBits} -> i:nat{i < bBits} -> tuple2 nat nat -> tuple2 nat nat
let exp_mont_ladder_swap2_f bBits b i (r0, r1) =
  let bit = b / pow2 (bBits - i - 1) % 2 in
  let r0, r1 = cswap bit r0 r1 in
  let r0, r1 = (r0 * r0, r1 * r0) in
  let r0, r1 = cswap bit r0 r1 in
  (r0, r1)

val exp_mont_ladder_swap2: a:nat -> bBits:nat -> b:nat{b < pow2 bBits} -> nat
let exp_mont_ladder_swap2 a bBits b =
  let r0 = 1 in
  let r1 = a in
  let (r0', r1') = Loops.repeati bBits (exp_mont_ladder_swap2_f bBits b) (r0, r1) in
  r0'


val exp_mont_ladder_swap2_lemma_loop:
    a:nat -> bBits:pos -> b:nat{b < pow2 bBits}
  -> r0:nat -> r1:nat
  -> i:nat{i <= bBits} ->
  Lemma
  (let (r0', r1') = Loops.repeati i (exp_mont_ladder_swap2_f bBits b) (r0, r1) in
   let (r0'', r1'') = Loops.repeati i (exp_mont_ladder_f bBits b) (r0, r1) in
   r0' == r0'' /\ r1' == r1'')

let rec exp_mont_ladder_swap2_lemma_loop a bBits b r0 r1 i =
  let (r0', r1') = Loops.repeati i (exp_mont_ladder_swap2_f bBits b) (r0, r1) in
  let (r0'', r1'') = Loops.repeati i (exp_mont_ladder_f bBits b) (r0, r1) in
  if i = 0 then begin
    Loops.eq_repeati0 i (exp_mont_ladder_swap2_f bBits b) (r0, r1);
    Loops.eq_repeati0 i (exp_mont_ladder_f bBits b) (r0, r1);
    () end
  else begin
    Loops.unfold_repeati i (exp_mont_ladder_swap2_f bBits b) (r0, r1) (i - 1);
    Loops.unfold_repeati i (exp_mont_ladder_f bBits b) (r0, r1) (i - 1);
    exp_mont_ladder_swap2_lemma_loop a bBits b r0 r1 (i - 1);
    () end


val exp_mont_ladder_swap2_lemma: a:nat -> bBits:pos -> b:nat{b < pow2 bBits} ->
  Lemma (exp_mont_ladder_swap2 a bBits b == exp_mont_ladder a bBits b)

let exp_mont_ladder_swap2_lemma a bBits b =
  let r0 = 1 in
  let r1 = a in
  exp_mont_ladder_swap2_lemma_loop a bBits b r0 r1 bBits


// cswap -> step -> cswap -> step -> cswap -> ..
val exp_mont_ladder_swap_f: bBits:nat -> b:nat{b < pow2 bBits} -> i:nat{i < bBits} -> tuple3 nat nat nat -> tuple3 nat nat nat
let exp_mont_ladder_swap_f bBits b i (r0, r1, privbit) =
  let bit = b / pow2 (bBits - i - 1) % 2 in
  let sw = (bit + privbit) % 2 in
  let r0, r1 = cswap sw r0 r1 in
  let r0, r1 = (r0 * r0, r1 * r0) in
  (r0, r1, bit)

val exp_mont_ladder_swap: a:nat -> bBits:nat -> b:nat{b < pow2 bBits} -> nat
let exp_mont_ladder_swap a bBits b =
  let r0 = 1 in
  let r1 = a in
  let sw = 0 in
  let (r0', r1', sw') = Loops.repeati bBits (exp_mont_ladder_swap_f bBits b) (r0, r1, sw) in
  let r0', r1' = cswap sw' r0' r1' in
  r0'


val exp_mont_ladder_swap_lemma_loop:
    a:nat -> bBits:pos -> b:nat{b < pow2 bBits}
  -> r0:nat -> r1:nat -> sw0:nat{sw0 == b / pow2 bBits % 2}
  -> i:nat{i <= bBits} ->
  Lemma
  (let (r0', r1', sw) = Loops.repeati i (exp_mont_ladder_swap_f bBits b) (r0, r1, sw0) in
   let (r0'', r1'') = Loops.repeati i (exp_mont_ladder_f bBits b) (cswap sw0 r0 r1) in
   let bit = b / pow2 (bBits - i) % 2 in
   sw == bit /\ cswap bit r0' r1' == (r0'', r1''))

let rec exp_mont_ladder_swap_lemma_loop a bBits b r0 r1 sw0 i =
  if i = 0 then begin
    Loops.eq_repeati0 i (exp_mont_ladder_swap_f bBits b) (r0, r1, sw0);
    Loops.eq_repeati0 i (exp_mont_ladder_f bBits b) (cswap sw0 r0 r1);
    () end
  else begin
    Loops.unfold_repeati i (exp_mont_ladder_swap_f bBits b) (r0, r1, sw0) (i - 1);
    Loops.unfold_repeati i (exp_mont_ladder_f bBits b) (cswap sw0 r0 r1) (i - 1);
    exp_mont_ladder_swap_lemma_loop a bBits b r0 r1 sw0 (i - 1);
    () end


val exp_mont_ladder_swap_lemma: a:nat -> bBits:pos -> b:nat{b < pow2 bBits} ->
  Lemma (exp_mont_ladder_swap a bBits b == exp_mont_ladder a bBits b)

let exp_mont_ladder_swap_lemma a bBits b =
  let r0 = 1 in
  let r1 = a in
  let sw = 0 in
  exp_mont_ladder_swap_lemma_loop a bBits b r0 r1 sw bBits


///
///  High-level specification of Montgomery exponentiation
///

val mod_exp_mont_f: n:pos -> d:int -> bBits:nat -> b:nat{b < pow2 bBits} -> i:nat{i < bBits} -> tuple2 nat nat -> tuple2 nat nat
let mod_exp_mont_f n d bBits b i (aM, accM) =
  let accM = if (b / pow2 i % 2 = 1) then accM * aM * d % n else accM in
  let aM = aM * aM * d % n in
  (aM, accM)

val mod_exp_mont: n:pos -> r:pos -> d:int{r * d % n == 1} -> a:nat -> bBits:nat -> b:nat{b < pow2 bBits} -> nat
let mod_exp_mont n r d a bBits b =
  let aM = a * r % n in
  let accM = 1 * r % n in
  let (aM, accM) = Loops.repeati bBits (mod_exp_mont_f n d bBits b) (aM, accM) in
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
   (let (aM2, accM2) = mod_exp_mont_f n d bBits b (i - 1) (aM1, accM1) in
    aM2 == pow aM0 (pow2 i) * pow d (pow2 i - 1) % n))

let mod_exp_mont_lemma_step_a n d bBits b i aM0 accM0 aM1 accM1 =
  let b1 = pow2 (i - 1) in
  let pow2i_loc () : Lemma (b1 + b1 == pow2 i) =
    Math.Lemmas.pow2_double_sum (i - 1) in
  let (aM2, accM2) = mod_exp_mont_f n d bBits b (i - 1) (aM1, accM1) in
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
   (let (aM2, accM2) = mod_exp_mont_f n d bBits b (i - 1) (aM1, accM1) in
    accM2 == pow aM0 (b % pow2 i) * accM0 * pow d (b % pow2 i) % n))

let mod_exp_mont_lemma_step_acc0 n d bBits b i aM0 accM0 aM1 accM1 =
  let (aM2, accM2) = mod_exp_mont_f n d bBits b (i - 1) (aM1, accM1) in
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
   (let (aM2, accM2) = mod_exp_mont_f n d bBits b (i - 1) (aM1, accM1) in
    accM2 == pow aM0 (b % pow2 i) * accM0 * pow d (b % pow2 i) % n))

let mod_exp_mont_lemma_step_acc1 n d bBits b i aM0 accM0 aM1 accM1 =
  let (aM2, accM2) = mod_exp_mont_f n d bBits b (i - 1) (aM1, accM1) in
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
   (let (aM2, accM2) = mod_exp_mont_f n d bBits b (i - 1) (aM1, accM1) in
    accM2 == pow aM0 (b % pow2 i) * accM0 * pow d (b % pow2 i) % n))

let mod_exp_mont_lemma_step_acc n d bBits b i aM0 accM0 aM1 accM1 =
  let (aM2, accM2) = mod_exp_mont_f n d bBits b (i - 1) (aM1, accM1) in
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
   (let aM1, accM1 = Loops.repeati i (mod_exp_mont_f n d bBits b) (aM0, accM0) in
    accM1 == pow aM0 (b % pow2 i) * accM0 * pow d (b % pow2 i) % n /\
    aM1 == pow aM0 (pow2 i) * pow d (pow2 i - 1) % n)

let rec mod_exp_mont_lemma n d bBits b i aM0 accM0 =
  if i = 0 then begin
    Loops.eq_repeati0 i (mod_exp_mont_f n d bBits b) (aM0, accM0);
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
    Loops.unfold_repeati i (mod_exp_mont_f n d bBits b) (aM0, accM0) (i - 1);
    let aM1, accM1 = Loops.repeati (i - 1) (mod_exp_mont_f n d bBits b) (aM0, accM0) in
    mod_exp_mont_lemma n d bBits b (i - 1) aM0 accM0;
    mod_exp_mont_lemma_step_a n d bBits b i aM0 accM0 aM1 accM1;
    mod_exp_mont_lemma_step_acc n d bBits b i aM0 accM0 aM1 accM1;
    () end


val lemma_mont_aux: n:pos -> r:pos -> d:int{r * d % n == 1} -> a:nat ->
  Lemma (a * r % n * d % n == a % n)
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
    n:pos -> r:pos -> d:int{r * d % n == 1}
  -> bBits:nat -> b:pos{b < pow2 bBits}
  -> a:nat -> accM0:nat{accM0 < n} ->
  Lemma (pow (a * r % n) b * accM0 * pow d b % n == pow a b * accM0 % n)

let mont_mod_exp_lemma_before_to_mont n r d bBits b a accM0 =
  let aM0 = a * r % n in
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
  assert (pow aM0 b * accM0 * pow d b % n == pow a b * accM0 % n)


val mont_mod_exp_lemma_after_to_mont:
    n:pos -> r:pos -> d:int{r * d % n == 1} -> a:nat
  -> bBits:nat -> b:pos{b < pow2 bBits} ->
  Lemma (pow a b * (1 * r % n) % n * d % n == pow a b % n)

let mont_mod_exp_lemma_after_to_mont n r d a bBits b =
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


val mod_exp_lemma:
    n:pos -> r:pos -> d:int{r * d % n == 1} -> a:nat
  -> bBits:nat -> b:pos{b < pow2 bBits} ->
  Lemma (mod_exp_mont n r d a bBits b == pow a b % n)

let mod_exp_lemma n r d a bBits b =
  let open Lib.LoopCombinators in
  let aM0 = a * r % n in
  let accM0 = 1 * r % n in
  let (aM1, accM1) : tuple2 nat nat = repeati bBits (mod_exp_mont_f n d bBits b) (aM0, accM0) in
  mod_exp_mont_lemma n d bBits b bBits aM0 accM0;
  Math.Lemmas.small_mod b (pow2 bBits);
  assert (accM1 == pow aM0 b * accM0 * pow d b % n);
  mont_mod_exp_lemma_before_to_mont n r d bBits b a accM0;
  assert (accM1 == pow a b * accM0 % n);
  let res = accM1 * d % n in
  mont_mod_exp_lemma_after_to_mont n r d a bBits b;
  assert (accM1 * d % n == pow a b % n)

///
///  High-level specification of Montgomery exponentiation using functions defined in Hacl.Spec.Montgomery.Lemmas
///

val mod_exp_mont_f_ll: rLen:nat -> n:pos -> mu:nat -> bBits:nat -> b:nat{b < pow2 bBits} -> i:nat{i < bBits} -> tuple2 nat nat -> tuple2 nat nat
let mod_exp_mont_f_ll rLen n mu bBits b i (aM, accM) =
  let accM = if (b / pow2 i % 2 = 1) then M.mont_mul rLen n mu accM aM else accM in
  let aM = M.mont_mul rLen n mu aM aM in
  (aM, accM)

val mod_exp_mont_ll: rLen:nat -> n:pos -> mu:nat -> a:nat -> bBits:nat -> b:pos{b < pow2 bBits} -> nat
let mod_exp_mont_ll rLen n mu a bBits b =
  let aM = M.to_mont rLen n mu a in
  let accM = M.to_mont rLen n mu 1 in
  let (aM, accM) = Loops.repeati bBits (mod_exp_mont_f_ll rLen n mu bBits b) (aM, accM) in
  M.from_mont rLen n mu accM


val mod_exp_mont_ll_lemma_loop:
    rLen:nat -> n:pos -> d:int -> mu:nat -> bBits:nat -> b:pos{b < pow2 bBits}
  -> i:nat{i <= bBits} -> aM0:nat -> accM0:nat -> Lemma
  (requires
    (1 + n * mu) % pow2 64 == 0 /\ pow2 (64 * rLen) * d % n == 1 /\
    n < pow2 (64 * rLen) /\ aM0 < n /\ accM0 < n)
  (ensures
    (let aM1, accM1 = Loops.repeati i (mod_exp_mont_f_ll rLen n mu bBits b) (aM0, accM0) in
     let aM2, accM2 = Loops.repeati i (mod_exp_mont_f n d bBits b) (aM0, accM0) in
     aM1 == aM2 /\ accM1 == accM2 /\ aM1 < n /\ accM1 < n))

let rec mod_exp_mont_ll_lemma_loop rLen n d mu bBits b i aM0 accM0 =
  let aM1, accM1 = Loops.repeati i (mod_exp_mont_f_ll rLen n mu bBits b) (aM0, accM0) in
  let aM2, accM2 = Loops.repeati i (mod_exp_mont_f n d bBits b) (aM0, accM0) in
  if i = 0 then begin
    Loops.eq_repeati0 i (mod_exp_mont_f n d bBits b) (aM0, accM0);
    Loops.eq_repeati0 i (mod_exp_mont_f_ll rLen n mu bBits b) (aM0, accM0);
    () end
  else begin
    let aM3, accM3 = Loops.repeati (i - 1) (mod_exp_mont_f_ll rLen n mu bBits b) (aM0, accM0) in
    let aM4, accM4 = Loops.repeati (i - 1) (mod_exp_mont_f n d bBits b) (aM0, accM0) in
    Loops.unfold_repeati i (mod_exp_mont_f n d bBits b) (aM0, accM0) (i - 1);
    Loops.unfold_repeati i (mod_exp_mont_f_ll rLen n mu bBits b) (aM0, accM0) (i - 1);
    //assert ((aM1, accM1) == mod_exp_mont_f_ll rLen n mu bBits b (i - 1) (aM3, accM3));
    //assert ((aM2, accM2) == mod_exp_mont_f n d bBits b (i - 1) (aM4, accM4));
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
  let (aM1, accM1) : tuple2 nat nat = Loops.repeati bBits (mod_exp_mont_f_ll rLen n mu bBits b) (aM0, accM0) in
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

///
///  A left-to-right binary method with Montgomery arithmetic
///

val mod_exp_lr_f: n:pos -> d:int -> aM:nat -> bBits:nat -> b:nat{b < pow2 bBits} -> i:nat{i < bBits} -> accM:nat -> nat
let mod_exp_lr_f n d aM bBits b i accM =
  let accM = accM * accM * d % n in
  let accM = if (b / pow2 (bBits - i - 1) % 2 = 0) then accM else accM * aM * d % n in
  accM


val mod_exp_lr: n:pos -> r:pos -> d:int{r * d % n = 1} -> a:nat -> bBits:nat -> b:nat{b < pow2 bBits} -> nat
let mod_exp_lr n r d a bBits b =
  let rM = 1 * r % n in
  let aM = a * r % n in
  let rM'= Loops.repeati bBits (mod_exp_lr_f n d aM bBits b) rM in
  rM' * d % n


val mod_exp_lr_lemma_step0:
    n:pos -> r:pos -> d:int{r * d % n = 1}
  -> aM:nat -> bBits:nat -> b:nat{b < pow2 bBits}
  -> i:nat{i < bBits}
  -> accM0:nat{accM0 * accM0 * d % n = accM0 % n /\ accM0 < n} ->
  Lemma (let accM1 = pow (aM * d) (b / pow2 (bBits - i)) * accM0 % n in
    let aM2 = pow (aM * d) (b / pow2 (bBits - i - 1) - b / pow2 (bBits - i - 1) % 2) in
    accM1 * accM1 * d % n == aM2 * accM0 % n)

let mod_exp_lr_lemma_step0 n r d aM bBits b i accM0 =
  let accM1 = pow (aM * d) (b / pow2 (bBits - i)) * accM0 % n in
  let aM1 = pow (aM * d) (b / pow2 (bBits - i)) in
  let aM2 = pow (aM * d) (b / pow2 (bBits - i - 1) - b / pow2 (bBits - i - 1) % 2) in

  calc (==) {
    accM1 * accM1 * d % n;
    (==) { }
    (aM1 * accM0 % n) * (aM1 * accM0 % n) * d % n;
    (==) { Math.Lemmas.paren_mul_right (aM1 * accM0 % n) (aM1 * accM0 % n) d;
           Math.Lemmas.lemma_mod_mul_distr_l (aM1 * accM0) ((aM1 * accM0 % n) * d) n;
	   Math.Lemmas.paren_mul_right (aM1 * accM0) (aM1 * accM0 % n) d }
    (aM1 * accM0) * (aM1 * accM0 % n) * d % n;
    (==) { Math.Lemmas.paren_mul_right (aM1 * accM0 % n) (aM1 * accM0) d;
           Math.Lemmas.lemma_mod_mul_distr_l (aM1 * accM0) (aM1 * accM0 * d) n;
	   Math.Lemmas.paren_mul_right (aM1 * accM0) (aM1 * accM0) d }
    aM1 * accM0 * (aM1 * accM0) * d % n;
    (==) { exp_lr_lemma_step0 (aM * d) bBits b i accM0 }
    aM2 * (accM0 * accM0) * d % n;
    (==) { Math.Lemmas.paren_mul_right aM2 (accM0 * accM0) d }
    aM2 * (accM0 * accM0 * d) % n;
    (==) { Math.Lemmas.lemma_mod_mul_distr_r aM2 (accM0 * accM0 * d) n }
    aM2 * (accM0 % n) % n;
    (==) {  Math.Lemmas.lemma_mod_mul_distr_r aM2 accM0 n }
    aM2 * accM0 % n;
    }


val mod_exp_lr_lemma_step1:
    n:pos -> r:pos -> d:int{r * d % n = 1}
  -> aM:nat -> bBits:nat -> b:nat{b < pow2 bBits}
  -> i:nat{i < bBits}
  -> accM0:nat{accM0 * accM0 * d % n = accM0 % n /\ accM0 < n} ->
  Lemma (let acc1 = pow (aM * d) (b / pow2 (bBits - i)) * accM0 % n in
    let a3 = pow (aM * d) (b / pow2 (bBits - i - 1) - b / pow2 (bBits - i - 1) % 2 + 1) in
    (acc1 * acc1 * d % n) * aM * d % n == a3 * accM0 % n)

let mod_exp_lr_lemma_step1 n r d aM bBits b i accM0 =
  let accM1 = pow (aM * d) (b / pow2 (bBits - i)) * accM0 % n in
  let aM1 = pow (aM * d) (b / pow2 (bBits - i)) in
  let aM2 = pow (aM * d) (b / pow2 (bBits - i - 1) - b / pow2 (bBits - i - 1) % 2) in
  let aM3 = pow (aM * d) (b / pow2 (bBits - i - 1) - b / pow2 (bBits - i - 1) % 2 + 1) in

  calc (==) {
    (accM1 * accM1 * d % n) * aM * d % n;
    (==) { mod_exp_lr_lemma_step0 n r d aM bBits b i accM0 }
    (aM2 * accM0 % n) * aM * d % n;
    (==) { Math.Lemmas.paren_mul_right (aM2 * accM0 % n) aM d;
           Math.Lemmas.lemma_mod_mul_distr_l (aM2 * accM0) (aM * d) n }
    (aM2 * accM0) * (aM * d) % n;
    (==) { Math.Lemmas.paren_mul_right accM0 aM2 (aM * d) }
    aM2 * (aM * d) * accM0 % n;
    (==) { lemma_pow1 (aM * d); lemma_pow_add (aM * d) (b / pow2 (bBits - i - 1) - b / pow2 (bBits - i - 1) % 2) 1 }
    aM3 * accM0 % n;
    }


val mod_exp_lr_lemma_step:
    n:pos -> r:pos -> d:int{r * d % n = 1}
  -> aM:nat -> bBits:nat -> b:nat{b < pow2 bBits}
  -> i:nat{i < bBits}
  -> accM0:nat
  -> accM1:nat -> Lemma
  (requires
    accM0 * accM0 * d % n = accM0 % n /\ accM0 < n /\
    accM1 == pow (aM * d) (b / pow2 (bBits - i)) * accM0 % n)
  (ensures
    mod_exp_lr_f n d aM bBits b i accM1 == pow (aM * d) (b / pow2 (bBits - i - 1)) * accM0 % n)

let mod_exp_lr_lemma_step n r d aM bBits b i accM0 accM1 =
  let acc = mod_exp_lr_f n d aM bBits b i accM1 in
  if (b / pow2 (bBits - i - 1) % 2 = 0) then
    mod_exp_lr_lemma_step0 n r d aM bBits b i accM0
  else
    mod_exp_lr_lemma_step1 n r d aM bBits b i accM0


val mod_exp_lr_lemma_loop:
    n:pos -> r:pos -> d:int{r * d % n = 1}
  -> aM:nat -> bBits:nat -> b:nat{b < pow2 bBits}
  -> i:nat{i <= bBits}
  -> accM0:nat{accM0 * accM0 * d % n = accM0 % n /\ accM0 < n} ->
  Lemma
   (let accM = Loops.repeati i (mod_exp_lr_f n d aM bBits b) accM0 in
    accM == pow (aM * d) (b / pow2 (bBits - i)) * accM0 % n)

let rec mod_exp_lr_lemma_loop n r d aM bBits b i accM0 =
  let acc = Loops.repeati i (mod_exp_lr_f n d aM bBits b) accM0 in

  if i = 0 then begin
    Loops.eq_repeati0 i (mod_exp_lr_f n d aM bBits b) accM0;
    lemma_pow0 (aM * d);
    Math.Lemmas.small_mod accM0 n;
    assert (acc == accM0 % n);
    () end
  else begin
    let accM1 = Loops.repeati (i - 1) (mod_exp_lr_f n d aM bBits b) accM0 in
    Loops.unfold_repeati i (mod_exp_lr_f n d aM bBits b) accM0 (i - 1);
    //assert (acc == mod_exp_lr_f n d a bBits b (i - 1) acc1);
    mod_exp_lr_lemma_loop n r d aM bBits b (i - 1) accM0;
    //assert (acc1 == pow a (b / pow2 (bBits - i + 1)) * acc0 * pow d (b / pow2 (bBits - i + 1)) % n);
    mod_exp_lr_lemma_step n r d aM bBits b (i - 1) accM0 accM1;
    () end


val lemma_one_mont: n:pos -> r:pos -> d:int{r * d % n = 1} ->
  Lemma (let r0 = 1 * r % n in r0 * r0 * d % n == r0 % n)

let lemma_one_mont n r d =
  let r0 = 1 * r % n in
  calc (==) {
    r0 * r0 * d % n;
    (==) { Math.Lemmas.paren_mul_right r0 r0 d; Math.Lemmas.lemma_mod_mul_distr_r r0 (r0 * d) n }
    r0 * (r0 * d % n) % n;
    (==) {lemma_mont_aux n r d 1 }
    r0 * (1 % n) % n;
    (==) { Math.Lemmas.lemma_mod_mul_distr_r r0 1 n }
    r0 % n;
    }


val mod_exp_lr_lemma:
    n:pos -> r:pos -> d:int{r * d % n = 1}
  -> a:nat -> bBits:nat -> b:pos{b < pow2 bBits} ->
  Lemma (mod_exp_lr n r d a bBits b == pow a b % n)

let mod_exp_lr_lemma n r d a bBits b =
  let aM = a * r % n in
  let rM = 1 * r % n in
  let rM' = Loops.repeati bBits (mod_exp_lr_f n d aM bBits b) rM in
  lemma_one_mont n r d;
  mod_exp_lr_lemma_loop n r d aM bBits b bBits rM;
  assert_norm (pow2 0 = 1);
  assert (rM' == pow (aM * d) b * rM % n);

  calc (==) {
    pow (aM * d) b * rM % n;
    (==) { lemma_pow_mul_base aM d b }
    pow aM b * pow d b * rM % n;
    (==) { Math.Lemmas.paren_mul_right (pow aM b) (pow d b) rM }
    pow aM b * (rM * pow d b) % n;
    (==) { Math.Lemmas.paren_mul_right (pow aM b) rM (pow d b) }
    pow aM b * rM * pow d b % n;
    (==) { mont_mod_exp_lemma_before_to_mont n r d bBits b a rM }
    pow a b * rM % n;
    };
  assert (rM' == pow a b * rM % n);
  let res = rM' * d % n in
  assert (res == pow a b * rM % n * d % n);
  mont_mod_exp_lemma_after_to_mont n r d a bBits b
