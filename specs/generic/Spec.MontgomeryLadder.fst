module Spec.MontgomeryLadder

open Spec.AdditiveLaw

#set-options "--initial_fuel 0 --max_fuel 0"

let lemma_div_scalar (k:nat) (ctr:pos) : Lemma
  (let b = k / pow2 (ctr-1) % 2 in
   k / pow2 (ctr - 1) = (k / pow2 ctr + k / pow2 ctr) + b)
  = let kctrm1 = k / pow2 (ctr - 1) in
    let kctr = k / pow2 ctr in
    Math.Lemmas.lemma_div_mod kctrm1 2;
    cut ( kctrm1 = op_Multiply 2 (kctrm1 / 2) + kctrm1 % 2);
    Math.Lemmas.division_multiplication_lemma k (pow2 (ctr-1)) 2;
    Math.Lemmas.pow2_plus 1 (ctr-1);
    assert_norm(pow2 1 = 2);
    cut ( kctrm1 = op_Multiply 2 kctr + kctrm1 % 2 )


let cswap swap x y = if swap then y,x else x,y

val montgomery_ladder_:
  #a:eqtype -> #zero:a ->
  f:additive_law a zero ->
  init:a ->
  x:a ->
  xp1:a ->
  k:nat ->
  ctr:nat{x = exp f init (k / pow2 ctr) /\ xp1 = exp f init (k / pow2 ctr + 1)} ->
  max:nat{ctr <= max /\ k < pow2 max} ->
  Tot (y:a{y = exp f init k})
      (decreases ctr)
let rec montgomery_ladder_ #a #zero plus init x xp1 k ctr max =
  if ctr = 0 then (assert_norm (pow2 0 = 1); cut (k / 1 = k); x)
  else (
    let ctr' = ctr - 1 in
    let swap = k / pow2 ctr' % 2 = 1 in
    let x, xp1 =
      if swap then (
        lemma_exp_add plus init (k/pow2 ctr) (k / pow2 ctr + 1) x xp1;
        lemma_exp_add plus init (k/pow2 ctr + 1) (k / pow2 ctr + 1) xp1 xp1;
        x `plus` xp1, xp1 `plus` xp1
      ) else (
        lemma_exp_add plus init (k/pow2 ctr) (k / pow2 ctr + 1) x xp1;
        lemma_exp_add plus init (k/pow2 ctr) (k / pow2 ctr) x x;
        x `plus` x, x `plus` xp1
      ) in
    lemma_div_scalar k ctr;
    montgomery_ladder_ plus init x xp1 k ctr' max
  )

val montgomery_ladder:
  #a:eqtype -> #zero:a ->
  f:additive_law a zero ->
  init:a ->
  k:nat ->
  max:nat{k < pow2 max} ->
  Tot (y:a{y = exp f init k})
let montgomery_ladder #a #zero plus init k max =
  lemma_exp_def_1 plus init 1;
  lemma_exp_def_0 plus init;
  montgomery_ladder_ #a #zero plus init zero init k max max
