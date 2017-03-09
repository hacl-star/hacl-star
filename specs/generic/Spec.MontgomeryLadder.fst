module Spec.MontgomeryLadder


#set-options "--initial_fuel 0 --max_fuel 0"

type additive_law (a:eqtype) (zero:a) = add:(x:a -> y:a -> Tot a)
  {(forall x y. {:pattern (x `add` y)} x `add` y = y `add` x /\ x `add` zero = x)
   /\ (forall x y z. {:pattern (x `add` (y `add` z))}  (x `add` y) `add` z = x `add` (y `add` z))}

let rec exp #a #zero (add:additive_law a zero) x (k:nat) =
  if k = 0 then zero
  else x `add` (exp add x (k-1))

#set-options "--initial_fuel 1 --max_fuel 1"

let rec lemma_exp_add #a #zero (add:additive_law a zero) x (k:nat) (k':nat) z z' : Lemma
  (requires (z = exp add x k /\ z' = exp add x k'))
  (ensures (z `add` z' = exp add x (k+k')))
  = if k = 0 then ()
    else (
      lemma_exp_add add x (k-1) k' (exp add x (k-1)) z';
      cut (z = x `add` (exp add x (k-1)));
      cut (z `add` z' = (x `add` (exp add x (k-1)) `add` z'));
      cut (x `add` ((exp add x (k-1)) `add` z') = (x `add` (exp add x (k-1)) `add` z'))
    )

let rec lemma_exp_def_0 #a #zero (add:additive_law a zero) x (k:nat) (k':nat) z z' : Lemma
  (requires (z = exp add x k /\ z' = exp add x k'))
  (ensures (z `add` z' = exp add x (k+k')))
  = if k = 0 then ()
    else (
      lemma_exp_add add x (k-1) k' (exp add x (k-1)) z';
      cut (z = x `add` (exp add x (k-1)));
      cut (z `add` z' = (x `add` (exp add x (k-1)) `add` z'));
      cut (x `add` ((exp add x (k-1)) `add` z') = (x `add` (exp add x (k-1)) `add` z'))
    )

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
        
#reset-options "--initial_fuel 1 --max_fuel 1 --z3rlimit 100"

val montgomery_ladder:
  #a:eqtype -> #zero:a ->
  f:additive_law a zero ->
  init:a ->
  k:nat ->
  max:nat{k < pow2 max} ->
  Tot (y:a{y = exp f init k})
let montgomery_ladder #a #zero plus init k max =
  cut (k / pow2 max = 0);
  cut (zero = exp plus init 0);
  cut (init = exp plus init 1);
  cut (zero = exp plus init (k / pow2 max));
  cut (init = exp plus init (k / pow2 max + 1));
  montgomery_ladder_ #a #zero plus init zero init k max max
