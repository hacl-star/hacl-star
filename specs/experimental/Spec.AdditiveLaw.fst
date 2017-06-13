module Spec.AdditiveLaw

module ST = FStar.HyperStack.ST

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

let rec lemma_exp_def_0 #a #zero (add:additive_law a zero) x : Lemma
  (zero = exp add x 0)
  = ()

let rec lemma_exp_def_1 #a #zero (add:additive_law a zero) x (n:pos) : Lemma
  (x `add` exp add x (n-1) = exp add x n)
  = ()
