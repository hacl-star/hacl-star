(*--build-config
  options:--verify_module Lemmas --z3rlimit 10;
  other-files:axiomatic.fst intlib.fst
  --*)

module Lemmas

open IntLib

val pow2_double_sum:
  n:nat -> Lemma (requires (True)) (ensures (pow2 n + pow2 n = pow2 (n+1))) 
let pow2_double_sum n =
  assert(n = ((n+1)-1));
  assert(pow2 n + pow2 n = 2 * pow2 n)

val pow2_double_mult:
  n:nat -> Lemma (requires (True)) (ensures (2 * pow2 n = pow2 (n+1)))
let pow2_double_mult n =
  assert(2 * pow2 n = pow2 n + pow2 n)

val pow2_increases_1:
  n:nat -> m:nat ->
  Lemma
    (requires (m < n))
    (ensures (pow2 m < pow2 n))
    (decreases (n-m))
let rec pow2_increases_1 n m =
  match n-m with
  | 1 -> ()
  | _ -> pow2_increases_1 (n-1) m; pow2_increases_1 n (n-1)

val pow2_increases_2:
  n:nat -> m:nat ->
  Lemma
    (requires (m <= n))
    (ensures (pow2 m <= pow2 n))
    (decreases (n-m))
let pow2_increases_2 n m =
  match n-m with
  | 0 -> ()
  | _ -> pow2_increases_1 n m

#reset-options

val aux_lemma_0: n:nat -> m:nat -> Lemma ((n-1)+m+1 = n+m)
let aux_lemma_0 n m = ()

val aux_lemma_1: n:nat -> Lemma (0+n = n)
let aux_lemma_1 n = ()

val aux_lemma_2: n:nat -> Lemma (1 * n = n)
let aux_lemma_2 n = ()

val pow2_exp_1:
  n:nat -> m:nat -> 
  Lemma 
    (requires (True))
    (ensures (pow2 n * pow2 m = pow2 (n+m)))
    (decreases n)
let rec pow2_exp_1 n m =
  match n with
  | 0 -> 
    assert(b2t(pow2 n = 1));
    aux_lemma_1 m;
    aux_lemma_2 (pow2 m)
  | i -> 
    cut(i >= 0 /\ i <> 0); 
    cut(b2t(i >= 1)); 
    cut(b2t(n - 1 >= 0)); 
    pow2_exp_1 (n-1) (m); 
    cut(b2t(pow2 (n-1) * pow2 m = pow2 ((n-1)+m)));
    pow2_double_mult ((n-1)+m);
    cut(b2t(2 * pow2 ((n-1)+m) = pow2 ((n-1)+m+1)));
    aux_lemma_0 n m;
    cut(b2t( 2 * (pow2 (n-1) * pow2 m) = pow2 (n+m))); 
    Axiomatic.paren_mul_left 2 (pow2 (n-1)) (pow2 m);
    Axiomatic.paren_mul_right 2 (pow2 (n-1)) (pow2 m);
    pow2_double_mult (n-1)
    
val nat_mul_1: a:nat -> b:nat -> Lemma (requires True) (ensures (a*b >= 0))
let nat_mul_1 a b = ()

(* Lemma : multiplying by a strictly positive value preserves strict inequalities *)
val mul_pos_strict_incr: a:pos -> b:int -> c:pos -> Lemma (requires (b < c)) (ensures (a * b < a * c /\ b * a < c * a ))
let mul_pos_strict_incr a b c = ()

(* Lemma : multiplying by a positive value preserves inequalities *)
val mul_incr : a:nat -> b:nat -> c:nat -> 
		     Lemma 
		       (requires ( b <= c))
		       (ensures ( a * b <= a * c /\ b * a <= c * a))
let mul_incr a b c = ()

(* Lemma : loss of precision in euclidian division *)
val multiply_fractions:
  a:nat -> n:pos ->
  Lemma
    (requires (True))
    (ensures ( n * ( a / n ) <= a ))
let multiply_fractions a n =
  (Axiomatic.euclidian_div_axiom a n)

(* Lemma : distributivity of minus over parenthesized sum *)
val paren_sub: a:int -> b:int -> c:int -> Lemma ((a - (b + c) = a - b - c /\ a - (b - c) = a - b + c))
let paren_sub a b c = ()

val non_zero_nat_is_pos: i:nat -> Lemma (requires (i <> 0)) (ensures (i >= 1))
let non_zero_nat_is_pos i = ()

val non_zero_nat_is_pos_2: n:nat -> Lemma (requires (n<>0)) (ensures (n-1>=0))
let non_zero_nat_is_pos_2 n = ()

val nat_plus_nat_is_nat: n:nat -> m:nat -> Lemma (n+m>=0)
let nat_plus_nat_is_nat n m = ()

val nat_times_nat_is_nat: n:nat -> m:nat -> Lemma (n*m>=0)
let nat_times_nat_is_nat n m = ()

val modulo_lemma: a:nat -> b:pos -> Lemma (requires (a < b)) (ensures (a % b = a))
let modulo_lemma a b = ()
