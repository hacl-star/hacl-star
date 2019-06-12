module Hacl.Spec.HE.Paillier

open FStar.Calc
open FStar.Mul
open FStar.Math.Lemmas
open FStar.Classical
open FStar.Squash

open Lib.Math.Algebra


(* Internals *)

type fenu (n:comp) = r:fe n{isunit r}
type fen2 (n:comp) = fe (n * n)
type fen2u n = r:fen2 n{isunit r}

val lemma_div_le_strict: #n:comp -> a:fen2 n -> Lemma (a / n < n /\ field_el #n (a/n))
let lemma_div_le_strict #n a =
  multiple_division_lemma n n;
  lemma_div_le a (n*n) n

val shrink: #n:comp -> a:fen2 n -> b:fe n{b = to_fe #n a}
let shrink #n a = to_fe #n a

val lift: #n:comp -> a:fe n -> b:fen2 n{b = a /\ shrink b = a}
let lift #n a = a

val isunit_in_nsquare2: #n:comp -> a:fen2 n -> Lemma
  (requires (isunit a))
  (ensures (isunit (shrink a)))
let isunit_in_nsquare2 #n a =

  let n2 = n * n in

  let l0 (): Lemma (requires (a % n = 0)) (ensures false) = begin
      mod_prop n a 0;
      assert (n * a = n2 * (a/n));
      multiple_modulo_lemma (a/n) n2;
      to_fe_idemp #n2 a;
      to_fe_idemp #n2 n;
      to_fe_mul' #n2 a n;
      assert (a *% n = 0);
      zerodiv_is_nonunit a n
    end in

  let l (): Lemma (a % n <> 0) = begin
      move_requires l0 ()
    end in

  l ();

  inv_as_gcd2 a;
  gcd_to_factor_one n n a;
  assert (is_gcd a n 1);
  gcd_mod_reduce n a;
  assert (is_gcd (to_fe #n a) n 1);
  inv_as_gcd1 (to_fe #n a)

// to_fe_mul specified for our case
val shrink_mul: #n:comp -> a:fen2 n -> b:fen2 n -> Lemma
  (shrink (a *% b) = shrink a *% shrink b)
let shrink_mul #n a b =
  to_fe_mul #n a b;
  modulo_modulo_lemma (a * b) n n

// to_fe_fexp specified for our case
val shrink_fexp: #n:comp -> g:fen2 n -> x:nat -> Lemma
  (shrink (fexp #(n*n) g x) = fexp #n (shrink g) x)
let shrink_fexp #n g x =
  cancel_mul_div n n;
  to_fe_fexp1 #(n*n) n g x

// Carmichael's function
val carm: p:prm -> q:prm -> l:fe (p*q){l <= (p-1) * (q-1) /\ l >= 1}
let carm p q = lcm_less_mul (p-1) (q-1); lcm (p-1) (q-1)

val carm_unit: p:prm -> q:prm -> Lemma
  (isunit #(p*q) (carm p q) /\ is_gcd (carm p q) (p*q) 1)
let carm_unit p q =
  // Any divisor of p*q has form kp or kq, but (p-1)(q-1) has none
  // of this form.
  assume (gcd (p * q) ((p - 1) * (q - 1)) = 1);

  gcd_pq_lcm_lemma p q;
  gcd_symm (p*q) (carm p q) 1;
  inv_as_gcd1 #(p*q) (carm p q)


// N plus one, for SMTPat not to throw warnings
val np1: #n:comp -> fen2 n
let np1 #n = 1 + n

// Paillier paper: p225 after definition 1
//
// (1 + n)^x = (x choose 0)*1 + (x choose 1)*n + sum{i>=2} (x choose i) * n^i
//           = 1 + xn
//
// The last sum cancels out because it has n^2 in each element of it.
val root_of_unity_form: #n:comp -> x:nat -> Lemma
  (fexp (np1 #n) x = 1 +% ((to_fe x) *% n))
let root_of_unity_form #n _ = admit()

// Another binomial expansion.
//
// (1 + xn)^n = (n choose 0)*1 + (n choose 1)*xn + (n choose 2)*(xn)^2 + ...
//            = 1 + xn^2 + (n choose 2) * x^2n^2 + ...
//            = 1
val root_of_unity_prop0: #n:comp -> x:fen2 n -> Lemma
  (fexp #(n*n) (1 +% (x *% n)) n = 1)
let root_of_unity_prop0 #n x = admit ()

val root_of_unity_prop: #n:comp -> x:fe n -> Lemma
  (fexp #(n*n) (1 + (x * n)) n = 1)
let root_of_unity_prop #n x =
  let n2 = n * n in
  assert (x * n < n2);
  assert (lift x *% n = x * n);
  assert (x * n + 1 < n2);
  to_fe_idemp #n2 (x * n + 1);
  assert (to_fe #n2 (x * n + 1) = x * n + 1);
  to_fe_add' #n2 1 (x * n);
  assert (( +% ) #n2 1 (x * n) = 1 + x * n);
  root_of_unity_prop0 #n (lift x)


#reset-options "--z3rlimit 100"

val kn_mod_n2: #n:comp -> k:fe (n*n) -> Lemma
  (k *% n = (k % n) * n)
let kn_mod_n2 #n k =
  pos_times_pos_is_pos n n;
  let n2:pos = n * n in
  distributivity_add_left ((k/n)*n2) (k%n) n;
  assert(((k/n)*n + (k%n)) * n = (k/n)*n2 + (k%n)*n);
  assert((((k/n)*n + (k%n)) * n)%n2 = ((k/n)*n2 + (k%n)*n)%n2);
  modulo_distributivity ((k/n)*n2) ((k%n)*n) n2;
  cancel_mul_mod (k/n) n2;
  lemma_mod_twice ((k%n)*n) n;
  modulo_range_lemma k n;
  assert(k%n < n);
  multiplication_order_lemma_strict (k%n) n n;
  assert((k%n)*n < n*n);
  modulo_lemma ((k%n)*n) n2

#reset-options

val x_mod_n_limits: #n:comp -> x:nat -> Lemma
   (to_fe #(n*n) (1 + (x % n) * n) == 1 + (x % n) * n)
let x_mod_n_limits #n x =
  assert(1 + (x%n)*n < n*n);
  modulo_lemma (1+(x%n)*n) (n*n)

val roots_of_unity_mod_n: #n:comp -> x:nat -> Lemma
  (fexp (np1 #n) x = 1 + (x % n) * n)
let roots_of_unity_mod_n #n x =
  let n2 = n*n in
  root_of_unity_form #n x;
  x_mod_n_limits #n x;
  assert(to_fe #(n*n) (1 + (x % n) * n) == 1 + (x % n) * n);
  calc (==) {
    1 +% ((to_fe #n2 x) *% n);
  == { to_fe_add' 1 (to_fe #n2 x *% n) }
    to_fe (1 + ((to_fe #n2 x) *% n));
  == { to_fe_mul' (to_fe #n2 x) n }
    to_fe (1 + to_fe #n2 (to_fe #n2 x * n));
  == { }
    to_fe (1 + (x % n2 * n) % n2);
  == { kn_mod_n2 #n (x % n2) }
    to_fe (1 + ((x % n2) % n) * n);
  == { modulo_modulo_lemma x n n }
    to_fe #(n*n) (1 + (x % n) * n);
  == { }
    1 + (x % n) * n;
  }


val in_base_order: p:prm -> q:prm -> g:fe ((p*q)*(p*q)){isunit g} -> Type0
let in_base_order p q g =
  let r = mult_order g in
  let n = p * q in
  r % n = 0 /\ (r / n > 0) /\ (r / n < carm p q)

val in_base: p:prm -> q:prm -> g:fe ((p*q)*(p*q)) -> Type0
let in_base p q g = g <> 0 /\ isunit g /\ in_base_order p q g

val is_g: n:big -> g:fe (n*n) -> Type0
let is_g n g = isunit g /\ (exists (p:prm) (q:prm). n = p * q /\ in_base p q g)

type isg (n:big) = g:fe (n*n){is_g n g}

// simply move exists, needs the fact that factorisation is unique
val is_g_in_base: p:prm -> q:prm -> g:fe ((p*q)*(p*q)) -> Lemma
  (requires (is_g (p*q) g))
  (ensures (in_base p q g))
let is_g_in_base p q g = admit ()

val np1_is_unit: #n:comp -> Lemma (isunit (np1 #n)) [SMTPat (np1 #n)]
let np1_is_unit #n =
  let g = np1 #n in
  assert (g <> 0);
  root_of_unity_prop #n 1;
  one_isunit (n*n);
  assert (isunit (fexp g n));
  g_pow_isunit_rev #(n*n) g n;
  assert (isunit g)

#reset-options "--z3rlimit 100"

val np1_is_primitive_root: #n:comp -> Lemma (mult_order (np1 #n) = n)
let np1_is_primitive_root #n =
  let g = np1 #n in
  comp_elim n #(mult_order g = n) (fun p q ->
    let r = mult_order g in
    root_of_unity_prop #n 1;

    let l (x:fe n{x>0}): Lemma (fexp g x <> 1) = begin
      to_fe_idemp x;
      roots_of_unity_mod_n #n x;
      assert (fexp g x = 1 + x * n);
      assert (fexp g x > 1)
    end in

    forall_intro l;
    assert (forall (x:fe n{x>0}). fexp g x <> 1);
    assert (fexp g n = 1);
    assert (is_mult_order g n);
    mult_order_unique g r n
  )

#reset-options

val np1_is_g: #n:comp -> Lemma (is_g n (np1 #n))
let np1_is_g #n =
  let g = np1 #n in
  np1_is_unit #n;
  let r = mult_order g in
  np1_is_primitive_root #n;
  assert (r = n);
  multiple_division_lemma 1 n


// This is a basic property of carmichael function.
val euler_thm: p:prm -> q:prm -> w:fe (p*q) -> Lemma
  (isunit w ==> fexp w (carm p q) = 1)
let euler_thm _ _ _ = admit()

// Slightly different version mentioned at p.224
val euler_thm2: p:prm -> q:prm -> w:fen2 (p*q) -> Lemma
  (requires (isunit w \/ isunit (to_fe #(p*q) w)))
  (ensures (
     fexp w (carm p q) % (p*q) = 1 /\
     fexp w (carm p q) > 0))
let euler_thm2 p q w =
  let n = p * q in

  multiple_modulo_lemma n n;
  multiple_division_lemma n n;
  assert ((n*n)%n = 0);
  assert ((n*n)/n = n);
  to_fe_fexp1 #(n*n) n w (carm p q);
  assert (fexp (to_fe #n w) (carm p q) = fexp w (carm p q) % n);

  move_requires #(fen2 n) #(fun a -> isunit a)
      #(fun a -> isunit (to_fe #n a))
      (isunit_in_nsquare2 #n)
      w;

  assert (isunit (to_fe #n w));

  euler_thm p q (to_fe #n w);
  assert (fexp w (carm p q) % (p*q) = 1)

// Carmichael-like thm, deals with cases modulo n^2
val euler_thm3: p:prm -> q:prm -> w:fen2 (p*q) -> Lemma
  (requires isunit (to_fe #(p*q) w))
  (ensures fexp w ((p*q)*carm p q) = 1)
let euler_thm3 p q w =
  let n:comp = p * q in
  let n2 = n * n in

  euler_thm2 p q w;

  let f1 = fexp w (carm p q) in
  assert (f1 % n = 1);
  mod_prop n f1 1;
  assert (f1 = 1 + (f1 / n) * n);
  fexp_exp w (carm p q) n;
  assert (fexp w (n*carm p q) = fexp f1 n);
  lemma_div_le_strict #n f1;
  assert (f1 / n < n);
  root_of_unity_prop #n (f1/n);
  assert (fexp #n2 (1 + (f1/n)*n) n = 1);
  assert (fexp f1 n = 1)

val fermat_inverse_carm:
     p:prm
  -> q:prm
  -> a:fe (p*q)
  -> b:fe (p*q){isunit a ==> (isunit b /\ a *% b = 1 /\ b = finv a)}
let fermat_inverse_carm p q a =
  let n = p * q in
  let b = fexp a (carm p q - 1) in
  fexp_mul1 a (carm p q - 1) 1;
  fexp_one1 a;
  euler_thm p q a;

  finv_unique #n a b;

  b

val encf_raw: #n:comp -> g:isg n -> x:nat -> y:fen2 n -> fen2 n
let encf_raw #n g x y = fexp g x *% fexp y n

val encf: #n:comp -> g:isg n -> x:fe n -> y:fenu n -> fen2 n
let encf #n g x y = encf_raw #n g x (lift y)

val encf_y_unit_raw0:
     #n:comp
  -> y:fen2 n { isunit (shrink y) }
  -> Lemma
  (let k = to_fe #(n*n) (((shrink y)*(finv (shrink y)))/n) in
   lift (shrink y) *% lift (finv (shrink y)) = 1 +% k *% n)
let encf_y_unit_raw0 #n y =
  let n2 = n * n in

  let a = shrink y in
  let b = finv a in

  mod_prop n (a * b) 1;
  assert (a * b = 1 + ((a*b)/n) * n);

  assert (lift a *% lift b = (a * b) % n2);
  assert (lift a *% lift b = (1 + ((a*b)/n) * n) % n2);
  modulo_distributivity 1 (((a*b)/n)*n) n2;
  modulo_lemma 1 n2;
  assert (lift a *% lift b = (1 + (((a*b)/n) * n)%n2) % n2);
  modulo_mul_distributivity ((a*b)/n) n n2;
  modulo_lemma n n2;
  assert ((((a*b)/n) * n)%n2 = (to_fe #n2 ((a*b)/n)) *% n);
  assert (lift a *% lift b = (1 + (to_fe #n2 ((a*b)/n)) *% n) % n2);
  assert (lift a *% lift b = 1 +% (to_fe #n2 ((a*b)/n)) *% n)

#reset-options "--z3rlimit 100"

val encf_y_unit_raw:
     #n:comp
  -> y:fen2 n { isunit (shrink y) }
  -> Lemma
  (fexp y n *% fexp (lift (finv (shrink y))) n = 1)
let encf_y_unit_raw #n y =
  let n2 = n * n in
  assert (n < n2);
  let y' = lift (finv (shrink y)) in
  fexp_mul2 y y' n;

  let k:fen2 n = to_fe #(n*n) (((shrink y)*(finv (shrink y)))/n) in
  lemma_div_le_strict y;
  let y_n:fen2 n = lift (y/n) in

  let lemma1 (): Lemma (y *% y' = 1 +% (k +% (y_n *% y')) *% n) = begin
      lemma_div_mod y n;
      assert (y = shrink y + n * (y / n));
      to_fe_idemp #n2 (shrink y);
      assert (to_fe #n2 (shrink y) = shrink y);
      to_fe_idemp_raw n2 (n * (y/n));
      assert (to_fe #n2 (n * (y/n)) = n * (y/n));
      to_fe_add #n2 (shrink y) (n * (y/n));
      let l1:fe n2 = lift (shrink y) in
      let l2:fe n2 = n * (y/n) in
      to_fe_idemp #n2 (shrink y + n * (y/n));
      assert (y = l1 +% l2);
      mul_add_distr_l #(n*n) l1 l2 y';
      assert (y *% y' = (l1 *% y') +% (l2 *% y'));
      encf_y_unit_raw0 #n y;
      assert (y *% y' = (1 +% (k *% n)) +% ((n * (y/n)) *% y'));
      to_fe_idemp #n2 (n * (y/n));
      to_fe_idemp #n2 n;
      to_fe_idemp #n2 (y/n);
      to_fe_mul #n2 n (y/n);
      assert (y *% y' = (1 +% k *% n) +% ((n *% (y/n)) *% y'));
      assert (y *% y' = (1 +% n *% k) +% ((n *% (y/n)) *% y'));
      assert (y *% y' = 1 +% (n *% k +% n *% (y_n *% y')));
      mul_add_distr_r n k (y_n *% y');
      assert (y *% y' = 1 +% (k +% (y_n *% y')) *% n)
    end in

  lemma1 ();

  root_of_unity_prop0 #n (k +% (y_n *% y'));
  assert (fexp (y *% y') n = 1)

#reset-options "--z3rlimit 100"

val encf_y_unit: #n:comp -> y:fenu n -> Lemma
  (fexp (lift y) n *% fexp (lift (finv y)) n = 1)
let encf_y_unit #n y = encf_y_unit_raw #n (lift y)

val encf_unit_raw: #n:comp -> g:isg n -> x:nat -> y:fen2 n{isunit (shrink y)} -> Lemma
  (isunit #(n*n) (encf_raw #n g x y))
let encf_unit_raw #n g x y =

  if x = 0 then (fexp_zero2 g; one_isunit n) else g_pow_isunit g x;
  assert(isunit (fexp g x));

  encf_y_unit_raw #n y;

  isunit_prod (fexp g x) (fexp y n)

val encf_unit: #n:comp -> g:isg n -> x:fe n -> y:fenu n -> Lemma
  (isunit #(n*n) (encf #n g x y))
let encf_unit #n g x y = encf_unit_raw g x (lift y)

val encf_inj_raw1:
     p:prm
  -> q:prm
  -> g:isg (p*q)
  -> x1:nat
  -> y1:fen2 (p*q) { isunit (shrink y1) }
  -> x2:nat
  -> y2:fen2 (p*q)
  -> Lemma
  (requires (encf_raw g x1 y1 = encf_raw g x2 y2))
  (ensures (let lambda = carm p q in
            let r = mult_order g in
            let n = p * q in
       fexp g (r - x1%r + x2%r) *%
       fexp (y2 *% lift (finv (shrink y1))) n = 1 /\

       (nat_times_nat_is_nat (r - (x1%r) + (x2%r)) lambda;
        nat_times_nat_is_nat n lambda;
        fexp g ((r - x1%r + x2%r) * lambda) *%
        fexp (y2 *% lift (finv (shrink y1))) (n*lambda) = 1)
   ))
let encf_inj_raw1 p q g x1 y1' x2 y2' =
  let lambda = carm p q in
  let n = p * q in
  let y1:fenu n = shrink y1' in
  let y2:fe n = shrink y2' in
  assert (fexp g x1 *% fexp y1' n = fexp g x2 *% fexp y2' n);
  let r = mult_order g in
  g_pow_order_reduc g x1;
  g_pow_order_reduc g x2;
  let x1 = x1 % r in
  let x2 = x2 % r in

  encf_y_unit #n y1;
  let fy = finv y1 in
  let fy' = lift fy in

  let lemma1 (): Lemma
   (fexp g (r - x1 + x2) *% (fexp (y2' *% fy') n) = 1 /\
    fexp (fexp g (r - x1 + x2)) lambda *% fexp (fexp (y2' *% fy') n) lambda = 1) = begin

      g_pow_inverse g x1;
      let z1 = fexp g (r - (x1 % r)) in

      assert ((z1 *% fexp g x1) *% fexp y1' n = z1 *% (fexp g x2 *% fexp y2' n));
      assert (fexp y1' n = (z1 *% fexp g x2) *% fexp y2' n);

      assert (fexp y1' n *% fexp fy' n = (z1 *% fexp g x2) *% (fexp y2' n *% fexp fy' n));
      encf_y_unit_raw #n y1';
      assert ((z1 *% fexp g x2) *% (fexp y2' n *% fexp fy' n) = 1);

      to_fe_idemp #r x1;
      fexp_mul1 g (r - x1) x2;
      assert (fexp g (r - x1 + x2) *% (fexp y2' n *% fexp fy' n) = 1);

      fexp_mul2 y2' fy' n;
      assert (fexp g (r - x1 + x2) *% fexp (y2' *% fy') n = 1);

      assert (fexp (fexp g (r - x1 + x2) *% fexp (y2' *% fy') n) lambda = fexp 1 lambda);
      fexp_one2 #(n*n) lambda;
      assert (fexp (fexp g (r - x1 + x2) *% fexp (y2' *% fy') n) lambda = 1);
      fexp_mul2 (fexp g (r - x1 + x2)) (fexp (y2' *% fy') n) lambda
  end in

  nat_times_nat_is_nat (r - x1 + x2) lambda;
  nat_times_nat_is_nat n lambda;

  let lemma2 (): Lemma (fexp g ((r - x1 + x2) * lambda) *% fexp (y2' *% fy') (n*lambda) = 1) = begin
      lemma1 ();
      fexp_exp g (r - x1 + x2) lambda;
      assert (fexp (fexp g (r - x1 + x2)) lambda = fexp g ((r - x1 + x2) * lambda));
      assert (fexp g ((r - x1 + x2) * lambda) *% fexp (fexp (y2' *% fy') n) lambda = 1);
      fexp_exp (y2' *% fy') n lambda;
      assert (fexp g ((r - x1 + x2) * lambda) *% fexp (y2' *% fy') (n * lambda) = 1)
  end in

  lemma1 ();
  lemma2 ()


val divides_over_higher_mod: n:big -> alpha:pos -> x1:nat -> x2:nat -> Lemma
  (requires (x2 % (alpha*n) - x1 % (alpha*n)) % n = 0)
  (ensures (x2 - x1) % n = 0)
let divides_over_higher_mod n alpha x1 x2 =
  let r = alpha * n in
  let s = x2 % r - x1 % r in
  mod_prop n s 0;
  assert (x2 % r = x1 % r + n * (s / n));
  mod_prop r x2 (x1 % r + n * (s / n));
  assert (x2 - (x1 % r + n * (s / n)) = (x2 / r) * r );
  assert (x1 % r = x2 - (x2 / r) * r - n * (s/n));
  mod_prop r x1 (x2 - (x2 / r) * r - n * (s/n));
  assert (x2 - x1 = n * ( (x2 / r) * alpha + (s/n) - (x1 / r) * alpha));
  cancel_mul_mod ((x2 / r) * alpha + (s/n) - (x1 / r) * alpha) n;
  assert (divides n (x2 - x1))

#reset-options "--z3rlimit 150"

val encf_inj_raw2:
     p:prm
  -> q:prm
  -> g:isg (p*q)
  -> x1:nat
  -> y1:fen2 (p*q) { isunit (shrink y1) }
  -> x2:nat
  -> y2:fen2 (p*q) { isunit (shrink y2) }
  -> Lemma
  (requires (encf_raw g x1 y1 = encf_raw g x2 y2))
  (ensures (let r = mult_order g in

    nat_times_nat_is_nat (r - (x1%r) + (x2%r)) (carm p q);

    fexp g ((r - (x1%r) + (x2%r)) * (carm p q)) = 1 /\
    (x2 - x1) % (p*q) = 0 /\
    (x2 % r - x1 % r) % (p*q) = 0))
let encf_inj_raw2 p q g x10 y1' x20 y2' =

  encf_inj_raw1 p q g x10 y1' x20 y2';

  let lambda = carm p q in
  let n = p * q in
  let r = mult_order g in
  g_pow_order_reduc g x10;
  g_pow_order_reduc g x20;

  let x1 = x10 % r in
  let x2 = x20 % r in

  nat_times_nat_is_nat (r - x1 + x2) lambda;


  let remove_ys (): Lemma (fexp g ((r - x1 + x2) * lambda) = 1) = begin
    let y1 = shrink y1' in
    let y2 = shrink y2' in
    let fy = finv y1 in
    let fy' = lift fy in

    assert (fexp g ((r - x1 + x2) * lambda) *% fexp (y2' *% fy') (n*lambda) = 1);

    fexp_mul2 y2' fy' (n*lambda);
    assert (fexp (y2' *% fy') (n*lambda) = fexp y2' (n*lambda) *% fexp fy' (n*lambda));

    euler_thm3 p q y2';
    encf_y_unit_raw y1';
    euler_thm3 p q fy';
    assert (fexp (y2' *% fy') (n*lambda) = 1);
    mul_one (fexp g ((r - x1 + x2) * lambda))
    end in

  remove_ys ();

  is_g_in_base p q g;
  let alpha = r / n in
  assert (r % n = 0 /\ alpha > 0 /\ alpha < lambda);
  lemma_div_mod r n;
  assert (r = alpha * n);

  mult_order_divides g ((r - x1 + x2) * lambda);
  divides_prod alpha n ((r - x1 + x2) * lambda);
  assert (divides n ((r - x1 + x2) * lambda));

  carm_unit p q;
  divides_exactly_one_multiple n (r - x1 + x2) lambda;
  assert (divides n (r - x1 + x2));

  modulo_distributivity r (x2 - x1) n;
  assert (divides n ((x2 - x1) % n));
  modulo_modulo_lemma (x2 - x1) n 1;
  assert (divides n (x2 - x1));

  divides_over_higher_mod n alpha x10 x20

#reset-options

val encf_inj_raw_partial:
     #n:comp
  -> g:isg n
  -> x1:nat
  -> y1:fen2 n { isunit (shrink y1) }
  -> x2:nat
  -> y2:fen2 n { isunit (shrink y2) }
  -> Lemma
  (requires (encf_raw g x1 y1 = encf_raw g x2 y2))
  (ensures to_fe #n x2 = to_fe #n x1)
let encf_inj_raw_partial #n g x1 y1 x2 y2 =
  comp_elim n #((x2 - x1) % n = 0) (fun p q -> encf_inj_raw2 p q g x1 y1 x2 y2);
  assert ((x2 - x1) % n = 0);
  to_fe_sub #n x2 x1;
  assert (to_fe #n x2 -% to_fe #n x1 = 0);
  add_move_to_right #n (to_fe #n x2) (to_fe #n x1) 0;
  add_sub_zero (to_fe #n x1)

// We only need injectivity on xs
val encf_inj: #n:comp -> g:isg n -> x1:fe n -> y1:fenu n -> x2:fe n -> y2:fenu n -> Lemma
  (requires (encf g x1 y1 = encf g x2 y2))
  (ensures (x1 = x2))
let encf_inj #n g x1 y1 x2 y2 =
  to_fe_idemp #n x1;
  to_fe_idemp #n x2;
  encf_inj_raw_partial #n g x1 (lift y1) x2 (lift y2)

// It is possible to get it checking every element of the preimage.
// encf is bijection for proper g
val encf_inv: #n:comp -> g:isg n -> w:fen2 n ->
  t:(tuple2 (fe n) (fenu n)){ encf g (fst t) (snd t) = w }
let encf_inv #n g w =
  if w = g
  then begin
    let x:fe (n*n) = one in
    let y:fe n = one in
    let y':fe (n*n) = one in

    fexp_one1 g;
    assert(fexp g one = g);
    fexp_one2 #(n*n) y;
    assert(fexp y' n = one);
    assert(fexp g one *% fexp y' n = g);
    assert(encf g x y = g);
    Mktuple2 x y
  end else magic() // it's hard to invert it

type is_res_class (#n:comp) (g:isg n) (w:fen2u n) (x:fe n) =
  exists (y:(t:fen2 n{isunit (shrink t)})). encf_raw g x y = w

val is_res_class_of_encf_raw: #n:comp -> g:isg n -> x:fe n -> y:fen2 n{isunit (shrink y)} -> Lemma
  (encf_unit_raw g x y; is_res_class g (encf_raw g x y) x)
let is_res_class_of_encf_raw #n g x y =
  let func (y':fen2 n): Type =  encf_raw g x y' = encf_raw g x y in
  exists_intro func y

val res_class_elim:
     #n:comp
  -> #goal:Type0
  -> g:isg n
  -> w:fen2u n
  -> x:fe n{is_res_class #n g w x}
  -> f:((y:fen2 n{isunit (shrink y) /\ encf_raw g x y = w}) -> squash goal)
  -> Lemma goal
let res_class_elim #n #goal g w x f =
  let l (): Lemma (is_res_class g w x) = () in
  exists_elim goal #(t:fen2 n{isunit (shrink t)}) #(fun y -> encf_raw g x y = w) (l ()) f

val res_class: #n:comp -> g:isg n -> w:fen2u n -> x:fe n{is_res_class g w x}
let res_class #n g w = fst (encf_inv g w)

// We invert twice and apply injectivity.
val res_class_is_unique: #n:comp -> g:isg n -> w:fen2u n -> x:fe n -> Lemma
  (requires is_res_class g w x)
  (ensures res_class g w = x)
let res_class_is_unique #n g w x =
  let x' = res_class g w in

  let goal = x' = x in

  let proof (y:fen2 n{isunit (shrink y) /\ encf_raw g x y = w})
            (y':fen2 n{isunit (shrink y') /\ encf_raw g x' y' = w}):
            Lemma goal = begin
      encf_inj_raw_partial g x y x' y';
      to_fe_idemp #n x;
      to_fe_idemp #n x'
    end in

  res_class_elim #n #goal g w x (fun y ->
    res_class_elim #n #goal g w x' (fun y' ->
      proof y y'))

val res_class_of_encf_raw: #n:comp -> g:isg n -> x:fe n -> y:fen2 n{isunit (shrink y)} -> Lemma
  (encf_unit_raw g x y; res_class g (encf_raw g x y) = x)
let res_class_of_encf_raw #n g x y =
  is_res_class_of_encf_raw g x y;
  encf_unit_raw g x y;
  res_class_is_unique g (encf_raw g x y) x

#reset-options "--z3rlimit 150"

val res_class_decomposition: #n:comp -> g1:isg n -> g2:isg n ->  w:fen2u n -> Lemma
  (ensures (res_class g1 w = res_class g2 w *% res_class g1 g2))
let res_class_decomposition #n g1 g2 w =
  let (x1,y1) = encf_inv g1 w in
  let (x2,y2) = encf_inv g2 w in
  let (x3,y3) = encf_inv g1 g2 in
  let y1':fen2 n = lift y1 in
  let y2':fen2 n = lift y2 in
  let y3':fen2 n = lift y3 in


  nat_times_nat_is_nat x3 x2;
  nat_times_nat_is_nat n x2;

  let encf_expand1 (): Lemma
      (encf_raw g1 x1 y1' =
       (fexp (fexp g1 x3 *% fexp y3' n) x2) *% fexp y2' n) =
    calc (==) {
      encf_raw g1 x1 y1';
    == { }
      encf_raw (encf_raw g1 x3 y3) x2 y2';
    == { }
      encf_raw (fexp g1 x3 *% fexp y3' n) x2 y2';
    == { }
      (fexp (fexp g1 x3 *% fexp y3' n) x2) *% fexp y2' n;
    } in


  let encf_expand2 (): Lemma
      (encf_raw g1 (x3 * x2) (fexp y3' x2 *% y2') =
       (fexp (fexp g1 x3 *% fexp y3' n) x2) *% fexp y2' n) = begin
    calc (==) {
      (fexp (fexp g1 x3 *% fexp y3' n) x2) *% fexp y2' n;
    == { fexp_mul2 (fexp g1 x3) (fexp y3' n) x2 }
      ((fexp (fexp g1 x3) x2) *% (fexp (fexp y3' n) x2)) *% fexp y2' n;
    == { fexp_exp g1 x3 x2 }
      (fexp g1 (x3 * x2) *% fexp (fexp y3' n) x2) *% fexp y2' n;
    == { }
      (fexp g1 (x3 * x2)) *% ((fexp (fexp y3' n) x2) *% fexp y2' n);
    == { fexp_exp y3' n x2 }
      (fexp g1 (x3 * x2)) *% (fexp y3' (n * x2) *% fexp y2' n);
    == { fexp_exp y3' x2 n }
      (fexp g1 (x3 * x2)) *% (fexp (fexp y3' x2) n *% fexp y2' n);
    == { fexp_mul2 (fexp y3' x2) y2' n }
      (fexp g1 (x3 * x2)) *% (fexp (fexp y3' x2 *% y2') n);
    }
    end in


  encf_expand1 ();
  encf_expand2 ();

  assert (encf_raw g1 x1 y1' = encf_raw g1 (x3 * x2) (fexp y3' x2 *% y2'));

  let second_y_is_unit (): Lemma (isunit (shrink (fexp y3' x2 *% y2'))) = begin
      shrink_mul (fexp y3' x2) y2';
      shrink_fexp y3' x2;
      assert (shrink (fexp y3' x2 *% y2') = fexp y3 x2 *% y2);
      g_pow_isunit y3 x2;
      isunit_prod (fexp y3 x2) y2
    end in

  assert (isunit (shrink y1'));
  second_y_is_unit ();
  encf_inj_raw_partial g1 x1 y1' (x3 * x2) (fexp y3' x2 *% y2');
  to_fe_idemp #n x1;
  to_fe_mul' x3 x2;
  assert(x1 = x3 *% x2)

val res_class_inverse: #n:comp -> g1:isg n -> g2:isg n -> Lemma
  (isunit (res_class g1 g2) /\
   finv (res_class g1 g2) = res_class g2 g1)
let res_class_inverse #n g1 g2 =
  res_class_decomposition g1 g2 g1;
  assert(res_class g1 g1 = one);
  finv_unique (res_class g1 g2) (res_class g2 g1)

#reset-options

val res_class_modulo_encf:
     #n:comp
  -> g:isg n
  -> x1:fe n
  -> y1:fenu n
  -> x2:nat
  -> y2:fen2 n{isunit (shrink y2)}
  -> Lemma
  (requires x2 % n = x1)
  (ensures (encf_unit g x1 y1; encf_unit_raw g x2 y2;
           res_class g (encf g x1 y1) = res_class g (encf_raw g x2 y2)))
let res_class_modulo_encf #n g x1 y1 x2 y2 =
  division_definition_lemma_2 x2 n 0;
  assert (x2/n >= 0);

  let lemma1 (): Lemma (encf_raw g x2 y2 = encf_raw g x1 (fexp g (x2/n) *% y2)) = begin
      mod_prop n x2 x1;
      assert (x2 = x1 + (x2/n) * n);
      assert (isunit (shrink y2));
      assert (encf_raw g x2 y2 = fexp g x2 *% fexp y2 n);
      nat_times_nat_is_nat (x2/n) n;
      fexp_mul1 g x1 ((x2/n)*n);
      assert (encf_raw g x2 y2 = fexp g x1 *% fexp g ((x2/n)*n) *% fexp y2 n);
      fexp_exp g (x2/n) n;
      assert (encf_raw g x2 y2 = fexp g x1 *% (fexp (fexp g (x2/n)) n) *% fexp y2 n);
      fexp_mul2 (fexp g (x2/n)) y2 n;
      assert (encf_raw g x2 y2 = fexp g x1 *% fexp (fexp g (x2/n) *% y2) n);
      assert (encf_raw g x2 y2 = encf_raw g x1 (fexp g (x2/n) *% y2))
  end in

  lemma1 ();


  encf_unit_raw g x1 (lift y1);

  let y3:fen2 n = fexp g (x2/n) *% y2 in

  let y3_is_unit (): Lemma (isunit (shrink (fexp g (x2/n) *% y2))) = begin
      shrink_mul (fexp g (x2/n)) y2;
      shrink_fexp g (x2/n);
      assert (shrink (fexp g (x2/n) *% y2) = fexp (shrink g) (x2/n) *% (shrink y2));
      isunit_in_nsquare2 g;
      g_pow_isunit (shrink g) (x2/n);
      isunit_prod (fexp (shrink g) (x2/n)) (shrink y2)
    end in

  y3_is_unit ();

  let w3 = encf_raw g x1 y3 in
  encf_unit_raw g x1 y3;
  res_class_of_encf_raw #n g x1 y3;
  assert (res_class g w3 = x1);

  assert (res_class g (encf_raw g x2 y2) = x1);
  res_class_of_encf_raw g x1 (lift y1);
  assert (res_class g (encf_raw g x1 (lift y1)) = x1)

val bigl: #n:comp -> u:fen2 n{u > 0} -> r:fe n
let bigl #n u = (u - 1) / n

val bigl_prop: #n:comp -> u:fen2 n{u > 0} -> Lemma
  (ensures (let r = bigl u in u % n = 1 ==> (r = 0 <==> u = 1)))
let bigl_prop #n u =
  let r = bigl u in
  assert(u = 1 ==> r = 0);
  assert(u % n = 1 ==> (r = 0 ==> u = 1));
  assert(u % n = 1 ==> (r = 0 <==> u = 1))

val w_lambda_representation: p:prm -> q:prm -> w:fen2u (p*q) -> Lemma
  (let n = p * q in
   np1_is_g #n;
   let a = res_class np1 w in
   let lm:fe n = carm p q in
   fexp w lm = 1 + ((a*lm)%n)*n)
let w_lambda_representation p q w =
  let n:comp = p * q in
  let lambda:pos = carm p q in
  np1_is_g #n;
  let (a,b) = encf_inv (np1 #n) w in

  //must be unit
  let b': fen2 n = lift b in
  assert (w = fexp (np1 #n) a *% fexp b' n);

  pos_times_pos_is_pos n lambda;
  nat_times_nat_is_nat a lambda;

  roots_of_unity_mod_n #n (a * lambda);
  assert (fexp (np1 #n) (a * lambda) = 1 + ((a*lambda) % n)*n);

  calc (==) {
    fexp w lambda;
  == { fexp_mul2 (fexp (np1 #n) a) (fexp b' n) lambda }
    (fexp (fexp np1 a) lambda) *% (fexp (fexp b' n) lambda);
  == { fexp_exp b' n lambda }
    (fexp (fexp np1 a) lambda) *% (fexp b' (n*lambda));
  == { euler_thm3 p q b' }
    fexp (fexp np1 a) lambda *% one;
  == { mul_one (fexp (fexp (np1 #n) a) lambda) }
    fexp (fexp np1 a) lambda;
  == { fexp_exp (np1 #n) a lambda }
    fexp (np1 #n) (a * lambda);
  == { }
    1 + ((a*lambda)%n)*n;
  }


// lemma 10 p227
val bigl_w_l_lemma: p:prm -> q:prm -> w:fen2u (p*q) -> Lemma
  (ensures (let n = p * q in
            np1_is_g #n;
            let x = res_class np1 w in
            let lm:fe n = carm p q in
            euler_thm2 p q w;
            bigl (fexp w lm) = lm *% x))
let bigl_w_l_lemma p q w =
  let n:comp = p * q in
  let lambda:fe n = carm p q in
  np1_is_g #n;
  let a:fe n = res_class (np1 #n) w in
  w_lambda_representation p q w;

  let d:fen2 n = (1 + ((a * lambda) % n) * n) in
  assert(d > 0);

  calc (==) {
    bigl #n d;
  == { }
    (((a * lambda) % n) * n) / n;
  == { cancel_mul_div ((a * lambda) % n) n }
    (a * lambda) % n;
  == { to_fe_mul #n a lambda }
    to_fe #n a *% to_fe #n lambda;
  == { to_fe_idemp #n a }
    a *% to_fe lambda;
  == { to_fe_idemp #n lambda }
    a *% lambda;
  }


val l1_div_l2: p:prm -> q:prm -> w:fen2 (p*q) -> g:isg (p*q) -> fe (p*q)
let l1_div_l2 p q w g =
  let n = p * q in
  let lambda: fe n = carm p q in
  let l1arg = fexp w lambda in
  // If w is not guaranteed to be unit, then we could
  // possibly get 0, which is not a proper input to L.
  //
  // TODO decryption of non-units is nonstandard and should
  // be re-considered at some point.
  if l1arg = 0 then 0 else begin
    let l1:fe n = bigl l1arg in
    g_pow_isunit g lambda; isunit_nonzero (fexp g lambda);
    let l2:fe n = bigl (fexp g lambda) in

    l1 *% fermat_inverse_carm p q l2
  end


val l1_div_l2_of_unit_w: p:prm -> q:prm -> w:fen2u (p*q) -> g:isg (p*q) -> Lemma
  (let lambda = carm p q in
   isunit (fexp w lambda) /\ (fexp w lambda > 0) /\
   isunit (fexp g lambda) /\ (fexp g lambda > 0) /\
   (isunit_nonzero (fexp g lambda);
    isunit (bigl (fexp g lambda))))
let l1_div_l2_of_unit_w p q w g =
  let n = p * q in
  let lambda:fe n = carm p q in
  let exp_is_unit (a:fen2u n): Lemma (isunit (fexp a lambda)) =
    begin
    g_pow_isunit a lambda;
    isunit_nonzero (fexp a lambda);
    assert (isunit (fexp a lambda))
    end in

  exp_is_unit w;
  exp_is_unit g;
  isunit_nonzero (fexp g lambda);

  let bigl_is_unit (): Lemma (isunit (bigl (fexp g lambda))) =
    begin
    np1_is_g #n;
    bigl_w_l_lemma p q g;
    assert (bigl (fexp g lambda) = lambda *% res_class np1 g);
    carm_unit p q;
    res_class_inverse np1 g;
    isunit_prod lambda (res_class np1 g)
    end in

  bigl_is_unit ()


val fexp_w_lambda_is_one_mod_n: p:prm -> q:prm -> w:fen2u (p*q) -> Lemma
  (let lambda = carm p q in fexp w lambda % (p*q) = 1)
let fexp_w_lambda_is_one_mod_n p q w =
  let n:comp = p * q in
  one_mod_n n;
  let lambda:fe n = carm p q in
  np1_is_g #n;
  let a:fe n = res_class (np1 #n) w in
  w_lambda_representation p q w;
  assert (fexp w lambda = 1 + ((a*lambda)%n)*n);
  assert (fexp w lambda % n = (1 + (((a*lambda)%n)*n))%n);
  modulo_distributivity 1 (((a*lambda)%n)*n) n;
  assert (fexp w lambda % n = (1%n + (((a*lambda)%n)*n)%n)%n);
  cancel_mul_mod ((a*lambda)%n) n;
  assert ((((a*lambda)%n)*n)%n = 0);
  assert (fexp w lambda % n = (1%n)%n);
  lemma_mod_twice 1 n;
  assert (fexp w lambda % n = 1)

val l1_div_l2_is_wg: p:prm -> q:prm -> w:fen2u (p*q) -> g:isg (p*q) -> Lemma
  (l1_div_l2 p q w g = res_class g w)
let l1_div_l2_is_wg p q w g =
  let n = p * q in
  let lambda: fe n = carm p q in

  np1_is_g #n;
  let r_w = res_class #n np1 w in
  let r_g = res_class #n np1 g in
  let r_z = res_class #n g w in

  l1_div_l2_of_unit_w p q w g;
  let l1:fe n = bigl (fexp w lambda) in
  let l2:fe n = bigl (fexp g lambda) in

  fexp_w_lambda_is_one_mod_n p q w;
  fexp_w_lambda_is_one_mod_n p q g;

  bigl_prop (fexp w lambda);
  bigl_prop (fexp g lambda);


  bigl_w_l_lemma p q w;
  assert (l1 = lambda *% r_w);
  bigl_w_l_lemma p q g;
  assert (l2 = lambda *% r_g);

  res_class_decomposition (np1 #n) g w;
  assert (r_w = r_g *% r_z);

  res_class_inverse np1 g;

  finv_mul r_w r_g r_z;
  assert (r_w *% finv r_g = r_z);

  carm_unit p q;
  let lem1 (): Lemma (isunit l2 /\ finv l2 = finv lambda *% finv r_g) =
    isunit_prod lambda r_g in

  calc (==) {
    l1 *% finv l2;
   == { lem1 () }
    (lambda *% r_w) *% (finv lambda *% finv r_g);
   == { mul4_assoc lambda r_w (finv lambda) (finv r_g) }
    (lambda *% finv lambda) *% (r_w *% finv r_g);
   == { }
    one *% (r_w *% finv r_g);
   == { }
    r_w *% finv r_g;
   == { }
    r_z;
  }

#reset-options


(* Keys *)

type secret =
  | Secret: p:prm
         -> q:prm{q <> p}
         -> g:isg (p*q)
         -> secret

// TODO get rid of "comp" here
type public =
  | Public: n:comp
         -> g:isg n
         -> public

val s2p: secret -> public
let s2p sec =
  Public (Secret?.p sec * Secret?.q sec)
         (Secret?.g sec)


(* Enc/Dec/Hom *)

type ciphertext (n:comp) = c:fen2 n

val encrypt_direct: #n:comp -> g:isg n -> r:fenu n -> m:fe n -> ciphertext n
let encrypt_direct #n g r m = encf g m r

val encrypt:
     p:public
  -> r:fenu (Public?.n p)
  -> m:fe (Public?.n p)
  -> ciphertext (Public?.n p)
let encrypt pub r m = encrypt_direct (Public?.g pub) r m

val decrypt_direct:
     p:prm
  -> q:prm
  -> g:isg (p * q)
  -> c:ciphertext (p * q)
  -> m:fe (p * q)
let decrypt_direct p q g c = l1_div_l2 p q c g

val decrypt:
     s:secret
  -> c:ciphertext (Public?.n (s2p s))
  -> m:fe (Public?.n (s2p s))
let decrypt sec c = decrypt_direct (Secret?.p sec) (Secret?.q sec) (Secret?.g sec) c

// Corresponds to the modular addition of encrypted values
val hom_add: #n:comp -> c1:ciphertext n -> c2:ciphertext n -> c:ciphertext n
let hom_add #n c1 c2 = c1 *% c2

// Corresponds to the modular multiplication of encrypted value by plaintext k
val hom_mul_plain: #n:comp -> c1:ciphertext n -> k:fe n -> c:ciphertext n
let hom_mul_plain #n c1 k = fexp c1 k

(* Functional correctness and properties *)

val enc_is_unit:
     p:public
  -> r:fenu (Public?.n p)
  -> m:fe (Public?.n p)
  -> Lemma
  (isunit (encrypt p r m))
let enc_is_unit pub r m = encf_unit (Public?.g pub) m r

val decrypts_into_res_class:
     s:secret
  -> c:ciphertext (Public?.n (s2p s))
  -> Lemma
     (requires (isunit c))
     (ensures (decrypt s c = res_class (Secret?.g s) c))
let decrypts_into_res_class sec c =
  l1_div_l2_is_wg (Secret?.p sec) (Secret?.q sec) c (Secret?.g sec)


val ex_ys: #n:comp -> g:isg n -> x1:fe n -> x2:fe n -> y1:fenu n -> y2:fenu n -> bool
let ex_ys #n g x1 x2 y1 y2 = encf g x1 y1 = encf g x2 y2

type y_pair (#n:comp) : Type = tuple2 (fenu n) (fenu n)

val encf_inj_pair: #n:comp -> g:isg n -> x1:fe n -> x2:fe n -> Lemma
  (requires (exists y1 y2. encf g x1 y1 = encf g x2 y2))
  (ensures (x1 = x2))
let encf_inj_pair #n g x1 x2 =
  let ex_pair' y1 y2 = (encf g x1 y1 = encf g x2 y2) in

  let goal:Type = x1 = x2 in
  ex_pair (fenu n) ex_pair';
  let predicate (ys:y_pair):Type = ex_pair' (fst ys) (snd ys) in

  assert(exists (ys:y_pair #n). predicate ys);
  let ex: squash (exists (ys:y_pair #n). predicate ys) = () in

  let proof (ys:y_pair #n{predicate ys}): GTot (squash goal) =
    encf_inj g x1 (fst ys) x2 (snd ys) in

  exists_elim goal #(y_pair #n) #predicate ex proof

val enc_dec_id:
     s:secret
  -> r:fenu (Public?.n (s2p s))
  -> m:fe (Public?.n (s2p s))
  -> Lemma
  (ensures (decrypt s (encrypt (s2p s) r m) = m))
let enc_dec_id sec r m =
  let pub = s2p sec in
  let n = Public?.n pub in
  let g = Secret?.g sec in

  enc_is_unit pub r m;
  let c: fen2u n = encrypt (s2p sec) r m in
  assert(exists y1. encf g m y1 = c);
  let m' = decrypt sec c in
  let r_c = res_class g c in
  decrypts_into_res_class sec c;
  assert(r_c = m');

  assert(exists y1. encf g m y1 = c);
  assert(exists y2. encf g m' y2 = c);
  assert(exists y1 y2. encf g m y1 = encf g m' y2);
  encf_inj_pair g m m'

val hom_add_lemma:
     s:secret
  -> r1:fenu (Public?.n (s2p s))
  -> m1:fe (Public?.n (s2p s))
  -> r2:fenu (Public?.n (s2p s))
  -> m2:fe (Public?.n (s2p s))
  -> Lemma
  (let c1 = encrypt (s2p s) r1 m1 in
  (let c2 = encrypt (s2p s) r2 m2 in
   decrypt s (hom_add c1 c2) = m1 +% m2))
let hom_add_lemma s r1 m1 r2 m2 =
  let g = Secret?.g s in
  let p = Secret?.p s in
  let q = Secret?.q s in
  let n = p * q in
  let c1 = encrypt (s2p s) r1 m1 in
  let c2 = encrypt (s2p s) r2 m2 in
  assert (hom_add c1 c2 = encf_raw g m1 (lift r1) *% encf_raw g m2 (lift r2));
  assert (hom_add c1 c2 = fexp g m1 *% fexp (lift r1) n *% fexp g m2 *% fexp (lift r2) n);
  assert (hom_add c1 c2 = fexp g m1 *% fexp g m2 *% fexp (lift r1) n *% fexp (lift r2) n);
  fexp_mul1 g m1 m2;
  fexp_mul2 (lift r1) (lift r2) n;
  assert (hom_add c1 c2 = fexp g (m1 + m2) *% fexp (lift r1 *% lift r2) n);

  let r3:fen2 n = lift r1 *% lift r2 in
  let shrink_r3_is_unit (): Lemma (isunit (shrink r3)) = begin
      shrink_mul (lift r1) (lift r2);
      isunit_prod r1 r2
    end in
  shrink_r3_is_unit ();
  assert (hom_add c1 c2 = encf_raw g(m1+m2) r3);


  let goal = decrypt s (hom_add c1 c2) = m1 +% m2 in
  // stub encryption w/ same res class
  let w = fexp g ((m1+m2)%n) *% fexp r3 n in
  is_res_class_of_encf_raw g ((m1+m2)%n) r3;
  res_class_modulo_encf g ((m1 + m2)%n) (shrink r3) (m1+m2) r3;
  encf_unit g ((m1+m2)%n) (shrink r3);
  encf_unit_raw g ((m1+m2)%n) r3;
  encf_unit_raw g (m1+m2) r3;
  assert (res_class g (encf g ((m1+m2)%n) (shrink r3)) =
          res_class g (encf_raw g (m1+m2) r3));
  let y' = lift (shrink r3) in
  assert (encf g ((m1+m2)%n) (shrink r3) = encf_raw g ((m1+m2)%n) y');
  assert (res_class g (encf_raw g ((m1+m2)%n) y') = res_class g (encf_raw g (m1+m2) r3));
  res_class_of_encf_raw g ((m1+m2)%n) y';
  assert (res_class g (encf_raw g ((m1+m2)%n) y') = (m1+m2)%n);
  assert (res_class g (hom_add c1 c2) = (m1+m2)%n);
  decrypts_into_res_class s (hom_add c1 c2);
  assert (decrypt s (hom_add c1 c2) = (m1 + m2)%n);
  to_fe_add' m1 m2;
  assert (decrypt s (hom_add c1 c2) = m1 +% m2)
