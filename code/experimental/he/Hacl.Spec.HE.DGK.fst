module Hacl.Spec.HE.DGK

open FStar.Mul
open FStar.Math.Lemmas
open FStar.Classical

open Lib.Math.Algebra


val gcd_split_comp: p:prm -> q:prm -> h:pos{is_gcd (p*q) h 1} -> Lemma
  (is_gcd p h 1 /\ is_gcd q h 1)
let gcd_split_comp p q h =
  let (g,u,v) = ex_eucl (p*q) h in
  gcd_unique (p*q) h 1 g;
  assert ((p * q) * u + h * v = 1);

  swap_mul p q;
  paren_mul_left p q u;
  paren_mul_right p q u;
  assert (p * (q * u) + h * v = 1);
  ex_eucl_lemma3 p h (q * u) v;

  paren_mul_left q p u;
  paren_mul_right q p u;
  assert (q * (p * u) + v * h = 1);
  ex_eucl_lemma3 q h (p * u) v

val gcd_prod_is_more: a:pos -> b:pos -> c:pos -> g:pos -> Lemma
  (requires is_gcd a b g)
  (ensures gcd a (b * c) >= g)
let gcd_prod_is_more a b c g =
  assert (is_gcd a b g ==> is_common_divisor a b g);
  divides_mult g b c;
  assert (is_gcd a b g ==> is_common_divisor a (b*c) g)

#reset-options "--z3rlimit 50"

val unit_mod_comp_divisibility: p:prm -> q:prm -> h:fe (p*q){isunit h} -> Lemma
  (to_fe #p h <> 0)
let unit_mod_comp_divisibility p q h =

  let l (): Lemma (requires (h % p = 0))
                  (ensures (gcd h (p*q) <> 1)) =
          assert (h <> 0);
          assert (is_gcd h p p);
          gcd_prod_is_more h p q p;
          assert (gcd h (p * q) >= p);
          assert (p >= 3);
          assert (gcd h (p * q) >= 3)
          in

  move_requires l ();
  inv_as_gcd2 h

#reset-options

val isunit_comp: p:prm -> q:prm -> h:fe (p*q){isunit h} -> Lemma
  (isunit (to_fe #p h) /\ isunit (to_fe #q h))
let isunit_comp p q h =
  inv_as_gcd2 #(p*q) h;
  gcd_split_comp p q h;
  gcd_mod_reduce_big p h;
  gcd_mod_reduce_big q h;
  swap_mul p q;
  unit_mod_comp_divisibility p q h;
  unit_mod_comp_divisibility q p h;
  inv_as_gcd1 (to_fe #p h);
  inv_as_gcd1 (to_fe #q h)

type is_h (p:prm) (q:prm) (v:pos) (h:fe (p*q)) =
  isunit h /\
  (isunit_comp p q h; mult_order (to_fe #p h) = v /\ mult_order (to_fe #q h) = v)

// h^v = 1 mod q, p
// h^v = 1 + k*q
// h^v = 1 + m*p
// k * q - m * p = 0
// k * q = 0 mod p
// q /= 0 mod p, so k = 0 mod p,
// so k = s * p,
// so h^v = 1 + s*p*q


#reset-options "--z3rlimit 200"

val prm_mod_prm: a:prm -> b:prm{b <> a} -> Lemma (a % b <> 0)
let prm_mod_prm a b =
  let l (): Lemma (requires (a % b = 0)) (ensures False) = begin
    assert (divides b a);
    assert (~(isprm a))
  end in move_requires l ()

val mod_product_zero: a:int -> b:prm -> p:prm -> Lemma
  (requires (b <> p /\ (a * b) % p = 0))
  (ensures a % p = 0)
let mod_product_zero a b p =
  let l (): Lemma (requires (a % p <> 0)) (ensures False) = begin
    modulo_mul_distributivity a b p;
    assert ((a * b) % p = ((a % p) * (b % p)) % p);
    prm_mod_prm b p;
    prime_field_zerodivs #p (a % p) (b % p)
  end in move_requires l ()

val h_raise_v: p:prm -> q:prm{p <> q} -> v:pos -> h:fe (p*q){is_h p q v h} -> Lemma (fexp h v = 1)
let h_raise_v p q v h =
  swap_mul p q;

  let l1 (): Lemma (fexp h v = 1 + (fexp h v / p) * p /\
                    fexp h v = 1 + (fexp h v / q) * q) = begin
    isunit_comp p q h;

    multiple_modulo_lemma p q;
    multiple_division_lemma p q;
    to_fe_fexp1 #(p*q) q h v;
    mod_prop p (fexp h v) 1;

    multiple_modulo_lemma q p;
    multiple_division_lemma q p;
    to_fe_fexp1 #(p*q) p h v;
    mod_prop q (fexp h v) 1
    end in

  l1 ();

  let l2 (): Lemma (fexp h v = 1 + ((fexp h v / p) / q) * (p * q)) = begin
    assert (fexp h v - fexp h v = (1 + (fexp h v / p) * p) - (1 + (fexp h v / q) * q));
    assert (0 = (fexp h v / p) * p - (fexp h v / q) * q);
    assert (0 % q = ((fexp h v / p) * p - (fexp h v / q) * q) % q);

    small_mod 0 q;

    modulo_distributivity ((fexp h v / p) * p) (- (fexp h v / q) * q) q;

    assert (0 = (((fexp h v / p) * p) % q - ((fexp h v / q) * q) % q) % q);

    multiple_modulo_lemma (fexp h v / q) q;
    assert (0 = (((fexp h v / p) * p) % q) % q);

    modulo_modulo_lemma ((fexp h v / p) * p) q 1;
    assert (((fexp h v / p) * p) % q = 0);

    mod_product_zero (fexp h v / p) p q;
    assert ((fexp h v / p) % q = 0);

    mod_prop q (fexp h v / p) 0;
    assert (fexp h v / p = ((fexp h v / p) / q) * q);

    assert (fexp h v = 1 + ((fexp h v / p) / q) * q * p);
    paren_mul_right ((fexp h v / p) / q) q p
  end in

  l2 ();

  mod_prop_inv (p * q) (fexp h v) 1 ((fexp h v / p) / q);
  small_mod 1 (p * q);
  to_fe_idemp #(p * q) (fexp h v);

  assert (fexp h v = 1)

#reset-options

val solve_dlp: #n:comp -> u:big -> g:fe n{isunit g /\ is_mult_order g u} -> a:fe n -> x:fe u
let solve_dlp #n u g a = admit()

type secret =
  | Secret: p:prm
         -> q:prm{q <> p}
         -> u:big{divides u (p-1) /\ divides u (q-1)}
         -> v:big{divides v (p-1) /\ divides v (q-1)}
         -> g:fe (p*q){isunit g /\ mult_order #(p*q) g = u * v}
         -> h:fe (p*q){is_h p q v h}
         -> secret

type public =
  | Public: n:comp
         -> u:big
         -> g:fe n{isunit g}
         -> h:fe n{isunit h}
         -> public

val s2p: secret -> public
let s2p sec =
  let p = Secret?.p sec in
  let q = Secret?.q sec in
  let u = Secret?.u sec in
  let g = Secret?.g sec in
  let h = Secret?.h sec in
  Public (p * q) u g h

type ciphertext (n:big) = c:fe n

val encrypt:
     p:public
  -> r:pos
  -> m:fe (Public?.u p)
  -> c:ciphertext (Public?.n p)
let encrypt p r m = fexp (Public?.g p) m *% fexp (Public?.h p) r

val check_is_zero:
     s:secret
  -> c:ciphertext (Public?.n (s2p s))
  -> bool
let check_is_zero s c = fexp c (Secret?.v s) = 1

val check_is_zero_prop:
     s:secret
  -> r:pos
  -> m:fe (Public?.u (s2p s))
  -> Lemma
  (check_is_zero s (encrypt (s2p s) r m) = (m = 0))
let check_is_zero_prop s r m =
  let g = Secret?.g s in
  let h = Secret?.h s in
  let v = Secret?.v s in
  let u = Secret?.u s in
  let c = encrypt (s2p s) r m in
  let gv = fexp g v in
  let cv = fexp c v in
  fexp_mul2 (fexp g m) (fexp h r) v;
  fexp_exp h r v;
  fexp_exp h v r;
  h_raise_v (Secret?.p s) (Secret?.q s) v h;
  fexp_exp g m v;
  fexp_exp g v m;
  assert (fexp c v = fexp gv m);

  let g_pow_nonzero (x:nat): Lemma (fexp g x <> 0) = begin
    g_pow_isunit g x;
    isunit_nonzero (fexp g x)
  end in

  g_pow_nonzero v;
  nat_times_nat_is_nat v m;
  g_pow_nonzero (v * m);

  fexp_zero2 gv;
  assert (m = 0 ==> check_is_zero s (encrypt (s2p s) r m) = true);

  let m_neq_zero (): Lemma (requires m <> 0)
                           (ensures check_is_zero s (encrypt (s2p s) r m) = false) = begin
    pos_times_pos_is_pos v m;
    mult_order_and_one g (m * v);
    multiplication_order_lemma_strict m u v;
    assert (m * v < u * v);
    assert (~(divides (u * v) (m * v)))
  end in

  move_requires m_neq_zero ()

val decrypt:
     s:secret
  -> c:ciphertext (Public?.n (s2p s))
  -> m:fe (Secret?.u s)
let decrypt s c =
  let g = Secret?.g s in
  let v = Secret?.v s in
  let u = Secret?.u s in
  let gv = fexp g v in
  g_pow_isunit g v;
  mult_order_of_fexp g v u;
  solve_dlp (Secret?.u s) gv (fexp c (Secret?.v s))
