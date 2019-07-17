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

type is_h (p:prm) (q:prm) (v:pos) =
  h:fe (p*q){isunit h /\ (isunit_comp p q h; mult_order (to_fe #p h) = v /\ mult_order (to_fe #q h) = v)}

val solve_dlp: #n:comp -> u:big -> g:fe n{isunit g /\ is_mult_order g u} -> a:fe n -> x:fe u
let solve_dlp #n u g a = admit ()

type secret =
  | Secret: p:prm
         -> q:prm{q <> p}
         -> u:big{divides u (p-1) /\ divides u (q-1)}
         -> v:big{divides v (p-1) /\ divides v (q-1)}
         -> g:fe (p*q){isunit g /\ mult_order #(p*q) g = u * v}
         -> h:is_h p q v
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
