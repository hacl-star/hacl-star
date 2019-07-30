module Hacl.Spec.HE.DGK

open FStar.Mul
open FStar.Math.Lemmas
open FStar.Classical

open Lib.Math.Algebra

module S = FStar.Seq


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

// h^v = 1 mod q, p
// h^v = 1 + k*q
// h^v = 1 + m*p
// k * q - m * p = 0
// k * q = 0 mod p
// q /= 0 mod p, so k = 0 mod p,
// so k = s * p,
// so h^v = 1 + s*p*q
val h_raise_v: p:prm -> q:prm{p <> q} -> v:pos -> h:fe (p*q){is_h p q v h} -> Lemma (mexp h v = 1)
let h_raise_v p q v h =
  swap_mul p q;

  let l1 (): Lemma (mexp h v = 1 + (mexp h v / p) * p /\
                    mexp h v = 1 + (mexp h v / q) * q) = begin
    isunit_comp p q h;

    multiple_modulo_lemma p q;
    multiple_division_lemma p q;
    to_fe_mexp1 #(p*q) q h v;
    mod_prop p (mexp h v) 1;

    multiple_modulo_lemma q p;
    multiple_division_lemma q p;
    to_fe_mexp1 #(p*q) p h v;
    mod_prop q (mexp h v) 1
    end in

  l1 ();

  let l2 (): Lemma (mexp h v = 1 + ((mexp h v / p) / q) * (p * q)) = begin
    assert (mexp h v - mexp h v = (1 + (mexp h v / p) * p) - (1 + (mexp h v / q) * q));
    assert (0 = (mexp h v / p) * p - (mexp h v / q) * q);
    assert (0 % q = ((mexp h v / p) * p - (mexp h v / q) * q) % q);

    small_mod 0 q;

    modulo_distributivity ((mexp h v / p) * p) (- (mexp h v / q) * q) q;

    assert (0 = (((mexp h v / p) * p) % q - ((mexp h v / q) * q) % q) % q);

    multiple_modulo_lemma (mexp h v / q) q;
    assert (0 = (((mexp h v / p) * p) % q) % q);

    modulo_modulo_lemma ((mexp h v / p) * p) q 1;
    assert (((mexp h v / p) * p) % q = 0);

    mod_product_zero (mexp h v / p) p q;
    assert ((mexp h v / p) % q = 0);

    mod_prop q (mexp h v / p) 0;
    assert (mexp h v / p = ((mexp h v / p) / q) * q);

    assert (mexp h v = 1 + ((mexp h v / p) / q) * q * p);
    paren_mul_right ((mexp h v / p) / q) q p
  end in

  l2 ();

  mod_prop_inv (p * q) (mexp h v) 1 ((mexp h v / p) / q);
  small_mod 1 (p * q);
  to_fe_idemp #(p * q) (mexp h v);

  assert (mexp h v = 1)

#reset-options

(*** Decryption ***)

val solve_dlp_power:
     #n:comp
  -> p:big
  -> s:big{exp p s < n}
  -> g:fe n{isunit g /\ is_mult_order g (exp p s)}
  -> a:fe n
  -> x:fe (exp p s)
let solve_dlp_power #n u g a = admit()


type crtbase0 = s:S.seq (tuple2 nat nat){S.length s > 0}

type is_crt_base0 (base:crtbase0) =
  forall (i:nat{i < S.length base}).
  isprm (fst (S.index base i)) /\ snd (S.index base i) > 0

type is_crt_base (base:crtbase0) =
  is_crt_base0 base /\
  (forall (i:nat{i < S.length base}) (j:nat{j < S.length base /\ j <> i}).
    fst (S.index base i) <> fst (S.index base j))

type crtbase = base:crtbase0{ is_crt_base base }

type crtvalues0 = S.seq nat

type is_crt_values0 (values:crtvalues0) =
  forall (i:nat{i < S.length values}). S.index values i > 0

type is_crt_values
  (base:crtbase)
  (values:crtvalues0{S.length values = S.length base}) =
  is_crt_values0 values /\
  (forall (i:nat{i < S.length values}).
   let (p,e) = S.index base i in S.index values i < exp p e)

type crtvalues base =
  values:crtvalues0{S.length values = S.length base /\
                    is_crt_values base values}

type is_crt_sol
  (base:crtbase)
  (values:crtvalues base)
  (sol:pos)
  =
  forall (i:nat{i<S.length base}).
  let (p,e) = S.index base i in
  sol % exp p e = S.index values i

val tailprod_go:
     s:crtbase
  -> i:pos{i <= S.length s}
  -> j:nat{j <= i}
  -> m:big
  -> Tot big (decreases (i-j))
let rec tailprod_go s i j m =
    if j = i then m else
    let (p,e) = S.index s j in tailprod_go s i (j+1) (m * exp p e)

val tailprod: s:crtbase -> i:pos{i <= S.length s} -> big
let tailprod s i =
  let (p,e) = S.index s 0 in
  tailprod_go s i 1 (exp p e)

val fullprod: s:crtbase -> big
let fullprod s = tailprod s (S.length s)

val tailprod_first: s:crtbase -> Lemma
  (let (p,e) = S.index s 0 in tailprod s 1 = exp p e)
let tailprod_first s = ()

val fermat_inv_pe:
     p:prm
  -> e:pos
  -> a:fe (exp p e)
  -> b:fe (exp p e)
let fermat_inv_pe p e a =
  let lam = carm_pe p e in
  mexp a (lam - 1)

#reset-options "--z3rlimit 100"

val fermat_inv_pe_lemma:
     p:prm
  -> e:pos
  -> a:fe (exp p e)
  -> Lemma
     (let b = fermat_inv_pe p e a in
      (isunit a ==> (isunit b /\ a *% b = 1 /\ b = finv a)))
     [SMTPat (fermat_inv_pe p e a)]
let fermat_inv_pe_lemma p e a =
  let lam = carm_pe p e in
  let b = mexp a (lam - 1) in
  mexp_mul1 a (lam - 1) 1;
  mexp_one1 a;
  euler_thm (exp p e) (pe_fact p e) lam a;
  finv_unique #(exp p e) a b

val crtgo_combine:
     p:prm
  -> e:pos
  -> m:big {m = exp p e}
  -> mprod:big
  -> a:nat
  -> acc:pos
  -> acc':pos
let crtgo_combine p e m mprod a acc =
  let m' = fermat_inv_pe p e (mprod % m) in
  let y = (m' * ((a - acc) % m)) % m in
  let next_acc = acc + mprod * y in
  next_acc

val crtgo:
     l:pos
  -> base:crtbase{S.length base = l}
  -> values:crtvalues base
  -> lcur:pos{lcur < l}
  -> mprod:big
  -> acc:pos
  -> Tot (res:pos)
         (decreases (l - lcur))
let rec crtgo l base values lcur mprod acc =

  let (p,e) = S.index base lcur in
  let m = exp p e in
  let a = S.index values lcur in

  let next_acc = crtgo_combine p e m mprod a acc in

  if lcur = l - 1 then next_acc else
    crtgo l base values (lcur+1) (mprod * m) next_acc

val crt:
     l:nat{l>1}
  -> base:crtbase{S.length base = l}
  -> values:crtvalues base
  -> res:pos
let crt l base values =
  let (p0,e0) = S.index base 0 in
  let a0 = S.index values 0 in
  tailprod_first base;
  crtgo l base values 1 (exp p0 e0) a0

val crt_proof:
     l:pos{l>1}
  -> base:crtbase{S.length base = l}
  -> values:crtvalues base
  -> Lemma
  (is_crt_sol base values (crt l base values))
  [SMTPat (crt l base values)]
let crt_proof _ _ _ = admit()

// O(S_{q^e}) -> O(eS_q) reduction.
// Or just shank.
val solve_dlp_pe:
     #n:comp
  -> p:prm
  -> e:pos
  -> g:fe n{isunit g /\ is_mult_order g (exp p e)}
  -> a:fe n
  -> x:fe (exp p e)
let solve_dlp_pe #n u g a = admit()

// Pohlig-Hellman
val solve_dlp:
     #n:comp
  -> base:crtbase
  -> g:fe n{isunit g /\ is_mult_order g (fullprod base)}
  -> a:fe n
  -> x:fe (fullprod base)
let solve_dlp #n base g a = admit()

val solve_dlp_proof:
     #n:comp
  -> base:crtbase
  -> g:fe n{isunit g /\ is_mult_order g (fullprod base)}
  -> a:fe n
  -> Lemma
  (mexp g (solve_dlp base g a) = a)
let solve_dlp_proof #n base g a = admit ()

(*** Keys, functions, proofs ***)

type secret =
  | Secret: p:prm
         -> q:prm{q <> p}
         -> u:fe (p*q){u > 1 /\ divides u (p-1) /\ divides u (q-1)}
         -> v:fe (p*q){v > 1 /\ divides v (p-1) /\ divides v (q-1)}
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
let encrypt p r m = mexp (Public?.g p) m *% mexp (Public?.h p) r

val check_is_zero:
     s:secret
  -> c:ciphertext (Public?.n (s2p s))
  -> bool
let check_is_zero s c = mexp c (Secret?.v s) = 1

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
  let gv = mexp g v in
  let cv = mexp c v in
  mexp_mul2 (mexp g m) (mexp h r) v;
  mexp_exp h r v;
  mexp_exp h v r;
  h_raise_v (Secret?.p s) (Secret?.q s) v h;
  mexp_exp g m v;
  mexp_exp g v m;
  assert (mexp c v = mexp gv m);

  let g_pow_nonzero (x:nat): Lemma (mexp g x <> 0) = begin
    g_pow_isunit g x;
    isunit_nonzero (mexp g x)
  end in

  g_pow_nonzero v;
  nat_times_nat_is_nat v m;
  g_pow_nonzero (v * m);

  mexp_zero2 gv;
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

#reset-options

val decrypt:
     s:secret
  -> c:ciphertext (Public?.n (s2p s))
  -> m:fe (Secret?.u s)
let decrypt s c =
  let g = Secret?.g s in
  let v = Secret?.v s in
  let u = Secret?.u s in
  let gv = mexp g v in
  g_pow_isunit g v;
  mult_order_of_mexp g v u;
  admit ()
//  solve_dlp (Secret?.u s) gv (mexp c (Secret?.v s))
