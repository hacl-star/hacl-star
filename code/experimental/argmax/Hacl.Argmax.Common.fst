module Hacl.Argmax.Common

open FStar.Math.Lemmas
open FStar.Math.Lib
open FStar.Constructive
open FStar.Classical
open FStar.Mul
open FStar.Calc


(* Primes and composite numbers *)

type big = x:int{x > 1}

val isprm: p:big -> bool
let isprm _ = magic()

type prm = n:big{isprm n}

val iscomp: n:big -> Type0
let iscomp n = exists (p:prm) (q:prm). n = p * q

type comp = n:big{iscomp n}

val one: pos
let one = 1

(* Basic algebra *)

val mod_twice: x:int -> n:pos -> Lemma
  ((x % n) % n = x % n)
let mod_twice _ _ = ()

val field_el: #n:big -> a:int -> bool
let field_el #n a = a >= 0 && a < n

type fe n = x:int{field_el #n x}

val to_fe: #n:big -> a:int -> r:fe n
let to_fe #n a = lemma_mod_lt a n; a % n

type binop = #n:big -> fe n -> fe n -> fe n
val ( +% ): binop
let ( +% ) #n n1 n2 = (n1 + n2) % n

val neg: #n:big -> a:fe n -> r:fe n{a +% r = 0}
let neg #n a = if a = 0 then 0 else n - a

val ( -% ): binop
let ( -% ) #n n1 n2 = n1 +% neg n2

val ( *% ): binop
let ( *% ) #n n1 n2 = (n1 * n2) % n

val sqr: #n:big -> fe n -> fe n
let sqr #n a = a *% a

val minus_is_neg: #n:big -> a:nat -> Lemma
  (ensures ((-a%n) % n = neg (to_fe #n a)))
let minus_is_neg #n a = ()

val minus_is_neg2: #n:big -> a:fe n -> Lemma
  (ensures (((-a)%n) = neg a))
let minus_is_neg2 #n a = ()

val add_comm: #n:big -> a:fe n -> b:fe n -> Lemma
  (a +% b = b +% a)
let add_comm #n _ _ = ()

val mul_one: #n:big -> a:fe n -> Lemma
  (ensures (a *% one = a /\ one *% a = a))
  [SMTPat (one *% a); SMTPat (a *% one)]
let mul_one #n a = ()

val mul_neg: #n:big -> a:fe n -> b:fe n -> Lemma
  (a *% (neg b) = neg (a *% b))
let mul_neg #n a b =
  admit ();
  if b = 0 || a = 0 then ()
  else
    calc (==) {
      a *% neg b;                         == { }
      (a * (n - b)) % n;                  == { distributivity_sub_right a n b }
      ((a * n) + (-(a * b))) % n;         == { modulo_distributivity (a * n) (-(a*b)) n }
      ((a * n) % n + (-(a * b)) % n) % n; == { multiple_modulo_lemma a n }
      ((-a * b) % n) % n;                 == { mod_twice (-(a*b)) n }
      (-(a * b)) % n;
    };
    if a*b = 0 then assert ((-(a * b)) % n = 0)
    else if a*b < n then begin
      let c: fe n = a*b in
      minus_is_neg2 c;
      assert ((-c)%n = neg c)
    end else admit()

val mul_comm: #n:big -> a:fe n -> b:fe n -> Lemma
  (ensures (a *% b = b *% a))
  [SMTPat (a *% b)]
let mul_comm #n a b = ()

val mul_add_distr_r: #n:big -> a:fe n -> b:fe n -> c:fe n -> Lemma
  (a *% (b +% c) = a *% b +% a *% c)
let mul_add_distr_r #n _ _ _ = admit()

val mul_add_distr_l: #n:big -> a:fe n -> b:fe n -> c:fe n -> Lemma
  ((a +% b) *% c = a *% c +% b *% c)
let mul_add_distr_l #n a b c = mul_add_distr_r c a b

val mul_sub_distr_r: #n:big -> a:fe n -> b:fe n -> c:fe n -> Lemma
  (a *% (b -% c) = a *% b -% a *% c)
let mul_sub_distr_r #n a b c =
    calc (==) {
      a *% (b -% c);
    == { }
      a *% (b +% (neg c));
    == { mul_add_distr_r a b (neg c) }
      (a *% b) +% (a *% neg c);
    == { mul_neg a c }
      (a *% b) -% (a *% c);
    }

val mul_sub_distr_l: #n:big -> a:fe n -> b:fe n -> c:fe n -> Lemma
  ((a -% b) *% c = a *% c -% b *% c)
let mul_sub_distr_l #n a b c =
  mul_sub_distr_r c a b;
  mul_comm (a -% b) c

val modulo_mul_distributivity: a:int -> b:int -> n:pos ->
    Lemma ((a * b) % n = ((a % n) * (b % n)) % n)
let rec modulo_mul_distributivity a b n =
  lemma_mod_mul_distr_l a b n;
  lemma_mod_mul_distr_r (a % n) b n


val mul3_modulo_out_l: #n:big -> a:fe n -> b:fe n -> c:fe n -> Lemma
  ((a *% b) *% c = ((a * b) * c) % n)
let mul3_modulo_out_l #n a b c =
  calc (==) {
   (a *% b) *% c;
  == { }
   ( (a * b) % n ) *% c;
  == { }
   ( ((a * b) % n) * c ) % n;
  == { modulo_mul_distributivity ((a * b) % n) c n }
   ( (((a * b) % n) % n) * (c % n) ) % n;
  == { mod_twice (a * b) n }
   ( ((a * b) % n) * (c % n)) % n;
  == { modulo_mul_distributivity (a * b) c n }
   ( (a * b) * c ) % n;
  }

val mul3_modulo_out_r: #n:big -> a:fe n -> b:fe n -> c:fe n -> Lemma
  (a *% (b *% c) = (a * (b * c)) % n)
let mul3_modulo_out_r #n a b c =
  calc (==) {
    a *% (b *% c);
   == { mul3_modulo_out_l #n b c a }
    ((b * c) * a) % n;
   == { swap_mul (b * c) a }
    (a * (b * c)) % n;
  }

val mul_assoc: #n:big -> a:fe n -> b:fe n -> c:fe n -> Lemma
  (ensures ((a *% b) *% c = a *% (b *% c)))
  [SMTPat ((a *% b) *% c); SMTPat (a *% (b *% c))]
let mul_assoc #n a b c =
  calc (==) {
    (a *% b) *% c;
  == { mul3_modulo_out_l a b c }
    ((a * b) * c) % n;
  == { assert((a*b)*c = a*(b*c)) }
    (a * (b * c)) % n;
  == { mul3_modulo_out_r a b c }
    (a *% (b *% c));
  }

val mul4_assoc: #n:big -> a:fe n -> b:fe n -> c:fe n -> d:fe n -> Lemma
  ((a *% b) *% (c *% d) = (a *% c) *% (b *% d))
let mul4_assoc #n a b c d =
  calc (==) {
    (a *% b) *% (c *% d);
  == { }
    a *% (b *% (c *% d));
  == { }
    a *% ((b *% c) *% d);
  == { }
    a *% ((c *% b) *% d);
  == { }
    a *% (c *% (b *% d));
  == { }
    (a *% c) *% (b *% d);
  }

// Naive exp
val nexp: #n:big -> fe n -> e:nat -> Tot (fe n) (decreases e)
let rec nexp #n g e = match e with
  | 0 -> 1
  | 1 -> g
  | _ -> g *% nexp g (e-1)

val nexp_eq_arg1: #n:big -> g1:fe n -> g2:fe n -> e:nat -> Lemma
  (requires (g1 = g2))
  (ensures (nexp g1 e = nexp g2 e))
let nexp_eq_arg1 #n _ _ _ = ()

val nexp_one1: #n:big -> g:fe n -> Lemma
  (ensures (nexp g one = g))
  [SMTPat (nexp g one)]
let nexp_one1 #n _ = ()

val nexp_one2: #n:big -> e:nat -> Lemma
  (ensures (nexp #n one e = one))
  [SMTPat (nexp #n one e)]
let rec nexp_one2 #n e = match e with
  | 0 -> ()
  | _ ->  nexp_one2 #n (e-1)

val nexp_mul1: #n:big -> g:fe n -> e1:nat -> e2:nat -> Lemma
  (nexp g e1 *% nexp g e2 = nexp g (e1 + e2))
let rec nexp_mul1 #n g e1 e2 = match e2 with
  | 0 -> assert(nexp g e2 = one)
  | 1 -> assert(nexp g e2 = g)
  | _ -> nexp_mul1 g e1 (e2-1)

val nexp_mul2: #n:big -> g1:fe n -> g2:fe n -> e:nat -> Lemma
  (ensures (nexp (g1 *% g2) e = nexp g1 e *% nexp g2 e))
  (decreases g2)
let rec nexp_mul2 #n g1 g2 e = match g2 with
  | 0 -> (assert (g1 *% 0 = 0); assert (nexp g1 e *% 0 = 0))
  | 1 -> begin
    assert(g2 = one);
    assert (g1 *% g2 = g1);
    nexp_eq_arg1 (g1 *% g2) g1 e;
    assert(nexp (g1 *% g2) e = nexp g1 e)
    end
  | _ -> begin
    nexp_mul2 g1 (g2 -% one) e;
    calc (==) {
      g1 *% (g2 -% one);
    == { mul_sub_distr_r g1 g2 one }
      (g1 *% g2) -% g1;
    };
    admit();
//    calc (==) {
//      nexp g1 e *% nexp (g2 -% one) e;
//    == { }
//
//    };
    admit()
    end

val nexp_exp: #n:big -> g:fe n -> e1:nat -> e2:nat -> Lemma
  ((nexp #n (nexp #n g e1) e2) = (nexp #n g (e1 * e2)))
let nexp_exp #n _ _ _ = admit()


// Define fexp' for composite n and for unit g.
val fexp: #n:big -> fe n -> e:nat -> Tot (fe n) (decreases e)
let rec fexp #n g e =
  if e = 1 then g
  else if e = 0 then 1
  else
     if e % 2 = 0
     then fexp (g *% g) (e / 2)
     else fexp (g *% g) ((e - 1) / 2) *% g

val fexp_eq_nexp: #n:big -> g:fe n -> e:nat -> Lemma
  (ensures (nexp g e = fexp g e)) (decreases e)
let rec fexp_eq_nexp #n g e = match e with
  | 0 -> ()
  | 1 -> ()
  | _ ->
    if e % 2 = 0
    then begin
      fexp_eq_nexp #n (g *% g) (e/2);
      nexp_exp #n g 2 (e/2)
    end
    else begin
      fexp_eq_nexp #n (g *% g) ((e-1)/2);
      nexp_exp g 2 ((e-1)/2)
    end

val fexp_one1: #n:big -> g:fe n -> Lemma
  (ensures (fexp g one = g))
  [SMTPat (fexp g one)]
let fexp_one1 #n _ = ()

val fexp_one2: #n:big -> e:nat -> Lemma
  (ensures (fexp #n one e = one))
  [SMTPat (fexp #n one e)]
let rec fexp_one2 #n e = fexp_eq_nexp #n one e; nexp_one2 #n e

val fexp_mul1: #n:big -> g:fe n -> e1:nat -> e2:nat -> Lemma
  (fexp g e1 *% fexp g e2 = fexp g (e1 + e2))
let fexp_mul1 #n g e1 e2 =
  fexp_eq_nexp g e1;
  fexp_eq_nexp g e2;
  fexp_eq_nexp g (e1+e2);
  nexp_mul1 g e1 e2

val fexp_mul2: #n:big -> g1:fe n -> g2:fe n -> e:nat -> Lemma
  (fexp (g1 *% g2) e = fexp g1 e *% fexp g2 e)
let fexp_mul2 #n g1 g2 e =
  fexp_eq_nexp (g1 *% g2) e;
  fexp_eq_nexp g1 e;
  fexp_eq_nexp g2 e;
  nexp_mul2 g1 g2 e

val fexp_exp: #n:big -> g:fe n -> e1:nat -> e2:nat -> Lemma
  (fexp #n (fexp #n g e1) e2 = fexp #n g (e1 * e2))
let fexp_exp #n g e1 e2 =
  fexp_eq_nexp g e1;
  fexp_eq_nexp (nexp g e1) e2;
  fexp_eq_nexp g (e1 * e2);
  nexp_exp g e1 e2

(* GCD and LCM *)

type divides (a:pos) (b:pos) = exists (c:pos). a * c = b

type is_gcd (a:pos) (b:pos) (gcd:pos) =
    (forall (d:pos). divides d a /\ divides d b ==> divides d gcd)
    /\ divides gcd a
    /\ divides gcd b

val ex_eucl:
     a:pos
  -> b:pos
  -> r:tuple3 pos int int{ let (g,u,v) = r in is_gcd a b g /\ a * u + b * v = g }
let rec ex_eucl a b =
  admit();
  let (g,s,t) = ex_eucl (b % a) a in
  (g, t - (b / a) * s, s)

val gcd: a:pos -> b:pos -> Tot (r:pos{is_gcd a b r}) (decreases b)
let gcd a b = Mktuple3?._1 (ex_eucl a b)

val ex_eucl_lemma1: a:pos -> b:pos -> g:pos -> u:int -> v:int -> Lemma
  (requires (a * u + b * v = g))
  (ensures (exists k. g = k * gcd a b))
let ex_eucl_lemma1 a b g u v = admit()

val ex_eucl_lemma2: a:pos -> b:pos -> g:pos -> u:int -> v:int -> Lemma
  (requires (a * u + b * v = g /\ divides g a /\ divides g b))
  (ensures (gcd a b = g))
let ex_eucl_lemma2 a b g u v = admit()

val ex_eucl_lemma3: a:pos -> b:pos -> u:int -> v:int -> Lemma
  (requires (a * u + b * v = 1))
  (ensures (gcd a b = 1))
let ex_eucl_lemma3 a b u v = ex_eucl_lemma2 a b 1 u v

val lcm: pos -> pos -> pos
let lcm a b = abs ((a / gcd a b) * b)

val mod_prop: n:big -> a:int -> b:int -> Lemma
  (requires (a % n = b))
  (ensures (a - b = (a / n) * n))
let mod_prop n a b =
  lemma_div_mod a n;
  assert(a % n = a - n * (a / n));
  assert(b = a - n * (a / n));
  assert(a - b = (a / n) * n)

val mod_ops_props1: #n:big -> a:fe n -> b:fe n -> c:fe n -> Lemma
  ((a +% b = c ==> (a + b) - c = ((a+b)/n) * n) /\
   (a *% b = c ==> (a * b) - c = ((a*b)/n) * n))
let mod_ops_props1 #n a b c =
  assert (a +% b = c ==> (mod_prop n (a+b) c; (a + b) - c = ((a+b)/n) * n));
  assert (a *% b = c ==> (mod_prop n (a*b) c; (a * b) - c = ((a*b)/n) * n))

val mod_ops_props2: #n:big -> a:fe n -> b:fe n -> c:fe n -> v:fe n -> Lemma
  (((a + b) - c = v * n ==> a +% b = c) /\
   ((a * b) - c = v * n ==> a *% b = c))
let mod_ops_props2 #n a b c v =

  multiple_modulo_lemma v n;
  assert((v * n) % n = 0);

  assert((a * b) - c = v * n ==> ((a * b) - c) % n = (v * n) % n);
  //assert((a * b) - c = v * n ==> ((a * b) - c) % n = 0);
  //assert((a * b) - c = v * n ==> (a * b) % n = c % n);
  //admit();
  //assert((a * b) - c = v * n ==> (a * b) % n = c);

//  admit();
//
//  let l1 (): Lemma ((a + b) - c = v * n ==> (a +% b) = c) =
//    (assert((a + b) - c = v * n ==> ((a + b) - c) % n = 0);
//     assert((a + b) - c = v * n ==> (a + b) % n = c % n);
//     assert((a + b) - c = v * n ==> (a + b) % n = c)) in
//
//  admit();


  admit()

(* Inverses *)

val isunit: #n:big -> a:fe n -> Type0
let isunit #n a = exists b. a *% b = 1

val finv0: #n:big -> a:fe n ->
  Tot (b:option (fe n){isunit a <==> (Some? b /\ Some?.v b *% a = one)})
let finv0 #n a = admit()

val finv: #n:big -> a:fe n{isunit a} -> b:fe n{b *% a = one}
let finv #n a = match finv0 a with | Some x -> x

val finv_unique: #n:big -> a:fe n -> b:fe n{a *% b = one} -> Lemma
  (isunit a /\ b = finv a)
let finv_unique #n a b =
  let z = finv a in
  calc (==) {
    z; =={} z *% one; =={} z *% (a *% b); =={}
            (z *% a) *% b; =={} one *% b; =={} b;
  }

val isunit_prod: #n:big -> a:fe n{isunit a} -> b:fe n{isunit b} -> Lemma
  (ensures (isunit (a *% b) /\ finv (a *% b) = finv a *% finv b))
let isunit_prod #n a b =
  mul4_assoc a b (finv a) (finv b);
  assert((a *% b) *% (finv a *% finv b) = one);
  finv_unique (a *% b) (finv a *% finv b)

val inv_as_gcd1: #n:big -> a:fe n{a>0} -> Lemma
  (requires (gcd a n = 1))
  (ensures (isunit a))
let inv_as_gcd1 #n a =
  let (g,u,v) = ex_eucl a n in
  assert (gcd a n = g);

  assert (g = 1);
  assert (u*a + v*n = 1);
  assert (u*a - 1 = -v*n);
  assert (u*a - 1 = (-v)*n);
  assert (u*a = 1 + (-v)*n);
  assert (((u*a)%n = (1 + (-v)*n)%n));
  modulo_distributivity 1 ((-v)*n) n;
  assert ((u*a)%n = (1%n + ((-v)*n)%n)%n);
  multiple_modulo_lemma (-v) n;
  assert((((-v)*n)%n) = 0);
  assert ((u*a)%n = (1%n + 0)%n);
  assert ((u*a)%n = (1%n)%n);
  mod_twice 1 n;
  assert ((u*a)%n = (1%n));
  assert ((u*a)%n = 1);
  modulo_mul_distributivity u a n;
  assert (((u%n)*(a%n))%n = 1);
  assert (((to_fe #n u)*(a%n))%n = 1);
  modulo_lemma a n;
  assert(a%n = a);
  assert ((to_fe #n u *% a) = 1);
  assert (isunit a)

val inv_as_gcd2: #n:big -> a:fe n{a>0} -> Lemma
  (requires (isunit a))
  (ensures (gcd a n = 1))
let inv_as_gcd2 #n a =
  let u = finv a in

  assert (isunit a);
  assert ((u *% a) = 1);
  assert ((u * a)%n = 1);
  assert ((u * a)%n = 1);
  mod_prop n (u*a) 1;
  assert ((u * a) - 1 = ((u*a)/n)*n);
  assert ((u * a) - ((u*a)/n)*n = 1);
  assert ((u * a) + (-(u*a)/n)*n = 1);
  ex_eucl_lemma3 a n u (-(u*a)/n);
  assert (gcd a n = 1)

val inv_as_gcd: #n:big -> a:fe n{a>0} -> Lemma
  (isunit a <==> gcd a n = 1)
let inv_as_gcd #n a =
  move_requires inv_as_gcd1 a;
  move_requires inv_as_gcd2 a

val mult_order:
     #n:big
  -> g:fe n{isunit g}
  -> r:pos{ fexp g r = one /\
            (forall (x:pos{x<r}). fexp g x <> one) /\
            (g <> 0 ==> r >= 1)
            }
let mult_order #n g = admit()

val g_pow_order_reduc: #n:comp -> g:fe n{isunit g /\ g > 0} -> x:pos -> Lemma
  (ensures (fexp g x = fexp g (x % mult_order g)))
  (decreases x)
let rec g_pow_order_reduc #n g x =
  let r = mult_order g in
  if x < r
  then modulo_lemma x r
  else begin
    lemma_div_mod x r;
    assert(x = r * (x / r) + x % r);
    fexp_mul1 g (r * (x/r)) (x%r);
    fexp_exp g r (x/r);
    assert(fexp g r = one);
    fexp_one2 #n (x/r)
  end

val g_pow_isunit: #n:comp -> g:fe n{isunit g /\ g > 0}  -> x:pos -> Lemma
  (isunit (fexp g x))
let g_pow_isunit #n g x =
  let r = mult_order g in
  let x' = x % r in
  modulo_range_lemma x r;
  let inv_e = r - x' in
  assert(inv_e >= 0 && inv_e <= r);
  assert(fexp g r = one);
  g_pow_order_reduc g x;
  fexp_mul1 g x' inv_e;
  assert(fexp g x' *% fexp g (r - x') = one);
  assert(fexp g x *% fexp g (r - x') = one);
  finv_unique (fexp g x) (fexp g (r - x'))
